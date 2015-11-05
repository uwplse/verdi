"""
Provisions EC2 instances and runs an experiment based on a
YAML-formatted experiment configuration.

Requirements:
- Amazon cli tools installed and working. Test with "aws ec2 describe-instances"
- SSH set up to use the provided key by default. Easiest way to do this is described below.
- "ubuntu" user with passwordless sudo on EC2 image (works in default ubuntu AMI)

SSH config:
- Make a key called "bench" in EC2 account
- Download the private key and put it in ~/.ssh
- Add the following to ~/.ssh/config:
    Host *.compute.amazonaws.com
    IdentityFile ~/.ssh/bench.pem

Basic usage:
    python experiment.py <experiment.yml> <name-of-experiment>
This creates a directory called <name-of-experiment> with complete logs of every 
process, by logical machine name.

To debug problems, do
    python experiment.py <experiment.yml> <name-of-experiment> --no-expt

This will run the provisioning and setup scripts, then spin until killed with C-c. 
The script prints out the addresses of provisioned nodes, so you can SSH to them and debug problems.

Some example YAML files are in the experiments/ subdirectory.

"""

import time
import yaml
import json
import subprocess
import os
import sys
import shutil
import string
import pipes
from datetime import datetime

USER = 'ubuntu'

INSTANCE_DEFAULTS = {
    'type': 't2.micro',
    'key' : 'bench',
    'image': 'ami-5189a661' # Canonical-provided Ubuntu AMI
}

def build_provision_command(type, image, key):
    return ['aws', 'ec2', 'run-instances',
            '--instance-type', type,
            '--image-id', image,
            '--key-name', key,
    ]

def start(type, image, key):
    cmd = build_provision_command(type, image, key)
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE)
    (out, err) = proc.communicate()
    return json.loads(out)['Instances'][0]['InstanceId']

def terminate(instance_id):
    proc = subprocess.Popen(['aws', 'ec2', 'terminate-instances', '--instance-ids', instance_id], stdout=subprocess.PIPE)
    proc.communicate()

def get_names(instance_id):
    proc = subprocess.Popen(['aws', 'ec2', 'wait', 'instance-running', '--instance-id', instance_id], stdout=subprocess.PIPE)
    proc.communicate()
    proc = subprocess.Popen(['aws', 'ec2', 'describe-instances', '--instance-ids', instance_id], stdout=subprocess.PIPE)
    (out, err) = proc.communicate()
    instance_desc = json.loads(out)['Reservations'][0]['Instances'][0]
    return instance_desc['PrivateIpAddress'], instance_desc['PublicDnsName']

class Timeout(Exception):
    pass

def run_command(host, command, logfile):
    for i in range(10):
        proc = subprocess.Popen(['ssh', '-o', 'UserKnownHostsFile=/dev/null',
                                        '-o', 'StrictHostKeyChecking=no',
                                        '-o', 'ConnectTimeout=2',
                                 '%s@%s' % (USER, host), 'bash -c %s' % pipes.quote(command)],
                                stdout=logfile, stderr=logfile)
        time.sleep(4)
        res = proc.poll()
        if res == 255:
            print 'SSH connection to %s refused; retrying' % host
            continue
        return proc
    else:
        print "Too many retries, exiting"
        raise Timeout()

def main(run_expt):
    print 'Starting experiment'
    experiment_label = sys.argv[2] + datetime.now().strftime('-%Y-%m-%d-%H%M%S')
    os.mkdir(experiment_label)
    shutil.copy(sys.argv[1], experiment_label)
    f = open(sys.argv[1])
    config = yaml.safe_load(f)
    f.close()
    instances = config['instances']

    experiment = {'label': experiment_label, 'vars': config.get('vars', {}), 'instances': {}}
    for instance_name in instances:
        instance = experiment['instances'][instance_name] = {}
        instance.update(INSTANCE_DEFAULTS)
        instance.update(instances[instance_name] or {})
        print 'Starting %s as %s' % (instance_name, instance['type'])
        instance['instance_id'] = start(instance['type'], instance['image'],
                                            instance['key'])

    for instance_name in experiment['instances']:
        private, public = get_names(experiment['instances'][instance_name]['instance_id'])
        experiment['instances'][instance_name]['private'] = private
        experiment['instances'][instance_name]['public'] = public
        experiment['vars'][instance_name] = private
        print 'Instance %s at %s (private %s)' % (instance_name, public, private)
    print 'All instances started'
    try:
        # provision instances
        if 'provision' in config:
            procs = []
            for instance_name in experiment['instances']:
                logfile = open(os.path.join(experiment_label, 'provision-%s.log' % instance_name), 'w')
                command = string.Template(config['provision']).substitute(experiment['vars'])
                procs.append(run_command(experiment['instances'][instance_name]['public'], command, logfile))
            for proc in procs:
                proc.wait()
        print "Provisioning complete"
        for instance_name in config.get('setup', {}):
            logfile = open(os.path.join(experiment_label, 'setup-%s.log' % instance_name), 'w')
            command = string.Template(config['setup'][instance_name]).substitute(experiment['vars'])
            run_command(experiment['instances'][instance_name]['public'], command, logfile)
        print 'Setup complete'
        if run_expt:
            time.sleep(10)
            procs = []
            for instance_name in config.get('experiment', {}):
                logfile = open(os.path.join(experiment_label, 'experiment-%s.log' % instance_name), 'w')
                command = string.Template(config['experiment'][instance_name]).substitute(experiment['vars'])
                procs.append(run_command(experiment['instances'][instance_name]['public'], command, logfile))
            for proc in procs:
                proc.wait()
        else:
            while True:
                pass
    finally:
        for instance_name in experiment['instances']:
            terminate(experiment['instances'][instance_name]['instance_id'])
            pass
if __name__ == '__main__':
    run_expt = True
    if '--no-expt' in sys.argv:
        run_expt = False
    main(run_expt)
