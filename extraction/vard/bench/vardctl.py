import argparse
import os
import sys

import vard

def cluster_type(addrs):
    ret = []
    for addr in addrs.split(','):
        (host, _, port) = addr.partition(':')
        ret.append((host, int(port)))
    return ret

def create_client(args):
    leader_host, leader_port = vard.Client.find_leader(args.cluster)
    return vard.Client(leader_host, leader_port)

def status(args):
    # TODO: add more information
    for (host, port) in args.cluster:
        c = vard.Client(host, port)
        print "%s:%d" % (host, port),
        try:
            c.get('a')
        except vard.LeaderChanged:
            print "is not leader"
        else:
            print "is leader"

def get(args):
    client = create_client(args)
    value = client.get(args.key)
    if value is not None:
        print value

def put(args):
    client = create_client(args)
    res = client.put(args.key, args.value)
    print res

def main():
    parser = argparse.ArgumentParser()

    # global options
    cluster_default = os.environ.get('VARD_CLUSTER')
    parser.add_argument('--cluster', type=cluster_type, required=(cluster_default is None), default=cluster_default)

    # subcommands
    subparsers = parser.add_subparsers(dest='cmd', help='commands')

    status_parser = subparsers.add_parser('status', help='Check status of nodes in cluster')

    get_parser = subparsers.add_parser('get', help='Issue GET request')
    get_parser.add_argument('key', action='store', help='Key to GET')

    put_parser = subparsers.add_parser('put', help='Issue PUT request')
    put_parser.add_argument('key', action='store', help='Key to PUT')
    put_parser.add_argument('value', action='store', help='Value to PUT')

    args = parser.parse_args()
    globals()[args.cmd](args)

if __name__ == '__main__':
    main()
