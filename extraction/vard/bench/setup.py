import time
import argparse
import random
import threading
import etcd
import vard

t = threading

def cluster(addrs):
    ret = []
    for addr in addrs.split(','):
        (host, _, port) = addr.partition(':')
        ret.append((host, int(port)))
    return ret

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--service', default='vard', choices=['etcd', 'vard'])
    parser.add_argument('--cluster', type=cluster)
    parser.add_argument('--keys', default=100, type=int)
    args = parser.parse_args()
    Client = vard.Client
    if args.service == 'etcd':
        Client = etcd.Client

    host, port = Client.find_leader(args.cluster)
        
    c = Client(host, port)
    for i in range(args.keys):
        c.put('key' + str(i), 'value' + str(i))
        
if __name__ == '__main__':
    main()
