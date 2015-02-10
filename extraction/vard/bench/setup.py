import time
import argparse
import random
import threading
import etcd
import vard

t = threading

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--service', default='vard', choices=['etcd', 'vard'])
    parser.add_argument('--host', default='localhost')
    parser.add_argument('--port', default=8001, type=int)
    parser.add_argument('--keys', default=100, type=int)
    args = parser.parse_args()

    Client = vard.Client
    if args.service == 'etcd':
        print 'using etcd'
        Client = etcd.Client
    c = Client(args.host, args.port)
    for i in range(args.keys):
        c.put('key' + str(i), 'value' + str(i))
        
if __name__ == '__main__':
    main()
