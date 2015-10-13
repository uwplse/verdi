import time
import argparse
import random
import threading
import etcd
import vard

t = threading

gets = []
puts = []
reqs = []
DEBUG = False

def benchmark(client, requests, keys, put_percentage, n):
    random.seed(n)
    put_prob = put_percentage / 100.0
    i = 0
    while True:
        i += 1
        key = str(random.randint(0, keys))
        if random.random() < put_prob:
            start = time.time()
            client.put('key' + key, str(i))
            end = time.time()
            puts.append(end-start)
            reqs.append((end, end-start))
        else:
            start = time.time()
            client.get('key' + key)
            end = time.time()
            gets.append(end-start)
            reqs.append((n, end, end-start))
        if DEBUG:
            print 'Thread %d Done with %d requests' % (n, i)
        if len(reqs) >= requests:
            return

def cluster(addrs):
    ret = []
    for addr in addrs.split(','):
        (host, _, port) = addr.partition(':')
        ret.append((host, int(port)))
    return ret

def main():
    global DEBUG
    parser = argparse.ArgumentParser()
    parser.add_argument('--service', default='vard', choices=['etcd', 'vard'])
    parser.add_argument('--cluster', type=cluster)
    parser.add_argument('--requests', default=1000, type=int)
    parser.add_argument('--threads', default=50, type=int)
    parser.add_argument('--keys', default=100, type=int)
    parser.add_argument('--put-percentage', default=50, type=int)
    parser.add_argument('--debug', default=False, action='store_true')
    args = parser.parse_args()

    if args.debug:
        DEBUG = True
    Client = vard.Client
    if args.service == 'etcd':
        Client = etcd.Client

    host, port = Client.find_leader(args.cluster)
    threads = []
    start = time.time()
    for i in range(args.threads):
        print 'Starting thread %s' % i
        c = Client(host, port)
        thr = t.Thread(target=benchmark, args=(c, args.requests, args.keys, args.put_percentage, i))
        threads.append(thr)
        thr.start()
        time.sleep(10)
    for thr in threads:
        thr.join()
    end = time.time()
    print 'Requests:'
    for (t, ts, latency) in reqs:
        print 'REQUEST: THREAD %s TIME %s LATENCY %s' % (t, ts, latency)
    print 'Total time: %f' % (end - start)
    print '%f gets, avg = %f' % (len(gets), sum(gets)/len(gets))
    print '%f puts, avg = %f' % (len(puts), sum(puts)/len(puts))
    print 'Requests:'
        
if __name__ == '__main__':
    main()
