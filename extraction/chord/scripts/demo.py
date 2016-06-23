import os
import Queue
import random
import subprocess
import sys
import threading
import time

CHORD = os.path.join(os.path.dirname(__file__), "../chord.native")

SUCC_LIST_LEN = 2
N = 256

class Addr(object):
    def __init__(self, ip, port):
        self.ip = ip
        self.port = int(port)

    def __repr__(self):
        return "{}:{}".format(self.ip, self.port)

    def chordhash(self):
        return self.port % N

def read_to_queue(f, queue):
    while True:
        line = f.readline()
        if line != "":
            # trim newline
            queue.put(line[:-1])

class Node(object):
    def __init__(self, addr, knowns):
        self.addr = addr
        self.knowns = knowns
        self.started = False
        self.p = None
        self.buffer = ""

    def spawn(self):
        args = [str(a) for a in [self.addr] + self.knowns]
        p = subprocess.Popen(
                [CHORD] + args,
                stdin=open(os.devnull, "r"),
                stdout=subprocess.PIPE)
        q = Queue.Queue()
        self.t = threading.Thread(target=read_to_queue, args=(p.stdout, q))
        self.t.daemon = True
        self.t.start()
        self.output_queue = q
        self.started = True

    def readlines(self):
        lines = []
        while len(lines) < 100:
            try:
                lines.append(self.output_queue.get_nowait())
            except Queue.Empty:
                break
        return lines

    def kill(self):
        self.p.terminate()
        self.p.wait()

    def __repr__(self):
        template = "Node(addr={}, knowns={}, started={})"
        return template.format(self.addr, self.knowns, self.started)

def ideal_ring(start, n):
    nodes = []
    addrs = sorted([Addr("127.0.0.1", start + i) for i in range(n)],
                   key=lambda a: a.chordhash())
    for i, a in enumerate(addrs):
        pred = addrs[i - 1]
        if n - i <= SUCC_LIST_LEN:
            extra = SUCC_LIST_LEN - (n - i - 1)
            succs = addrs[i+1:] + addrs[0:extra]
        else:
            succs = addrs[i+1:i+SUCC_LIST_LEN+1]
        nodes.append(Node(a, [pred] + succs))
    return nodes

def random_action(nodes):
    r = random.random()
    if r < 0.4:
        known = random.choice(nodes)
        port = max([n.addr.port for n in nodes]) + 1
        addr = Addr("127.0.0.1", port)
        joiner = Node(addr, [known.addr])
        print "adding node {} at {}".format(addr.chordhash(), addr)
        joiner.spawn()
        nodes.append(joiner)
    else:
        pass # do nothing

def main():
    nodes = ideal_ring(8000, 10)
    print nodes
    for node in nodes:
        node.spawn()
    tick = time.time() + 25.0
    while True:
        lines = []
        for node in nodes:
            for l in node.readlines():
                if " - " not in l:
                    continue
                timestamp, line = l.split(" - ", 1)
                lines.append((float(timestamp), line))
        lines.sort(key=lambda (ts, _): ts)
        for (ts, line) in lines:
            print line
        if time.time() > tick:
            random_action(nodes)
            tick = time.time() + 20.0

if __name__ == "__main__":
    main()
