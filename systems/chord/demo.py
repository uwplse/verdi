import logging
import multiprocessing
import sys
import time

from data import Pointer, SUCC_LIST_LEN
from node import Node

def launch_node(ip, pred, succ_list):
    node = Node(ip=ip, pred=pred, succ_list=succ_list)
    p = multiprocessing.Process(target=node.start)
    p.daemon = True
    p.start()

    return node, p

def launch_ring_of(n):
    ptrs = sorted([Pointer(ip="127.0.0.{}".format(i)) for i in range(1, n+1)])
    nodes = []
    procs = []
    for i, p in enumerate(ptrs):
        succs = ptrs[i+1:i+1+SUCC_LIST_LEN]
        if len(succs) < SUCC_LIST_LEN:
            succs += ptrs[:SUCC_LIST_LEN-len(succs)]
        node, proc = launch_node(p.ip, ptrs[i - 1], succs)
        nodes.append(node)
        procs.append(proc)
    return nodes, procs

def kill_demo():
    logging.debug("running kill_demo()")
    nodes, procs = launch_ring_of(40)
    time.sleep(2)
    for kill_idx in [3,5]:
        logging.warn("killing node {}".format(nodes[kill_idx].state.ptr.id))
        procs[kill_idx].terminate()

    known = nodes[0].state.ptr
    new_node = Node("127.0.0.100")
    time.sleep(0.5)
    print "adding new node:", new_node.state.ptr
    new_node.start(known)

    procs[0].join()

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
    kill_demo()
