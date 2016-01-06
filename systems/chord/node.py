from collections import defaultdict
import time

from data import Pointer, Message, MessageIncomplete
from net import IOThread

SUCC_LIST_LEN = 3

def between(a, x, b):
    if a < b:
        return a < x < b
    else:
        return a < x or x < b


class Node(object):
    def __init__(self, ip, pred=None, succ_list=None):
        self.ip = ip
        self.ptr = Pointer(ip)
        self.id = self.ptr.id

        self.pred = pred
        if succ_list is None:
            if pred is not None:
                raise ValueError("provided pred but not succ_list")
            self.joined = False
            self.succ_list = succ_list
        elif len(succ_list) == SUCC_LIST_LEN:
            if pred is None:
                raise ValueError("provided succ_list but not pred")
            self.joined = True
            self.succ_list = succ_list
        else:
            raise ValueError("succ_list isn't the right length")

        self.io = IOThread(self.ip)
        self.started = False

        # map from ids to the clients that have asked for the id's successor
        self.lookup_clients = defaultdict(list)

    # can only be run once we've joined and stabilized
    def main_loop(self):
        while True:
            src, msg = self.io.recv()
            outs = self.handle(src, msg)
            for dst, msg in outs:
                self.io.send(dst, msg)

    def find_succ(self, id):
        full_succ_list = [self.ptr] + self.succ_list
        for i, cur in enumerate(full_succ_list[:-1]):
            next = full_succ_list[i + 1]
            if between(cur.id, id, next.id) or cur.id == id or id + 1 == next.id:
                return next
        return None

    def handle(self, src, msg):
        kind = msg.kind
        if kind == "lookup_succ":
            id = msg.data[0]
            succ = self.find_succ(id)
            if succ is not None:
                return [(src, Message("found_succ_for", [id, succ]))]
            # otherwise we have to forward it
            self.lookup_clients[id].append(src)
            return [(self.succ_list[-1], Message("lookup_succ", [id]))]
        elif kind == "found_succ_for":
            id, succ = msg.data
            # forward the message to whoever asked
            packet = (self.lookup_clients[id][0], msg)
            # and take them off the waiting list
            del self.lookup_clients[id][0]
            return [packet]
        else:
            print "ignoring a strange message: {}".format(msg)
            return []

    def start(self, known=None):
        self.setup(known)
        self.main_loop()

    def setup(self, known=None):
        if self.started:
            raise RuntimeError("already started")
        self.started = True
        self.io.start()
        if self.succ_list is None:
            if known is None:
                raise ValueError("can't join without a known node!")
            self.join(known)
            self.stabilize()

    def lookup_succ(self, ptr=None, id=None):
        if id is None:
            id = self.id
        if ptr is None:
            ptr = self.find_succ(id)
            if ptr is not None:
                return ptr
        self.io.send(self.succ_list[-1], Message("lookup_succ", [id]))
        #XXX src should be known
        while True:
            src, msg = self.io.recv()
            if msg.kind == "found_succ_for" and msg.data[0] == id:
                return msg.data[1]

#    def join(self, known):
#        succeeded = False
#        while not succeeded:
#            new_succ = self.lookup_succ(known)
#            if new_succ is not None:
#                self.io.send(new_succ, Message("get_succ_list", []))
#                if succs is not None:
#                    self.succ_list = [new_succ] + succs[:-1]
#                    self.pred = None
#                    succeeded = True
#                else:
#                    time.sleep(5)
#            else:
#                time.sleep(5)


if __name__ == "__main__":
    ptrs = [Pointer(ip="127.0.0.1{}".format(i)) for i in range(0, 10)]
    nodes = []
    for i in range(0, 10):
        localhost = "127.0.0.1{}".format(i)
        succs = ptrs[i+1:i+1+SUCC_LIST_LEN]
        if len(succs) < SUCC_LIST_LEN:
            succs += ptrs[:SUCC_LIST_LEN-len(succs)]
        node = Node(ip=localhost, pred=ptrs[i - 1], succ_list=succs)
        nodes.append(node)

    import multiprocessing
    for node in nodes[1:]:
        p = multiprocessing.Process(target=node.start)
        p.daemon = True
        p.start()

    me = nodes[0]
    me.setup()
    print "POINTERS:"
    for ptr in ptrs:
        print " {}\t{}".format(ptr.id, ptr.ip)
    time.sleep(1)
    # should be a pointer to 127.0.0.15 (id = 47)
    for i in range(40, 52):
        print "the successor of {} is {}".format(i, me.lookup_succ(id=i).id)
