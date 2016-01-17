from collections import defaultdict
import logging
import time

from data import Pointer, Message, MessageIncomplete, SUCC_LIST_LEN
from net import IOThread, DeadNode

# these should be higher in real life, probably
DEFAULT_STABILIZE_INTERVAL = 3
QUERY_TIMEOUT = 5

def between(a, x, b):
    if a < b:
        return a < x < b
    else:
        return a < x or x < b


class QueryFailed(RuntimeError):
    pass

class Node(object):
    def __init__(self, ip, pred=None, succ_list=None,
            stabilize_interval=DEFAULT_STABILIZE_INTERVAL):
        self.ip = ip
        self.ptr = Pointer(ip)
        self.id = self.ptr.id
        self.stabilize_interval = stabilize_interval

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

        self.logger = logging.getLogger(__name__ + "({},{})".format(self.ip, self.id))

        # map from ids to the clients that have asked for the id's successor
        self.lookup_clients = defaultdict(list)

    # can only be run once we've joined and stabilized
    def main_loop(self):
        while True:
            if time.time() - self.last_stabilize > self.stabilize_interval:
                self.stabilize()

            res = self.io.recv()
            if res is not None:
                src, msg = res
                self.do_handle(src, msg)

    def handle_all(self, packets):
        for src, msg in packets:
            self.do_handle(src, msg)

    def do_handle(self, src, msg):
        outs = self.handle(src, msg)
        for dst, msg in outs:
            try:
                self.io.send(dst, msg)
            except DeadNode, e:
                mark_node_dead(e.ptr)

    def find_successor(self, id, known=None):
        """look up the proper successor of the given id in the ring"""
        pred = self.find_predecessor(id, known)
        succ = self.get_succ(pred)
        if succ.id == id:
            return self.get_succ(succ)
        else:
            return succ

    def find_predecessor(self, id, known=None):
        """look up the proper predecessor of the given id in the ring"""
        if known is None:
            cur = self.ptr
            succ_of_cur = self.succ_list[0]
        else:
            cur = known
            succ_of_cur = self.get_succ(known)
        arg = cur
        while not between(cur.id, id, succ_of_cur.id + 1):
            cur = self.get_best_predecessor(cur, id)
            succ_of_cur = self.get_succ(cur)
        self.logger.debug("find_predecessor({}, {}) = {}".format(id, arg, cur))
        return cur

    def get_best_predecessor(self, ptr, id):
        if ptr == self.ptr:
            return self.best_predecessor(id)
        msg = Message("get_best_predecessor", [id])
        best_pred = self.query(ptr, msg, "got_best_predecessor")[1]
        self.logger.debug("get_best_predecessor({}, {}) = {}".format(ptr, id,
            best_pred))
        return best_pred

    def get_succ(self, ptr):
        return self.get_succ_list(ptr)[0]

    # this is like closest_preceding_finger in the chord paper
    # but I have no finger tables (yet)
    def best_predecessor(self, id):
        for node in reversed(self.succ_list):
            if between(self.id, node.id, id):
                return node
        return self.ptr

    def handle(self, src, msg):
        kind = msg.kind
        if kind == "get_best_predecessor":
            id = msg.data[0]
            pred = self.best_predecessor(id)
            return [(src, Message("got_best_predecessor", [id, pred]))]
        elif kind == "get_succ_list":
            return [(src, Message("got_succ_list", self.succ_list))]
        elif kind == "get_pred_and_succs":
            msg = Message("got_pred_and_succs", [self.pred] + self.succ_list)
            return [(src, msg)]
        elif kind == "notify":
            self.rectify(src)
            # rectify(..) does io on its own, so we just return []
            return []
        elif kind == "ping":
            return [(src, Message("pong"))]
        else:
            self.logger.warning("ignoring a strange message: {}".format(msg))
            return []

    def rectify(self, new_pred):
        self.logger.debug("rectifying with new_pred = {}".format(new_pred))
        old_pred = self.pred
        if self.pred is None:
            self.pred = new_pred
        else:
            try:
                res = self.query(self.pred, Message("ping"), "pong")
                if between(self.pred.id, new_pred.id, self.id):
                    self.pred = new_pred
            except QueryFailed:
                self.pred = new_pred
        if self.pred != old_pred:
            self.logger.info("rectify: changed pred to {}".format(self.pred))
        self.logger.debug("rectified")

    def notify(self, node):
        self.logger.debug("notifying {}".format(node))
        try:
            self.io.send(node, Message("notify"))
        except DeadNode, e:
            self.mark_node_dead(e.ptr)
            self.stabilize()

    def mark_node_dead(self, ptr):
        self.logger.info("marking a node dead: {}".format(ptr))
        self.succ_list.remove(ptr)
        if self.pred == ptr:
            self.pred = None

    def start(self, known=None):
        self.setup(known)
        self.logger.debug("done setting up. proceeding to main loop")
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
            self.logger.debug("joined successfully")
            self.stabilize()
        else:
            # fake it
            self.last_stabilize = time.time()

    def stabilize(self):
        self.logger.debug("stabilizing")
        old_succ_list = self.succ_list
        while len(self.succ_list) > 0:
            succ = self.succ_list[0]
            try:
                nodes = self.get_pred_and_succs(succ)
            except QueryFailed:
                self.succ_list = self.succ_list[1:]
                continue
            new_succ = nodes[0]
            succ_list_of_succ = nodes[1:]
            self.succ_list = [succ] + succ_list_of_succ[:-1]
            if between(self.id, new_succ.id, succ.id):
                try:
                    succs = self.get_succ_list(new_succ)
                except QueryFailed:
                    self.succ_list = self.succ_list[1:]
                    continue
                self.succ_list = [new_succ] + succs[:-1]
            break
        if self.succ_list != old_succ_list:
            self.logger.info("stabilize: updated succ_list to {}".format(
                self.succ_list))
        self.notify(self.succ_list[0])
        self.last_stabilize = time.time()
        self.logger.debug("stabilized")

    def query(self, dst, msg, response_kind, timeout=QUERY_TIMEOUT):
        buffered = []
        start_time = time.time()
        try:
            self.io.send(dst, msg)
        except DeadNode, e:
            self.mark_node_dead(e.ptr)
            raise QueryFailed()
        while time.time() - start_time < timeout:
            res = self.io.recv()
            if res is not None:
                src, msg = res
                if msg.kind == response_kind and src.id == dst.id:
                    self.handle_all(buffered)
                    return msg.data
                else:
                    buffered.append((src, msg))
        self.handle_all(buffered)
        raise QueryFailed()

    def get_succ_list(self, node):
        if node == self.ptr:
            return self.succ_list
        msg = Message("get_succ_list", [])
        return self.query(node, msg, "got_succ_list")

    def get_pred_and_succs(self, node):
        msg = Message("get_pred_and_succs", [])
        return self.query(node, msg, "got_pred_and_succs")

    def join(self, known):
        self.logger.debug("joining with known = {}".format(known))
        succeeded = False
        while not succeeded:
            self.logger.debug("trying to join via {}".format(known.id))
            try:
                new_succ = self.find_successor(self.id, known)
            except QueryFailed:
                self.logger.debug("couldn't get succ. retrying in 5s")
                time.sleep(5)
                continue
            self.logger.debug("{} says my succ is {}".format(known.id,
                new_succ.id))
            try:
                succs = self.get_succ_list(new_succ)
            except QueryFailed:
                self.logger.debug("couldn't get succ_list. retrying in 5s")
                time.sleep(5)
                continue
            self.logger.debug(
                    "got new succ list from {}:".format(new_succ.id))
            self.succ_list = [new_succ] + succs[:-1]
            self.logger.info("join: got new succ_list {}".format(
                    self.succ_list))
            self.pred = None
            succeeded = True
        self.logger.debug("joined")


def launch_ring_of(n):
    ptrs = sorted([Pointer(ip="127.0.0.{}".format(i)) for i in range(1, n+1)])
    nodes = []
    for i, p in enumerate(ptrs):
        localhost = p.ip
        succs = ptrs[i+1:i+1+SUCC_LIST_LEN]
        if len(succs) < SUCC_LIST_LEN:
            succs += ptrs[:SUCC_LIST_LEN-len(succs)]
        node = Node(ip=localhost, pred=ptrs[i - 1], succ_list=succs)
        nodes.append(node)

    import multiprocessing
    for node in nodes:
        p = multiprocessing.Process(target=node.start)
        p.daemon = True
        p.start()

    return nodes

def join_demo():
    nodes = launch_ring_of(10)
    print "initial ring:", [node.ptr for node in nodes]
    known = nodes[6].ptr
    new_node = Node("127.0.0.100")
    print "adding new node:", new_node.ptr
    print
    time.sleep(3)
    new_node.start(known)

if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    join_demo()
