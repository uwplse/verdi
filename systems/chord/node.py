from collections import defaultdict, namedtuple
import logging
import sys
import time

from data import *
from net import IOThread, DeadNode

# these should be higher in real life, probably
DEFAULT_STABILIZE_INTERVAL = 4
QUERY_TIMEOUT = 1

def between(a, x, b):
    if a < b:
        return a < x < b
    else:
        return a < x or x < b

class QueryFailed(IOError):
    pass

class UnexpectedMessage(IOError):
    pass

class InterruptedQuery(RuntimeError):
    pass

class BadQueryCallbackResult(TypeError):
    pass

def trim_succs(succs):
    if len(succs) > SUCC_LIST_LEN:
        return succs[:SUCC_LIST_LEN]
    else:
        return succs

def remove_all_refs(state, ptr):
    if state.pred == ptr:
        state = state._replace(pred=None)
    if state.rectify_with == ptr:
        state = state._replace(rectify_with=None)
    if ptr in state.succ_list:
        new_list = state.succ_list[:]
        new_list.remove(ptr)
        state = state._replace(succ_list=new_list)
    return state

# pointer -> (msg -> query or [msg], state) -> query
def ping(node, cb):
    return Query(node, Message("ping"), "pong", cb)
def get_succ_list(node, cb):
    return Query(node, Message("get_succ_list"), "got_succ_list", cb)
def get_pred_and_succs(node, cb):
    return Query(node, Message("get_pred_and_succs"), "got_pred_and_succs", cb)
def get_best_predecessor(node, id, cb):
    return Query(node, Message("get_best_predecessor", [id]),
            "got_best_predecessor", cb)

# state -> pointer -> query
def rectify_query(pred, notifier):
    def cb(state, pong):
        if pong is None or between(state.pred.id, notifier.id, state.ptr.id):
            return None, state._replace(pred=notifier)
        else:
            return None, state
    return ping(pred, cb)

def notify(node):
    if node is None:
        raise TypeError(node)
    return [(node, Message("notify"))]

# state -> query or single notify message
def stabilize_query(succ):
    def cb(state, msg):
        if msg is not None:
            pred_and_succ_list = msg.data
            pred, succs = pred_and_succ_list[0], pred_and_succ_list[1:]
            new_succ = pred
            new_succs = trim_succs([succ] + succs)
            new_state = state._replace(succ_list=new_succs)
            if between(state.ptr.id, new_succ.id, succ.id):
                return stabilize2(new_succ), new_state
            else:
                return notify(succ), new_state
        else:
            return None, state
    return get_pred_and_succs(succ, cb)

def stabilize2(new_succ):
    def cb(state, msg):
        if msg is not None:
            succs = trim_succs([new_succ] + msg.data)
            return notify(new_succ), state._replace(succ_list=succs)
        else:
            return notify(state.succ_list[0]), state
    return get_succ_list(new_succ, cb)

# state -> pointer -> query
def join_query(known):
    def cb(state, msg):
        if msg is not None:
            new_succ = msg.data[0]
            return join2(new_succ), state
        else:
            return None, state
    return lookup_succ(known, state.ptr.id, cb)

# pointer -> id -> (msg -> query * state) -> query
def lookup_succ(node, id, cb):
    def inner_cb(state, msg):
        if msg is not None:
            return get_succ(msg.data[0], cb), state
        else:
            return cb(state, msg)
    return lookup_predecessor(node, id, inner_cb)

def get_succ(node, cb):
    def inner_cb(state, msg):
        if msg is not None:
            return cb(state, msg.data[0])
        else:
            return cb(state, msg)
    return get_succ_list(node, cb)

def lookup_predecessor(node, id, cb):
    def inner_cb(state, msg):
        if msg is not None:
            best_pred = msg.data[0]
            if best_pred == node:
                # it's the best predecessor
                return cb(state, msg)
            else:
                # it's referring us to a better one
                return lookup_predecessor(best_pred, id, cb), state
        else:
            return cb(state, msg)
    return get_best_predecessor(node, id, inner_cb)


# state -> pointer -> query
def join2(new_succ):
    def cb(state, msg):
        if msg is not None:
            succs = trim_succs([new_succ] + msg.data)
            return None, state._replace(succ_list=succs, pred=None, joined=True)
        else:
            return None, state
    return get_succ_list(new_succ, cb)


class Node(object):
    @property
    def state(self):
        return self._state

    @state.setter
    def state(self, new_state):
        for i, new_val in enumerate(new_state):
            if not hasattr(self, "_state") or self._state[i] != new_val:
                name = new_state._fields[i]
                val = new_state[i]
                if isinstance(val, list) and len(val) > 0:
                    if isinstance(val[0], Pointer):
                        val = "[{}]".format(", ".join(str(p.id) for p in val))
                elif isinstance(val, Pointer):
                    val = val.id
                self.logger.info("{} := {}".format(name, str(val)))
        self._state = new_state

    def __init__(self, ip, pred=None, succ_list=None,
            stabilize_interval=DEFAULT_STABILIZE_INTERVAL):
        ptr = Pointer(ip)
        self.logger = logging.getLogger(__name__ + "({})".format(ptr.id))
        self.stabilize_interval = stabilize_interval
        state = State(ptr=ptr, pred=pred, succ_list=[], joined=False,
                rectify_with=None)
        self.query = None


        if succ_list is None:
            if pred is not None:
                raise ValueError("provided pred but not succ_list")
        elif len(succ_list) == SUCC_LIST_LEN:
            if pred is None:
                raise ValueError("provided succ_list but not pred")
            state = state._replace(joined=True, succ_list=succ_list)
        else:
            raise ValueError("succ_list isn't the right length")

        self.state = state

        self.io = IOThread(ip)
        self.started = False

        # map from ids to the clients that have asked for the id's successor
        self.lookup_clients = defaultdict(list)

    def timeout_handler(self, state):
        if self.query is None and state.joined:
            self.last_stabilize = time.time()
            return self.start_query(stabilize_query(state.succ_list[0])), state
        elif time.time() - self.query_sent > QUERY_TIMEOUT:
            msgs, state = self.mark_node_dead(state, self.query.dst)
            return msgs, state
        else:
            return [], state

    # can only be run once we've joined and stabilized
    def main_loop(self):
        while True:
            if time.time() - self.last_stabilize > self.stabilize_interval:
                outs, self.state = self.timeout_handler(self.state)
                for dst, msg in outs:
                    self.io.send(dst, msg)
            res = self.io.recv()
            if res is not None:
                src, msg = res
                sends, self.state = self.recv_handler(self.state, src, msg)
                self.send_all(sends)

    # state -> ptr -> [ptr * msg] * state
    def mark_node_dead(self, state, ptr):
        self.logger.debug("{}".format([p.id for p in state.succ_list]))
        self.logger.debug("marking node {} dead".format(ptr.id))
        state = remove_all_refs(state, ptr)
        if self.query is not None and self.query.dst == ptr:
            self.logger.debug("query {} failed".format(self.query))
            output, state = self.query.cb(state, None) 
            self.logger.debug("{}".format([p.id for p in state.succ_list]))
            return self.handle_cb_result(state, output)
        else:
            return [], state

    # state -> return value of a callback -> [ptr * msg] * state
    def handle_cb_result(self, state, output):
        self.query = None
        if output is None:
            return self.try_rectify(state)
        elif isinstance(output, Query):
            return self.start_query(output), state
        elif isinstance(output, list):
            rectify_sends, state = self.try_rectify(state)
            return output + rectify_sends, state
        else:
            raise BadQueryCallbackResult(output)

    # this is like closest_preceding_finger in the chord paper
    # but I have no finger tables (yet)
    def best_predecessor(self, state, id):
        for node in reversed(state.succ_list):
            if between(state.ptr.id, node.id, id):
                return node
        return state.ptr

    # state -> ptr -> msg -> [ptr * msg], state
    # side effects: changing self.query
    def recv_handler(self, state, src, msg):
        kind = msg.kind
        outs = []

        if kind == "get_best_predecessor":
            id = msg.data[0]
            pred = self.best_predecessor(state, id)
            outs = [(src, Message("got_best_predecessor", [pred]))]
        elif kind == "get_succ_list":
            outs = [(src, Message("got_succ_list", state.succ_list))]
        elif kind == "get_pred_and_succs":
            pred_and_succs = [state.pred] + state.succ_list
            msg = Message("got_pred_and_succs", pred_and_succs)
            outs = [(src, msg)]
        elif kind == "notify":
            state = state._replace(rectify_with=src)
            if self.query is None:
                outs, state = self.try_rectify(state)
        elif kind == "ping":
            outs = [(src, Message("pong"))]
        elif self.query is not None:
            if kind == self.query.res_kind and src == self.query.dst:
                res = self.query.cb(state, msg)
                output, state = res
                outs, state = self.handle_cb_result(state, output)
            elif time.time() - self.query_sent > QUERY_TIMEOUT:
                dead_msgs, state = self.mark_node_dead(state, self.query.dst)
                outs, state = dead_msgs + self.recv_handler(state, src, msg)
        else:
            raise UnexpectedMessage(msg)
        return outs, state

    # state -> [ptr * msg], state
    def try_rectify(self, state):
        if state.rectify_with is None:
            return [], state
        if self.query is not None:
            raise InterruptedQuery(self.query)
        if state.pred is None:
            state = state._replace(pred=state.rectify_with)
            return [], state
        else:
            new_succ = state.rectify_with
            state = state._replace(rectify_with=None)
            return self.start_query(rectify_query(state.pred, new_succ)), state

    def send_all(self, sends):
        for dst, msg in sends:
            self.io.send(dst, msg)

    def start(self, known=None):
        if self.started:
            raise RuntimeError("already started")
        self.started = True
        self.io.start()
        sends, self.state = self.start_handler(self.state, known)
        self.send_all(sends)
        self.main_loop()

    # query -> [ptr * msg]
    # side effects: setting self.query_sent and self.query
    def start_query(self, query):
        if self.query is not None:
            raise InterruptedQuery(self.query)
        self.query = query
        self.query_sent = time.time()
        return [(query.dst, query.msg)]
        

    # state -> ptr -> [ptr * msg] * state
    # or state -> None -> [ptr * msg] * state, since you can give this a fully
    # initialized state to skip join stuff
    def start_handler(self, state, known):
        if len(state.succ_list) == 0:
            if known is None:
                raise ValueError("can't join without a known node!")
            self.last_stabilize = time.time() - self.stabilize_interval
            return self.start_query(join_query(known)), state
        else:
            # fake it
            self.last_stabilize = time.time()
            return [], state

def launch_node(ip, pred, succ_list):
    import multiprocessing
    import signal
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

def join_demo():
    logging.debug("running join_demo()")
    nodes, procs = launch_ring_of(10)
    print "initial ring:", [node.ptr for node in nodes]
    known = nodes[6].ptr
    new_node = Node("127.0.0.100")
    time.sleep(0.5)
    print "adding new node:", new_node.ptr
    new_node.start(known)

def kill_demo():
    logging.debug("running kill_demo()")
    import os
    nodes, procs = launch_ring_of(40)
    kill_idx = 17
    time.sleep(2)
    for kill_idx in [3,5]:
        logging.warn("killing node {}".format(nodes[kill_idx].state.ptr.id))
        procs[kill_idx].terminate()
    procs[0].join()

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
    kill_demo()
