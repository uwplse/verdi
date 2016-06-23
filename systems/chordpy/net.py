from collections import defaultdict
import errno
from Queue import Queue, Empty
import logging
import select
import socket
import threading

from data import Pointer, Message, MessageIncomplete

CHORD_PORT = 6000
MAX_CONNS = 30
RECV_TIMEOUT = 1

logger = logging.getLogger(__name__)

class DeadNode(RuntimeError):
    def __init__(self, ptr):
        super(DeadNode, self).__init__()
        self.ptr = ptr

class Connection(object):
    def __init__(self, socket, remote_ip):
        self.socket = socket
        self.remote_ip = remote_ip
        self.buffer = b""

    def broken(self):
        try:
            self.socket.getpeername()
        except socket.error:
            return True
        return False

class ServerConnection(Connection):
    def read(self):
        closed = False
        # read in chunks of at most 4096 bytes until it breaks
        while True:
            try:
                chunk = self.socket.recv(4096)
            except socket.error, e:
                if e.errno == errno.EAGAIN:
                    # there's nothing to read right now
                    break
                else:
                    raise
            self.buffer += chunk
            if len(chunk) == 0:
                closed = True
            if len(chunk) < 4096:
                # won't get more if we recv again
                break
        msgs = self.parse_buffer()
        if closed and len(self.buffer) != 0:
            raise RuntimeError("connection closed with a message incomplete")
        return msgs, closed

    def parse_buffer(self):
        msgs = []
        while self.buffer != "":
            try:
                msg, rest = Message.deserialize(self.buffer)
                msgs.append(msg)
                self.buffer = rest
            except MessageIncomplete:
                break
        return msgs

class ClientConnection(Connection):
    def queue_writes(self, bytes):
        self.buffer += bytes

    def write(self):
        try:
            bytes_sent = self.socket.send(self.buffer)
            self.buffer = self.buffer[bytes_sent:]
        except socket.error, e:
            if e.errno != errno.EAGAIN:
                raise
        if len(self.buffer) == 0:
            self.socket.shutdown(socket.SHUT_RDWR)
            self.socket.close()
            return True
        return False

class IOThread(threading.Thread):
    def __init__(self, ip):
        self.ip = ip
        # queues of (ip, Message) tuples
        self.sends = Queue()
        self.recvs = Queue()
        # map from ips to ClientConnection objects
        self.outgoing_conns = {}
        # map from ips to lists of ServerConnection objects
        self.incoming_conns = defaultdict(list)
        # set of ips
        self.dead_nodes = set()

        self.logger = logging.getLogger(__name__ + "({})".format(self.ip))

        # ok, all set
        super(IOThread, self).__init__()
        # we want these to die when the thread that spawns them does
        self.daemon = True

    def send(self, dst, msg):
        self.sends.put((dst.ip, msg))

    def recv(self, timeout=RECV_TIMEOUT):
        try:
            ip, msg = self.recvs.get(timeout=timeout)
        except Empty:
            # timed out
            return None
        return Pointer(ip), msg

    def listen(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.bind((self.ip, CHORD_PORT))
        sock.listen(MAX_CONNS)
        self.server_sock = sock

    def prune_conns(self):
        """Look through outgoing and incoming connections for broken
        connections and remove them.

        Returns the connections that were pruned."""
        pruned = []
        for ip, conn in self.outgoing_conns:
            if conn.broken():
                del self.outgoing_conns[ip]
                pruned.append(conn)
        for ip, conns in self.outgoing_conns:
            for conn in conns:
                if conn.broken():
                    self.outgoing_conns[ip].remove(conn)
                    pruned.append(conn)
        return pruned

    def select(self):
        to_write = [c.socket for c in self.outgoing_conns.values()]
        to_read = [c.socket for l in self.incoming_conns.values() for c in l]
        to_read.append(self.server_sock)
        select_succeeded = False
        while not select_succeeded:
            try:
                readable_socks, writeable_socks, _ = select.select(to_read,
                        to_write, [], 0)
                select_succeeded = True
            except select.error, e:
                if e.errno == errno.EBADF:
                    # there's a broken or closed connection somewhere
                    pruned = set(self.prune_conns())
                    self.logger.debug("got EBADF, pruned {} connections"
                            .format(len(pruned)))
                    if len(pruned) == 0:
                        raise
                    readable_socks = set(readable_socks) - pruned
                    writeable_socks = set(writeable_socks) - pruned
                else:
                    raise
        can_accept = False
        if self.server_sock in readable_socks:
            readable_socks.remove(self.server_sock)
            can_accept = True
        readable = []
        for sock in readable_socks:
            conns = self.incoming_conns[sock.getpeername()[0]]
            for conn in conns:
                if conn.socket is sock:
                    readable.append(conn)
        writeable = []
        for sock in writeable_socks:
            writeable.append(self.outgoing_conns[sock.getpeername()[0]])
        return can_accept, readable, writeable

    def connect_to(self, dst_ip):
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.bind((self.ip, 0))
        try:
            sock.connect((dst_ip, CHORD_PORT))
        except socket.error, e:
            self.dead_nodes.add(dst_ip)
            return None
        sock.setblocking(0)
        conn = ClientConnection(sock, dst_ip)
        return conn

    def run(self):
        self.listen()
        while True:
            try:
                dst_ip, msg = self.sends.get(block=False)
                # we only have one socket per destination
                if dst_ip not in self.outgoing_conns:
                    conn = self.connect_to(dst_ip)
                if conn is not None:
                    self.logger.debug("{} <= {}".format(dst_ip, msg))
                    self.outgoing_conns[dst_ip] = conn
                    conn.queue_writes(msg.serialize())
                # otherwise we just drop the message
            except Empty:
                # nothing to send.
                pass
            can_accept, readable, writeable = self.select()
            if can_accept:
                conn, (ip, _) = self.server_sock.accept()
                new_connection = ServerConnection(conn, ip)
                self.incoming_conns[ip].append(new_connection)
            for conn in writeable:
                done = conn.write()
                if done:
                    del self.outgoing_conns[conn.remote_ip]
            for conn in readable:
                msgs, closed = conn.read()
                for msg in msgs:
                    self.logger.debug("{} => {}".format(conn.remote_ip, msg))
                    self.recvs.put((conn.remote_ip, msg))
                if closed:
                    self.incoming_conns[conn.remote_ip].remove(conn)
