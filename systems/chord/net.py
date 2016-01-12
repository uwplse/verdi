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

logger = logging.getLogger(__name__)

class Connection(object):
    def __init__(self, socket, remote_ip=None):
        self.socket = socket
        if remote_ip is None:
            remote_ip, _ = socket.getpeername()
        self.remote_ip = remote_ip
        self.buffer = b""

class ServerConnection(Connection):
    def read(self):
        closed = False
        try:
            # read in chunks of at most 4096 bytes until it breaks
            while True:
                chunk = self.socket.recv(4096)
                self.buffer += chunk
                if len(chunk) == 0:
                    closed = True
                if len(chunk) < 4096:
                    # definitely won't get more if we recv again
                    break
        except socket.error, e:
            if e.errno != errno.EAGAIN:
                raise
        return self.parse_buffer(), closed

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
        #XXX this won't work much of the time
        bytes_sent = self.socket.send(self.buffer)
        self.buffer = self.buffer[bytes_sent:]
        if len(self.buffer) == 0:
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

        self.logger = logging.getLogger(__name__ + "({})".format(self.ip))

        # ok, all set
        super(IOThread, self).__init__()
        # we want these to die when the thread that spawns them does
        self.daemon = True

    def send(self, dst, msg):
        self.sends.put((dst.ip, msg))

    def recv(self, timeout=None):
        if timeout is None:
            # busy polling because it makes it so ctrl-c works faster
            # i don't know why that is
            while True:
                try:
                    ip, msg = self.recvs.get(block=False)
                except Empty:
                    # nothing to receive.. keep polling
                    pass
        else:
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

    def select(self):
        to_write = [c.socket for c in self.outgoing_conns.values()]
        to_read = [c.socket for l in self.incoming_conns.values() for c in l]
        to_read.append(self.server_sock)
        readable_socks, writeable_socks, _ = select.select(to_read, to_write,
                [], 0)
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
        sock.connect((dst_ip, CHORD_PORT))
        sock.setblocking(0)
        self.outgoing_conns[dst_ip] = ClientConnection(sock)

    def run(self):
        self.listen()
        while True:
            try:
                dst_ip, msg = self.sends.get(block=False)
                # we only have one socket per destination
                if dst_ip not in self.outgoing_conns:
                    self.connect_to(dst_ip)
                self.logger.debug("{} <= {}".format(dst_ip, msg))
                self.outgoing_conns[dst_ip].queue_writes(msg.serialize())
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
