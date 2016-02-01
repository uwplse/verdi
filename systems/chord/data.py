from collections import namedtuple
from functools import total_ordering
import socket
import struct
import hashlib

ID_SPACE_SIZE = 2048
SUCC_LIST_LEN = 3

def hash(string):
    h = hashlib.sha256()
    h.update(string)
    return long(h.hexdigest(), 16) % ID_SPACE_SIZE

Query = namedtuple("Query", ["dst", "msg", "res_kind", "cb"])
State = namedtuple("State", [
    "id",
    "pred",
    "succ_list",
    "joined",
    "rectify_with"])

@total_ordering
class Pointer(object):
    def __init__(self, ip, id=None):
        self.ip = ip
        self.id = hash(ip)
        if id is not None and id != self.id:
            raise ValueError("someone hashed something wrong: {} != {}".format(
                id, self.id))

    def __eq__(self, other):
        if isinstance(other, Pointer):
            return self.id == other.id
        else:
            return False

    def __lt__(self, other):
        return self.id < other.id

    def serialize(self):
        return socket.inet_aton(self.ip) + struct.pack(">I", self.id)

    @classmethod
    def deserialize(cls, bytestring):
        if len(bytestring) != 8:
            raise ValueError()
        ip = socket.inet_ntoa(bytestring[:4])
        id = struct.unpack(">I", bytestring[4:])[0]
        ptr = cls(ip)
        if ptr.id != id:
            raise ValueError("computed id != provided id :(")
        return ptr

    def __repr__(self):
        return 'Pointer("{}", {})'.format(self.ip, self.id)

class MessageIncomplete(ValueError):
    pass

class Signature(object):
    def __init__(self, arity, id_first=False, response=False):
        self.arity = arity
        self.id_first = id_first
        self.response = response

class Message(object):
    signatures = {
        "get_best_predecessor": Signature(1, True),
        "got_best_predecessor": Signature(1, False),
        "get_succ_list": Signature(0),
        "got_succ_list": Signature(None, False),
        "get_pred": Signature(0),
        "got_pred": Signature(1),
        "get_pred_and_succs": Signature(0),
        "got_pred_and_succs": Signature(None, False),
        "notify": Signature(0),
        "ping": Signature(0),
        "pong": Signature(0)
    }
    kinds = list(signatures.keys())

    def __init__(self, kind, data=None):
        if data is None:
            data = []
        if kind not in Message.kinds:
            raise ValueError("Unknown message kind {}".format(kind))
        self.kind = kind
        arity = Message.signatures[self.kind].arity
        if arity is not None and len(data) != arity:
            message = "Incorrect arity {} for kind {}".format(len(data), kind)
            raise ValueError(message)
        self.arity = len(data)
        self.data = data

    def __repr__(self):
        return "Message({}, {})".format(self.kind, self.data)

    def serialize(self):
        kind_idx = Message.kinds.index(self.kind)
        byte_string = struct.pack(">II", kind_idx, self.arity)
        data = self.data
        if Message.signatures[self.kind].id_first:
            byte_string += struct.pack(">I", data[0])
            data = data[1:]
        for ptr in data:
            byte_string += ptr.serialize()
        return struct.pack(">I", len(byte_string)) + byte_string

    @classmethod
    def deserialize(cls, bytes):
        if len(bytes) < 4:
            raise MessageIncomplete()
        length = struct.unpack(">I", bytes[:4])[0]
        bytes = bytes[4:]
        if len(bytes) < length:
            raise MessageIncomplete()
        leftovers = bytes[length:]
        bytes = bytes[:length]
        header = bytes[:8]
        rest = bytes[8:]
        kind_idx, arity = struct.unpack(">II", header)
        kind = Message.kinds[kind_idx]
        data = []
        kind_arity = Message.signatures[kind].arity
        if kind_arity is not None and kind_arity != arity:
            raise ValueError("wrong arity >:(")
        if Message.signatures[kind].id_first:
            data = list(struct.unpack(">I", rest[:4]))
            rest = rest[4:]
            arity = arity - 1
        for i in range(0, arity):
            ptr = Pointer.deserialize(rest[:8])
            rest = rest[8:]
            data.append(ptr)
        return cls(kind, data), leftovers
