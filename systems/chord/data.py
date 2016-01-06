from collections import namedtuple
import socket
import struct

ID_SPACE_SIZE = 100

class Pointer(object):
    def __init__(self, ip):
        self.ip = ip
        self.id = self.hash(ip) % ID_SPACE_SIZE

    def __eq__(self, other):
        return self.ip == other.ip and self.id == other.id

    def hash(self, ip):
        # should use a real hash function, or whatever
        return struct.unpack("!L", socket.inet_aton(ip))[0]

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
        return "Pointer(ip={}, id={})".format(self.ip, self.id)

class MessageIncomplete(ValueError):
    pass

class Message(object):
    kinds = [
        "lookup_succ",
        "found_succ_for"
    ]
    Signature = namedtuple("Signature", ["arity", "id_first"])
    signatures = {
        "lookup_succ": Signature(1, True),
        "found_succ_for": Signature(2, True)
    }
    def __init__(self, kind, data):
        if kind not in Message.kinds:
            raise ValueError("Unknown message kind {}".format(kind))
        self.kind = kind
        if len(data) != Message.signatures[self.kind].arity:
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
        rest = bytes[length:]
        bytes = bytes[:length]
        header = bytes[:8]
        rest = bytes[8:]
        kind_idx, arity = struct.unpack(">II", header)
        kind = Message.kinds[kind_idx]
        data = []
        if arity != Message.signatures[kind].arity:
            raise ValueError("wrong arity >:(")
        if Message.signatures[kind].id_first:
            data = list(struct.unpack(">I", rest[:4]))
            rest = rest[4:]
            arity = arity - 1
        for i in range(0, arity):
            ptr = Pointer.deserialize(rest[:12])
            rest = rest[12:]
            data.append(ptr)
        return cls(kind, data), rest
