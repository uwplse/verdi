import socket
import re

class LeaderChanged(Exception):
    pass

class Client(object):

    response_re = re.compile(r'Response\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)')

    def __init__(self, host, port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.connect((host, port))

    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def serialize(self, arg):
        if arg is None:
            return '-'
        return str(arg)

    def send_command(self, cmd, arg1=None, arg2=None, arg3=None):
        self.sock.send(cmd + ' ' + ' '.join(map(self.serialize, (arg1, arg2, arg3))))

    def process_response(self):
        data = self.sock.recv(256).strip()
        if data == 'NotLeader':
            raise LeaderChanged
        match = self.response_re.match(data)
        return [self.deserialize(match.group(n)) for n in (1,2,3)]

    def get(self, k):
        self.send_command('GET', k)
        return self.process_response()[1]

    def put(self, k, v):
        self.send_command('PUT', k, v)
        return self.process_response()[1]

    def delete(self, k):
        self.send_command('DEL', k)
        self.process_response()[1]

    def compare_and_set(self, k, current, new):
        self.send_command('CAS', k, current, new)
        if self.process_response()[2] == new:
            return True
        return False

    def compare_and_delete(self, k, current):
        self.send_command('CAD', k, current)
        if self.process_response()[2] is None:
            return True
        return False
