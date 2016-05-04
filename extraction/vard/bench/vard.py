import socket
import re
import uuid
from select import select

def poll(sock, timeout):
    return sock in select([sock], [], [], timeout)[0]

MAX_ID = 2**31

class LeaderChanged(Exception):
    pass

class Client(object):
    class NoLeader(Exception):
        pass

    @classmethod
    def find_leader(cls, cluster):
        # cluster should be a list of [(host, port)] pairs
        for (host, port) in cluster:
            c = cls(host, port)
            try:
                c.get('a')
            except LeaderChanged:
                continue
            else:
                return (host, port)
        raise cls.NoLeader
    
    response_re = re.compile(r'Response\W+([0-9]+)\W+([0-9]+)\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)')

    def __init__(self, host, port, sock=None):
        if not sock:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock
        self.client_id = uuid.uuid4().int % MAX_ID
        self.request_id = 0
        
    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def serialize(self, arg):
        if arg is None:
            return '-'
        return str(arg)

    def send_command(self, cmd, arg1=None, arg2=None, arg3=None):
        self.sock.send(str(self.client_id) + ' ' + str(self.request_id) + ' ' + cmd + ' ' + ' '.join(map(self.serialize, (arg1, arg2, arg3))) + '\n')
        self.request_id += 1

    def send_command_bad(self, cmd, arg1=None, arg2=None, arg3=None):
        self.sock.send(str(self.client_id) + ' ' + str(self.request_id) + ' ' + cmd + ' ' + ' '.join(map(self.serialize, (arg1, arg2, arg3))) + '\n')

    def parse_response(self, data):
        if data.startswith('NotLeader'):
            raise LeaderChanged
        try:
            match = self.response_re.match(data)
            return [self.deserialize(match.group(n)) for n in (1,2,3,4,5)]
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e
        
    def process_response(self):
        while True:
            data = self.sock.recv(256).strip()
            if data != '':
                return self.parse_response(data)

    def get_responses(self, timeout):
        if poll(self.sock, timeout):
            data = ''
            while poll(self.sock, 0):
                data += self.sock.recv(1024)
            return map(self.parse_response, data.strip().split('\n'))
        return []

    def get(self, k):
        self.send_command('GET', k)
        return self.process_response()[3]

    def get_no_wait(self, k):
        self.send_command('GET', k)

    def put_no_wait(self, k, v):
        self.send_command('PUT', k, v)

    def put(self, k, v):
        self.send_command('PUT', k, v)
        return self.process_response()[3]

    def pre(self, k, v):
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command_bad('PRE', k, v)
        self.process_response()[3]
        self.send_command('PRE', k, v)
        return self.process_response()[3]

    def delete(self, k):
        self.send_command('DEL', k)
        self.process_response()[3]

    def compare_and_set(self, k, current, new):
        self.send_command('CAS', k, current, new)
        if self.process_response()[4] == new:
            return True
        return False

    def compare_and_delete(self, k, current):
        self.send_command('CAD', k, current)
        if self.process_response()[4] is None:
            return True
        return False
