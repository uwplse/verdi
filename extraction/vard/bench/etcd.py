import httplib
import urllib

class Client(object):
    class NoLeader(Exception):
        pass

    @classmethod
    def find_leader(cls, cluster):
        # cluster should be a list of [(host, port)] pairs
        for (host, port) in cluster:
            c = cls(host, port)
            c.conn.request('GET', '/v2/stats/self')
            if '"state":"StateLeader"' in c.conn.getresponse().read():
                return (host, port)
        raise cls.NoLeader
    

    def __init__(self, host, port):
        self.conn = httplib.HTTPConnection(host, port)

    def get(self, key):
        self.conn.request('GET', '/v2/keys/' + str(key) + '?quorum=true')
        self.conn.getresponse().read()

    def put(self, key, value):
        self.conn.request('PUT', '/v2/keys/' + str(key), urllib.urlencode({'value': str(value)}),
                          {"Content-type": "application/x-www-form-urlencoded"})
        self.conn.getresponse().read()
