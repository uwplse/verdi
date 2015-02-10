import httplib
import urllib

class Client(object):

    def __init__(self, host, port):
        self.conn = httplib.HTTPConnection(host, port)

    def get(self, key):
        self.conn.request('GET', '/v2/keys/' + str(key) + '?quorum=true')
        self.conn.getresponse().read()

    def put(self, key, value):
        self.conn.request('PUT', '/v2/keys/' + str(key), urllib.urlencode({'value': str(value)}),
                          {"Content-type": "application/x-www-form-urlencoded"})
        self.conn.getresponse().read()
