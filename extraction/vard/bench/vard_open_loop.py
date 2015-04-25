import time
import random

import vard

class VardOpenLoopClient(object):
    EPSILON = 0.000001
    
    def __init__(self, host, port, n_clients=100, put_prob=0.5):
        self.put_prob = put_prob
        self.master = vard.Client(host, port)
        self.clients = {}
        self.request_times = []
        self.outstanding = {}
        self.next_request_time = 0
        for i in range(n_clients):
            c = vard.Client(host, port, sock=self.master.sock)
            self.clients[c.client_id] = c
        self.available_clients = set(self.clients.keys())

    def handle_responses(self, resps):
        current_time = time.time()
        for r in resps:
            id = int(r[0])
            assert id in self.outstanding
            self.request_times.append(current_time - self.outstanding[id])
            del self.outstanding[id]
            self.available_clients.add(id)

    def make_request(self, client, key):
        if random.random() < self.put_prob:
            client.put_no_wait(key, 42)
        else:
            client.get_no_wait(key)
            
    def loop(self, n, delay):
        for i in range(n):
            current_time = time.time()
            id = self.available_clients.pop()
            c = self.clients[id]
            self.make_request(c, id)
            self.outstanding[id] = current_time
            next_request_time = current_time + delay
            while True:
                if current_time > next_request_time:
                    break
                self.handle_responses(self.master.get_responses(next_request_time - current_time + self.EPSILON))
                current_time = time.time()
        while self.outstanding:
            self.handle_responses(self.master.get_responses(None))
        return self.request_times
