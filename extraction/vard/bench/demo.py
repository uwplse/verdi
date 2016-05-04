from vard import Client

host, port = Client.find_leader([('localhost', 8001), ('localhost', 8002), ('localhost', 8003)])
key = 'key'
c1 = Client(host, port)
c2 = Client(host, port)

print c1.pre(key, 'A')
c1.delete(key)
