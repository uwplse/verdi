#!/usr/bin/env python

with open('index-template.html', 'r') as f:
    template = f.read()

with open('compile-times.txt', 'r') as f:
    compile_times = f.read()

with open('compile-times-raft.txt', 'r') as f:
    compile_times_raft = f.read()

html = template
html = html.replace('COMPILE_TIMES_RAFT', compile_times_raft)
html = html.replace('COMPILE_TIMES', compile_times)

with open('index.html', 'w') as f:
    f.write(html)
