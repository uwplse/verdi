import argparse
import sys
from collections import defaultdict, namedtuple

import data
from node import between

class Node(object):
    def __init__(self, pred=None, succ_list=None, joined=False):
        self.pred = pred
        if succ_list is None:
            self.succ_list = []
        self.joined = joined
    def __repr__(self):
        return "Node(pred={pred}, succ_list={succ_list}, joined={joined})".format(**self.__dict__)


invariants = ["at_least_one_ring", "at_most_one_ring", "ordered_ring",
              "connected_appendages", "ordered_successor_lists",
              "globally_correct_node_data", "ideal_ring"]

class NodeLostSuccessors(RuntimeError):
    pass

def best_succ(nodes, id):
    candidates = nodes[id].succ_list
    if candidates is None:
        raise NodeLostSuccessors(id)
    for succ in candidates:
        if succ in nodes:
            return succ
    raise NodeLostSuccessors(id)

def report(nodes, succ_list_len):
    results = {}
    aux_results = {}
    ring_members = set()
    ordered_successor_lists = True
    for id in nodes:
        if len(nodes[id].succ_list) > 0:
            succ_list = [id] + nodes[id].succ_list
            for i, succ in enumerate(succ_list[:-2]):
                if not between(succ, succ_list[i+1], succ_list[i+2]):
                    ordered_successor_lists = False
                    break
        visible = ring_members_visible_from(nodes, id)
        ring_members.update(visible)

    # OrderedSuccessorLists
    results["ordered_successor_lists"] = ordered_successor_lists

    # AtLeastOneRing
    results["at_least_one_ring"] = len(ring_members) > 0

    # AtMostOneRing
    if len(nodes) > 0:
        results["at_most_one_ring"] = len(visible) == len(ring_members)
    else:
        results["at_most_one_ring"] = True

    # OrderedRing
    ring = sorted(ring_members)
    n = len(ring)
    if not results["at_most_one_ring"]:
        results["ordered_ring"] = False
    elif n < 3:
        results["ordered_ring"] = True
    elif n == 3:
        results["ordered_ring"] = between(ring[0], ring[1], ring[2])
    else:
        ring = sorted(ring_members)
        i, j, k = 1, 2, 3
        ok = between(ring[0], ring[i], ring[j])
        while ok and i != 0:
            if not between(ring[i], ring[j], ring[k]):
                ok = False
            i = (i + 1) % n
            j = (j + 1) % n
            k = (k + 1) % n
        results["ordered_ring"] = ok

    # ideal ring?
    aux_results["ideal_ring"] = len(ring_members) == len(nodes) and results["ordered_ring"]

    # globally correct, fully filled in successor lists? and preds?
    ordered_nodes = sorted(nodes)
    ok = True
    node_count = len(ordered_nodes)
    for i, id in enumerate(ordered_nodes):
        if len(nodes[id].succ_list) < succ_list_len:
            ok = False
            break
        if nodes[id].pred != ordered_nodes[i - 1]:
            ok = False
            break
        if len(ordered_nodes) - i > 3:
            for j, succ_id in enumerate(nodes[id].succ_list):
                if succ_id != ordered_nodes[(i + j + 1) % node_count]:
                    ok = False
                    break
    aux_results["globally_correct_node_data"] = ok

    # ConnectedAppendages
    if not results["at_least_one_ring"] or not results["at_most_one_ring"]:
        results["connected_appendages"] = False
    else:
        connected = set()
        for id in set(nodes) - ring_members:
            if len(ring_members_visible_from(nodes, id)) > 0:
                connected.add(id)
        results["connected_appendages"] = set(nodes) == connected | ring_members
        if not results["connected_appendages"]:
            print sorted(nodes)
            print sorted(ring_members)
            print sorted(connected)
            print sorted(set(nodes) - ring_members - connected)
    return results, aux_results


def ring_members_visible_from(nodes, node_id):
    if len(nodes[node_id].succ_list) == 0:
        return set()
    cur = best_succ(nodes, node_id)
    path = [node_id]
    while cur not in path:
        path.append(cur)
        if len(nodes[cur].succ_list) == 0:
            return set()
        cur = best_succ(nodes, cur)
    return set(path[path.index(cur):])

def dangling_pointers(nodes):
    for id in nodes:
        node = nodes[id]
        if node.pred is not None and node.pred not in nodes:
            return True
        for id in node.succ_list:
            if id not in nodes:
                return True
    return False

def die(msg):
    sys.stdin.close()
    print msg
    sys.exit(1)

def update_nodes_from(nodes, line):
    if "killing node" in line:
        del nodes[int(line.split()[-1])]
        return

    l_bracket = line.index("(")
    r_bracket = line.index(")")
    node_id = int(line[l_bracket+1:r_bracket])
    assignment = line[r_bracket+2:].strip()

    prop, val = assignment.split(" := ")
    val = val.strip()
    if prop == "pred":
        if val == "None":
            nodes[node_id].pred = None
        else:
            nodes[node_id].pred = int(val)
    elif prop == "succ_list":
        if val is "None":
            nodes[node_id].succ_list = None
        else:
            val = val[1:-1]
            if val == "":
                nodes[node_id].succ_list = []
            else:
                nodes[node_id].succ_list = [int(id) for id in val.split(", ")]
    elif prop == "joined":
        nodes[node_id].joined = val == "True"

def print_report_for(nodes, line, buffered_lines, starting_up, last, succ_list_len):
    if (len(nodes) == 0 or dangling_pointers(nodes)) and starting_up:
        buffered_lines.append(line)
        return buffered_lines, starting_up, last

    # a node isn't *really* a node until its join operation has completed.
    visible_nodes = {id: node for id, node in nodes.items() if node.joined}
    try:
        results, aux_results = report(dict(visible_nodes), succ_list_len)
    except NodeLostSuccessors:
        print line
        print_state(visible_nodes)
        raise
    if starting_up and all(results.values()):
        starting_up = False
    outputs = []
    for invariant in invariants:
        if invariant in results:
            outputs.append("t" if results[invariant] else "f")
        elif invariant in aux_results:
            outputs.append("t" if aux_results[invariant] else "f")

    output = " ".join(outputs)
    for line in buffered_lines:
        print indent + "\t" + line[:-1]
    last_result = " ".join(outputs)
    print last_result + "\t" + line[:-1]

    if not starting_up and not all(results.values()):
        print_state(visible_nodes)
        die("invariant broken!")

    return [], starting_up, last_result

def print_state(nodes):
    for id in sorted(nodes):
        print "{}\t{}\t{}".format(nodes[id].pred, id, nodes[id].succ_list)

parser = argparse.ArgumentParser()
parser.add_argument("--succ-list-len", "-l",
                    metavar="N",
                    type=int,
                    default=data.SUCC_LIST_LEN)
args = parser.parse_args()

print "Running with SUCC_LIST_LEN := {}".format(data.SUCC_LIST_LEN)

for i, invariant in enumerate(invariants):
    print "| " * i + invariant
indent = "| "*(len(invariants)-1) + "|"
print indent
nodes = defaultdict(Node)
buffered_lines = []
last_result = indent
starting_up = True
for line in sys.stdin:
    if "killing node" in line or line.startswith("INFO:") and " := " in line:
        # log line mutates state
        update_nodes_from(nodes, line)
        new_vals = print_report_for(nodes, line, buffered_lines, starting_up, last_result,
                args.succ_list_len)
        print nodes
        buffered_lines, starting_up, last_result = new_vals
    else:
        # log line is just debug information
        print last_result + "\t" + line[:-1]
    sys.stdout.flush()
