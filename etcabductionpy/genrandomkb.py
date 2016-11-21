
import random
import argparse
import sys
import os
import collections
import math
import itertools

import networkx as nx
from networkx import bipartite

random.seed(19851008)

def get_prob(mean):
    return min(max(1e-8, random.gauss(mean, 0.05)), 1.0)

def generate(args):

    # determine the number of nodes and edges.
    num_atoms = random.randint(args.minatoms, args.maxatoms)
    num_links = random.randint(num_atoms, args.maxedges)

    print >>sys.stderr, "Generating axioms..."
    print >>sys.stderr, "# atoms: %d, # links: %d" % (num_atoms, num_links)

    # create a random DAG.
    g = nx.gnm_random_graph(num_atoms, num_links, directed=True)
    g = nx.DiGraph([
        ("p%d" % u, "p%d" % v)
        for (u, v) in g.edges_iter()
        if u < v
        ])

    assert(nx.is_directed_acyclic_graph(g))

    # observation.
    head, obs = [], []

    for n in nx.topological_sort(g):
        if 0 == len(g.successors(n)):
            obs += [n]

        if 0 == len(g.predecessors(n)):
            head += [n]

    # resample the observation and reduce the graph.
    obs = random.sample(obs,
        random.randint(
            min(args.minobs, len(obs)),
            min(args.maxobs, len(obs)),
        )
    )

    kb = []
    avg_branch = []

    # rule generation.
    for n in g.nodes_iter():

        branch = 0
        branch += 1

        # posterior.
        if 0 < len(g.predecessors(n)):
            antecedents = list(g.predecessors(n))

            while len(antecedents) > 0:
                focus = antecedents[:random.randint(1, args.maxconjunct)]

                branch += 1
                kb += ["(if (and %s (etc_%s_%s %.8f)) (%s))" % (
                    " ".join(["(%s)" % j for j in focus]),
                    "".join(focus),
                    n,
                    get_prob(0.5),
                    n,
                    )]

                # next segment.
                antecedents = antecedents[len(focus):]

        avg_branch += [branch]

    for n in g.nodes_iter():

        # prior.
        kb += ["(if (and (etc_%s %.8f)) (%s))" % (
            n, get_prob(0.1), n,
        )]

    kb = ["""; Automatically generated synthetic knowledge base.
;
; [attributes]
;  longest path: %d
;  atoms: %d
;  links: %d
;  obs: %d
;  axioms: %d
;  branch: %.2f
;  tail: %s
;  head: %s
;
""" % (
    nx.dag_longest_path_length(g),
    len(g.nodes()),
    len(g.edges()),
    len(obs),
    len(kb),
    1.0*sum(avg_branch) / len(avg_branch),
    " ".join(obs),
    " ".join(head),
    )] + kb

    # viz = nx.to_agraph(g)
    # viz.layout()
    # viz.draw(sys.stdout)

    return kb, obs

def main():
    argparser = argparse.ArgumentParser(description='Random KB generator.')
    argparser.add_argument('-s', '--nsample',
                   type=int,
                   default=10,
                   help='Number of samples.')
    argparser.add_argument('-b', '--samplebaseid',
                   type=int,
                   default=0,
                   help='Base ID.')
    argparser.add_argument('-mina', '--minatoms',
                   type=int,
                   default=100,
                   help='Minimum number of atoms.')
    argparser.add_argument('-maxa', '--maxatoms',
                   type=int,
                   default=40000,
                   help='Maximum number of atoms.')
    argparser.add_argument('-maxe', '--maxedges',
                   type=int,
                   default=600000,
                   help='Maximum number of edges.')
    argparser.add_argument('-mino', '--minobs',
                   type=int,
                   default=6,
                   help='Minimum number of observations.')
    argparser.add_argument('-maxo', '--maxobs',
                   type=int,
                   default=12,
                   help='Maximum number of observations.')
    argparser.add_argument('-maxc', '--maxconjunct',
                   type=int,
                   default=6,
                   help='Maximum number of conjunction.')
    args = argparser.parse_args()

    for i in xrange(args.nsample):
        fn_kb, fn_obs = "data/synthetic/kb%d.lisp" % (1+args.samplebaseid+i), "data/synthetic/obs%d.lisp" % (1+args.samplebaseid+i)

        kb, obs = generate(args)

        print >>sys.stderr, "# obs: %d, # axioms: %d" % (len(obs), len(kb))
        print >>sys.stderr, "Writing to %s... " % fn_kb

        with open(fn_kb, "w") as f:
            for r in kb:
                print >>f, r

        with open(fn_obs, "w") as f:
            print >>f, " ".join(["(%s)" % ob for ob in obs])

        os.system("python etcabductionpy -k %s -kc %s.mcdb" % (fn_kb, fn_kb))

if "__main__" == __name__:
    main()
