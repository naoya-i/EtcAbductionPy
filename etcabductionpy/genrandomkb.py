
import random
import argparse
import sys
import os
import collections
import math

import networkx as nx

random.seed(19851008)

def get_prob(mean):
    return min(max(1e-8, random.gauss(mean, 0.05)), 1.0)

def generate(args, num_atoms, num_links):

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

    # Resample the observation and reduce the graph.
    obs = random.sample(obs,
        random.randint(
            min(args.minobs, len(obs)),
            min(args.maxobs, len(obs)),
        )
    )
    nodes = []
    nodes += obs

    for ob in obs:
        nodes += nx.ancestors(g, ob)

    g = g.subgraph(nodes)

    kb = []
    avg_branch = []

    # rule generation.
    for n in g.nodes_iter():

        branch = 0

        # prior.
        kb += ["(if (and (etc_%s %.8f)) (%s))" % (
            n, get_prob(0.1), n,
        )]
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
    num_atoms,
    num_links,
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
    argparser.add_argument('-minn', '--minatoms',
                   type=int,
                   default=100,
                   help='Minimum number of atoms.')
    argparser.add_argument('-maxn', '--maxatoms',
                   type=int,
                   default=10000,
                   help='Maximum number of atoms.')
    argparser.add_argument('-mino', '--minobs',
                   type=int,
                   default=6,
                   help='Maximum number of observations.')
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
        num_atoms = random.randint(args.minatoms, args.maxatoms)
        num_links = random.randint(num_atoms, 100000)

        print >>sys.stderr, "Generating axioms..."
        print >>sys.stderr, "# atoms: %d, # links: %d" % (num_atoms, num_links)

        fn_kb, fn_obs = "data/synthetic/kb%d.lisp" % (1+i), "data/synthetic/obs%d.lisp" % (1+i)

        kb, obs = generate(args, num_atoms, num_links)

        print >>sys.stderr, "# obs: %d, # axioms: %d" % (len(obs), len(kb))

        with open(fn_kb, "w") as f:
            for r in kb:
                print >>f, r

        with open(fn_obs, "w") as f:
            print >>f, " ".join(["(%s)" % ob for ob in obs])

        os.system("python etcabductionpy -k %s -kc %s.mcdb" % (fn_kb, fn_kb))

if "__main__" == __name__:
    main()
