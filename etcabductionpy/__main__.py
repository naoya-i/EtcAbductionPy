# etcabductionpy.__main__
# Etcetera Abduction in Python
# Andrew S. Gordon
# Spring 2016

from __future__ import print_function
import argparse
import sys

import unify
import parse
import etcetera
import abduction
import forward
import formula

import cPickle, pickle
import logging

argparser = argparse.ArgumentParser(description='Etcetera Abduction in Python')

argparser.add_argument('-i', '--infile',
                       nargs='?',
                       type=argparse.FileType('r'),
                       default=sys.stdin,
                       help='Input file of observed literals as lisp s-expressions, defaults to STDIN')

argparser.add_argument('-o', '--outfile',
                       nargs='?',
                       type=argparse.FileType('w'),
                       default=sys.stdout,
                       help='Output file, defaults to STDOUT')

argparser.add_argument('-k', '--kb',
                       nargs='?',
                       type=argparse.FileType('r'),
                       help='Knowledge base of definite clauses as lisp s-expressions')

argparser.add_argument('-km', '--kbmcdb',
                       help='mcdb-cached knowledge base of definite clauses as lisp s-expressions')

argparser.add_argument('-kc', '--kbcache',
                       help='Cache knowledge base.')

argparser.add_argument('-n', '--nbest',
                       type=int,
                       default=10,
                       help='Generate NBEST-best proofs, defaults to 10')

argparser.add_argument('-g', '--graph',
                       action='store_true',
                       help='Output graph of solution in .dot format')

argparser.add_argument('-s', '--solution',
                       type=int,
                       default=1,
                       help='Graph the SOLUTION-best solution, defaults to 1')

argparser.add_argument('-d', '--depth',
                       type=int,
                       default=5,
                       help='Backchain to depth DEPTH, defaults to 5')

argparser.add_argument('-a', '--all',
                       action='store_true',
                       help='Generate all solutions')

argparser.add_argument('-l', '--ilp',
                       action='store_true',
                       help='Use ILP solver to get solution(s)')

argparser.add_argument('-as', '--astar-search',
                       action='store_true',
                       help='Use A* search to get solution(s)')

argparser.add_argument('-asg','--astar-graph',
                       action='store_true',
                       help='Output graph of AO* solutions in .dot format')

argparser.add_argument('-lv','--ilp-verbose',
                       action='store_true',
                       help='Output ILP solver log')

argparser.add_argument('-expfg','--expf-graph',
                       action='store_true',
                       help='Output graph of explanation formula in .dot format')

argparser.add_argument('-f', '--forward',
                       action='store_true',
                       help='Forward chain from INFILE with KB')

args = argparser.parse_args()

logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)-5s:%(asctime)-15s: %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    )

# For kb caching.

if args.kbcache:
    logging.info("Loading knowledge base...")
    kblines = args.kb.readlines()
    kbtext = "".join(kblines)

    kbkb, kbfacts = parse.definite_clauses(parse.parse(kbtext))

    logging.info("Indexing...")

    import mcdb
    mk = mcdb.make(args.kbcache)

    for p, rules in abduction.index_by_consequent_predicate(kbkb, []).iteritems():
        mk.add(p, cPickle.dumps(rules))

    mk.add("__fact__", cPickle.dumps(kbfacts))
    mk.finish()

    sys.exit()

# Load files

inlines = args.infile.readlines()
intext = "".join(inlines)
kb, obs = parse.definite_clauses(parse.parse(intext))

logging.info("Loading knowledge base...")

if args.kb:
    kblines = args.kb.readlines()
    kbtext = "".join(kblines)
    kbkb, kbobs = parse.definite_clauses(parse.parse(kbtext))
    kb.extend(kbkb)
    indexed_kb = abduction.index_by_consequent_predicate(kbkb, [])

if args.kbmcdb:
    import knowledgebase
    indexed_kb = knowledgebase.mcdb_t(args.kbmcdb)
    logging.info("Knowledge base loaded.")

# Explanation formula
if args.expf_graph:
    # obs = unify.standardize(obs)
    # rkb, nonab = formula.obtain_relevant_kb(kb, obs, args.depth)
    # f = formula.clark_completion_t(rkb)
    # f.add_observations(obs)
    # f.visualize(sys.stdout)
    #
    # print("Nonabs: %s" % nonab, file=sys.stderr)

    import networkx as nx
    g = nx.DiGraph()
    c = 0

    for r in kb:

        c += 1
        dest = "^%d" % c

        if len(parse.antecedent(r)) == 1:
            dest = tuple(parse.consequent(r))

        for a in parse.antecedent(r):
            g.add_edge(tuple(a), dest)

        if len(parse.antecedent(r)) > 1:
            g.add_edge("^%d" % c, tuple(parse.consequent(r)))

    for node in g.nodes_iter():
        if len(g.successors(node)) > 1:
            g.node[node]["color"] = "red"
            g.node[node]["fontcolor"] = "red"

    if not nx.is_directed_acyclic_graph(g):
        print("Cycle detected.", file=sys.stderr)

    ag = nx.to_agraph(g)
    ag.layout()
    ag.draw(sys.stdout)

    sys.exit()

# Handle forward

if args.forward:
    entailed = forward.forward(obs, kb)
    if args.graph:
        print(forward.graph(obs, entailed), file=args.outfile)
    else:
        for e in entailed:
            print(parse.display(e[0]), file=args.outfile)
    sys.exit()

# Handle abduction
import time
time_start = time.time()

if args.all:
    solutions = etcetera.etcAbduction(obs, kb, indexed_kb, args.depth)
else:
    if args.ilp:
        import etcetera_ilp

        # import may take a while.
        time_start = time.time()
        solutions = etcetera_ilp.nbest_ilp(obs, indexed_kb, args.depth, args.nbest, args.ilp_verbose)

    elif args.astar_search:
        import etcetera_search

        time_start = time.time()
        solutions = etcetera_search.nbest_astar(obs, kb, indexed_kb, args.depth, args.nbest, args.astar_graph)

    else:
        solutions = etcetera.nbest(obs, kb, indexed_kb, args.depth, args.nbest)

logging.info(str(len(solutions)) + " solutions.")
logging.info("It took %.2f sec to find the solutions." % (time.time() - time_start))

if args.graph:
    solution = solutions[args.solution - 1]
    print(forward.graph(solution, forward.forward(solution, kb), targets=obs),
          file=args.outfile)
else:
    for solution in solutions:
        print("; prob=%s\n%s" % (etcetera.jointProbability(solution), parse.display(solution)), file=args.outfile)


# To do: enable skolemize as an option
