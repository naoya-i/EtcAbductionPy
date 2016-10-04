# etcabductionpy.__main__
# Etcetera Abduction in Python
# Andrew S. Gordon
# Spring 2016

from __future__ import print_function
import argparse
import sys

import parse
import etcetera
import abduction
import forward
import explanation_formula

import cPickle
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

argparser.add_argument('-kp', '--kbpickle',
                       nargs='?',
                       type=argparse.FileType('rb'),
                       help='Pickle knowledge base of definite clauses as lisp s-expressions')

argparser.add_argument('-kc', '--kbcache',
                       nargs='?',
                       type=argparse.FileType('wb'),
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

argparser.add_argument('-lv','--ilp-verbose',
                       action='store_true',
                       help='Output ILP solver log')

argparser.add_argument('-expfg','--expf-graph',
                       action='store_true',
                       help='Output explanation formula graph.')

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
    kblines = args.kb.readlines()
    kbtext = "".join(kblines)
    cPickle.dump(parse.parse(kbtext), args.kbcache)
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

if args.kbpickle:
    kbkb, kbobs = parse.definite_clauses(cPickle.load(args.kbpickle))
    kb.extend(kbkb)

    logging.info("Knowledge base loaded.")

indexed_kb = abduction.index_by_consequent_predicate(kb)
logging.info("Knowledge base indexed.")

# Explanation formula
if args.expf_graph:
    expf = explanation_formula.explanation_formula_t(obs, indexed_kb, args.depth)
    expf.visualize("/home/naoya-i/public_html/test.dot")

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
        solutions = etcetera_ilp.nbest_ilp(obs, kb, indexed_kb, args.depth, args.nbest, args.ilp_verbose)

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
