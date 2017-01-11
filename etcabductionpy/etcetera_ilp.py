# etcetera_ilp.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
#  -- ILP plugin
# Naoya Inoue

import unify
import abduction
import bisect
import itertools
import parse
import formula
import knowledgebase
import ilp_wmaxsat

import gurobipy
import math
import time
import logging
import os
import sys

import collections

class stopwatch_t:
    def __init__(self):
        self.records = {}

    def start(self):
        self.time    = time.time()

    def stop(self, name):
        self.records[name] = time.time() - self.time

def nbest_ilp(obs, kb, args):
    sw = stopwatch_t()

    sw.start()

    # Standardize the observations.
    obs = unify.standardize(obs)

    if not args.ilp_no_relreason:
        logging.info("Relevant reasoning...")
        rkb, facts, nonab = knowledgebase.obtain_relevant_kb(kb, obs, args.depth)

    else:
        logging.info("Loading axioms...")
        rkb, facts, nonab = kb.get_axioms(), kb.get_facts(), []

    sw.stop("relrea")

    sw.start()
    if not args.ilp_use_cnf:
        logging.info("Clark completion on %d axioms..." % len(rkb))
        f = formula.clark_completion_t(rkb)

    else:
        logging.info("Clark completion (CNF mode) on %d axioms..." % len(rkb))
        f = formula.clark_completion_cnf_t(rkb)


    f.add_facts(facts)
    f.add_observations(obs)
    f.add_nonabs(nonab)
    f.scan_unifiables()
    sw.stop("comp")

    # create ilp problem.
    logging.info("Converting the WMSAT into ILP...")

    sw.start()
    wms = ilp_wmaxsat.ilp_wmaxsat_solver_t()

    # set options.
    wms.use_eqtransitivity = not args.ilp_no_transitivity
    wms.use_lazyeqtrans    = args.ilp_lazy_transitivity

    if not args.ilp_verbose:
        wms.gm.params.outputFlag = 0

    else:
        wms.gm.params.outputFlag = 1

    wms.encode(f)
    sw.stop("ilpconv")

    # output statistics.
    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d" % (len(wms.gm.getVars()), ))
    logging.info("  ILP constraints: %d" % (len(wms.gm.getConstrs()), ))

    if args.ilp_verbose:
        wms.write_lp("test.lp")

    #
    # get k-best solutions.
    logging.info("Solving the WMSAT...")
    sw.start()

    sols = []

    for sol in wms.find_solutions(args.nbest):
        if sol == None:
            logging.info("  No more solution.")

            if args.ilp_verbose:
                if wms.gm.getAttr(gurobipy.GRB.Attr.Status) == gurobipy.GRB.INFEASIBLE:
                    wms.print_iis()

            break

        logging.info("  Got %d-best solution!" % (1+len(sols)))

        # sounds good.
        sols += [[l for l in sol.literals if args.ilp_show_nonetc or parse.is_etc(l)]]

        if args.ilp_verbose:
            wms.print_abduciblevars()

    sw.stop("ilpsol")

    logging.info("  Inference time: [relrea] %.2f, [comp] %.2f, [gen-ilp] %.2f, [opt] %.2f" % (
        sw.records["relrea"],
        sw.records["comp"],
        sw.records["ilpconv"],
        sw.records["ilpsol"],
        ))

    return sols
