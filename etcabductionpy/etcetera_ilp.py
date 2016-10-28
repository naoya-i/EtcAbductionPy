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

def nbest_ilp(obs, kb, maxdepth, n, verbose = False):

    sw = stopwatch_t()

    logging.info("Relevant reasoning...")

    sw.start()
    obs = unify.standardize(obs)
    rkb = formula.obtain_relevant_kb(kb, obs, maxdepth)
    f = formula.clark_completion_t(rkb)
    f.add_observations(obs)
    f.scan_unifiables()
    sw.stop("gen_expf")

    for r in rkb:
        print r

    # create ilp problem.
    logging.info("Converting the WMSAT into ILP...")

    sw.start()
    wms = ilp_wmaxsat.ilp_wmaxsat_solver_t()

    if not verbose:
        wms.gm.params.outputFlag = 0

    else:
        wms.gm.params.outputFlag = 1

    wms.encode(f)
    sw.stop("ilpconv")

    # output statistics.
    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d" % (len(wms.gm.getVars()), ))
    logging.info("  ILP constraints: %d" % (len(wms.gm.getConstrs()), ))

    if verbose:
        wms.write_lp("test.lp")

    #
    # get k-best solutions.
    logging.info("Solving the WMSAT...")
    sw.start()

    sols = []

    for sol in wms.find_solutions(n):
        if len(sol) == 0:
            logging.info("  No more solution.")

            if verbose:
                if wms.gm.getAttr(gurobipy.GRB.Attr.Status) == gurobipy.GRB.INFEASIBLE:
                    wms.print_iis()

            break

        logging.info("  Got %d-best solution!" % (1+len(sols)))

        # sounds good.
        sols += [sol]

        if verbose:
            wms.print_costvars()


    sw.stop("ilpsol")

    logging.info("  Inference time: [gen-expf] %.2f, [gen-ilp] %.2f, [opt] %.2f" % (
        sw.records["gen_expf"],
        sw.records["ilpconv"],
        sw.records["ilpsol"],
        ))

    return sols
