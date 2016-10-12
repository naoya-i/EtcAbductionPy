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

import collections

class stopwatch_t:
    def __init__(self):
        self.records = {}

    def start(self):
        self.time    = time.time()

    def stop(self, name):
        self.records[name] = time.time() - self.time

def nbest_ilp(obs, kb, indexed_kb, maxdepth, n, verbose = False):

    sw = stopwatch_t()

    logging.info("Generating an explanation formula...")

    sw.start()
    f = formula.explanation_formula_t(obs, indexed_kb, maxdepth)
    sw.stop("gen_expf")

    # create ilp problem.
    logging.info("Converting the WMSAT into ILP...")

    sw.start()
    wms = ilp_wmaxsat.ilp_wmaxsat_solver_t()
    wms.encode(f)
    sw.stop("ilpconv")

    # output statistics.
    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d" % (len(wms.gm.getVars()), ))
    logging.info("  ILP constraints: %d" % (len(wms.gm.getConstrs()), ))

    if not verbose:
        wms.gm.params.outputFlag = 0

    else:
        wms.gm.params.outputFlag = 1
        wms.write_lp("test.lp")

    #
    # get k-best solutions.
    logging.info("Solving the WMSAT...")
    sw.start()

    sols = []

    for sol in wms.find_solutions(n):
        if len(sol) == 0:
            logging.info("  No more solution.")

            if verbose and wms.gm.getAttr(gurobipy.GRB.Attr.Status) == gurobipy.GRB.INFEASIBLE:
                # output IIS for debug.
                wms.gm.computeIIS()

                for c in wms.gm.getConstrs():
                    if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                        print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

            break

        # sounds good.
        sols += [sol]

        logging.info("  Got %d-best solution!" % (len(sols)))

    sw.stop("ilpsol")

    logging.info("  Inference time: [gen-expf] %.2f, [gen-ilp] %.2f, [opt] %.2f" % (
        sw.records["gen_expf"],
        sw.records["ilpconv"],
        sw.records["ilpsol"],
        ))

    return sols
