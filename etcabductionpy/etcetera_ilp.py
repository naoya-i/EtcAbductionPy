# etcetera_ilp.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
#  -- ILP plugin
# Naoya Inoue

import unify
import abduction
import bisect
import itertools
import parse
import explanation_formula
import ilp_wmaxsat

import gurobipy
import math
import time
import logging
import os

def nbest_ilp(obs, kb, indexed_kb, maxdepth, n, verbose = False):

    time_ilp_gen, time_ilp_sol = 0, 0
    time_start = time.time()

    logging.info("Generating an explanation formula...")
    expf = explanation_formula.explanation_formula_t(obs, indexed_kb, maxdepth)

    # create ilp problem.
    logging.info("Converting the WMSAT into ILP...")
    wms = ilp_wmaxsat.ilp_wmaxsat_solver_t()
    wms.encode(expf)

    # output statistics.
    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d" % (len(wms.gm.getVars()), ))
    logging.info("  ILP constraints: %d" % (len(wms.gm.getConstrs()), ))

    time_ilp_gen = time.time() - time_start

    if not verbose:
        wms.gm.params.outputFlag = 0

    else:
        wms.gm.params.outputFlag = 1
        wms.write_lp("test.lp")

    #
    # get k-best solutions.
    logging.info("Solving the WMSAT...")

    time_start = time.time()
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

    time_ilp_sol = time.time() - time_start

    logging.info("  Inference time: [gen] %.2f, [opt] %.2f" % (time_ilp_gen, time_ilp_sol))

    return sols
