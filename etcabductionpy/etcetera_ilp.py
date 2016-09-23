# etcetera_ilp.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
# Andrew S. Gordon

import unify
import abduction
import bisect
import itertools
import parse

import gurobipy
import math
import collections
import time
import logging

def _sig(x):
    return "_".join([t for t in (x[:-1] if x[0].startswith("etc") else x)])

def _conj2predsid(x):
    return ",".join([_sig(l) for l in x])

class andor_graph_t:
    def __init__(self, gm, indexed_kb, maxdepth):
        self.hvars     = {}
        self.ovars     = []
        self.disjcons  = []
        self.conjcons  = []
        self.gm        = gm
        self.ikb       = indexed_kb
        self.maxdepth  = maxdepth
        self.etcs      = []
        self.non_assumables = []

    def encode_variables(self, obs):
        '''create ILP variables'''
        for ob in obs:
            self.ovars += [self._recursively_create_vars(ob, 0)]

        self.gm.update()

    def _recursively_create_vars(self, literal, level):

        predicate = literal[0]

        if level < self.maxdepth and predicate in self.ikb:
            disj = []

            for rule in self.ikb[predicate]:
                theta = unify.unify(literal, parse.consequent(rule))

                if theta == None:
                    continue

                new_assumptions = unify.standardize(unify.subst(theta, parse.antecedent(rule)))

                conj = []

                for assumption in new_assumptions:
                    conj += [self._recursively_create_vars(assumption, level+1)]

                if None in conj:
                    self.non_assumables += [x for x in conj if x != None]
                    continue

                if len(conj) == 1:
                    disj += [conj[0]]
                    continue

                # there are several literals in the conjunction.
                cvar = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="c_{%s}" % _conj2predsid(new_assumptions))
                conj = [cvar] + conj
                self.conjcons += [conj]

                disj += [cvar]

            if len(disj) == 1:
                return disj[0]

            # there are several conjunctions in the disjunction.
            dvar = self.gm.addVar(vtype=gurobipy.GRB.BINARY)
            disj = [dvar] + disj
            self.disjcons += [disj]

            return dvar

        # this literal is going to be assumed.
        if not predicate.startswith("etc"):
            return None

        if not self.hvars.has_key(_sig(literal)):
            self.hvars[_sig(literal)] = [
                self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="h_%s" % _sig(literal))
                ]

        xvar = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="x_%s" % _sig(literal))
        self.hvars[_sig(literal)] += [xvar]

        self.etcs += [tuple(literal)]

        return xvar

    def encode_constraints(self):
        '''encode ovars/cvars/dvars/xvars constraints.'''
        for disj in self.disjcons:
            # dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1
            dvar, disj = disj[0], disj[1:]

            if len(disj) == 0:
                dvar.setAttr(gurobipy.GRB.Attr.UB, 0)
                continue

            self.gm.addConstr(dvar <= sum(disj))
            self.gm.addConstr(sum(disj) <= len(disj)*dvar)

            # explanations are mutually exclusive.
            if len(disj) > 1:
                self.gm.addSOS(gurobipy.GRB.SOS_TYPE1, disj)

        for conj in self.conjcons:
            # cvar=1 <=> h1=1 \land h2=1 \land ... \land hn=1
            cvar, conj = conj[0], conj[1:]

            self.gm.addConstr(len(conj)*cvar <= sum(conj))
            self.gm.addConstr(sum(conj) - (len(conj)-1) <= cvar)

            # for minimality (in terms of ...).
            for xvar in conj:
                self.gm.addConstr(xvar <= cvar)

        # for non-assumables
        for hvar in self.non_assumables:
            # h=1
            hvar.setAttr(gurobipy.GRB.Attr.UB, 0)

        # for observables.
        for dvar in self.ovars:
            # d=1
            dvar.setAttr(gurobipy.GRB.Attr.LB, 1)

        # for xvars.
        for ls, xvars in self.hvars.iteritems():
            hvar, xvars = xvars[0], xvars[1:]

            self.gm.addConstr(hvar <= sum(xvars))
            self.gm.addConstr(sum(xvars) <= len(xvars)*hvar)

        self.gm.update()

    def set_objective(self):
        '''set ILP objective.'''
        self.gm.setObjective(sum([math.log(l[-1]) * self.hvars[_sig(l)][0] for l in set(self.etcs)]), gurobipy.GRB.MAXIMIZE)

        self.gm.update()

def ilpsol(obs, kb, indexed_kb, maxdepth, n, verbose = False):

    gm = gurobipy.Model("etcabduction")

    time_ilp_gen, time_ilp_sol = 0, 0

    logging.info("Generating ILP problem...")
    time_start = time.time()

    # enumerate all possible etcs.
    g = andor_graph_t(gm, indexed_kb, maxdepth)
    g.encode_variables(obs)
    g.encode_constraints()
    g.set_objective()

    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d" % (len(gm.getVars()), ))
    logging.info("  ILP constraints: %d" % (len(gm.getConstrs()), ))

    time_ilp_gen = time.time() - time_start

    if not verbose:
        gm.params.outputFlag = 0

    else:
        gm.params.outputFlag = 1
        gm.write("test.lp")

    #
    # get k-best solutions.
    time_start = time.time()
    sols = []

    for i in xrange(n):

        # find the best assignment.
        gm.optimize()

        #
        # add new solution (if any).
        if gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
            logging.info("  No more solution.")

            if verbose:
                gm.computeIIS()

                for c in gm.getConstrs():
                    if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                        print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

            break

        logging.info("  Got %d-best solution!" % (1+i))

        sols += [[
            [l[0], l[-1]]
            for l in set(g.etcs)
            if g.hvars[_sig(l)][0].getAttr(gurobipy.GRB.Attr.X) == 1.0
            ]]

        # deny the current sol.
        if 1+i < n:
            gm.addConstr(sum([
                g.hvars[_sig(l)][0]
                if g.hvars[_sig(l)][0].getAttr(gurobipy.GRB.Attr.X) == 1.0 else
                1.0 - g.hvars[_sig(l)][0]
                for l in set(g.etcs)
                ]) <= len(set(g.etcs))-1)

    time_ilp_sol = time.time() - time_start

    logging.info("  Inference time: [gen] %.2f, [opt] %.2f" % (time_ilp_gen, time_ilp_sol))

    return sols
