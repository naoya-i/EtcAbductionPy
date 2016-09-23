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

class ilp_based_abduction_t:
    def __init__(self, gm, indexed_kb, maxdepth):
        self.hvars     = {}

        self.obscons    = []
        self.disjcons   = []
        self.conjcons   = []
        self.nonasmcons = []

        self.gm        = gm
        self.ikb       = indexed_kb
        self.maxdepth  = maxdepth
        self.etcs      = []


    def encode_variables(self, obs):
        '''create ILP variables'''
        for ob in obs:
            self.obscons += [self._recursively_create_vars(ob, 0)]

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
                    self.nonasmcons += [x for x in conj if x != None]
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
            self.etcs += [literal]

        xvar = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="x_%s" % _sig(literal))
        self.hvars[_sig(literal)] += [xvar]

        return xvar

    def encode_constraints(self):
        '''encode obscons/cvars/dvars/xvars constraints.'''

        # represent disjunction
        for disj in self.disjcons:
            # dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1
            dvar, disj = disj[0], disj[1:]

            if len(disj) == 0:
                dvar.setAttr(gurobipy.GRB.Attr.UB, 0)
                continue

            self.gm.addConstr(sum(disj) == dvar)

            # the above is short for:
            '''
            self.gm.addConstr(dvar <= sum(disj))
            self.gm.addConstr(sum(disj) <= len(disj)*dvar)

            # explanations are mutually exclusive.
            if len(disj) > 1:
                self.gm.addSOS(gurobipy.GRB.SOS_TYPE1, disj)
            '''

        # represent conjunction
        for conj in self.conjcons:
            # c=1 => h1=1 \land h2=1 \land ... \land hn=1
            # h1=1 \lor h2=1 \lor ... \lor hn=1 => c=1
            cvar, conj = conj[0], conj[1:]

            self.gm.addConstr(len(conj)*cvar == sum(conj))

            # the above is short for:
            '''
            self.gm.addConstr(len(conj)*cvar <= sum(conj))

            # for minimality (in terms of ...).
            self.gm.addConstr(sum(conj) <= len(conj)*cvar)
            '''

        # constraint: non-assumables cannot be assumed.
        # h=0, forall h \in NA
        for hvar in self.nonasmcons:
            hvar.setAttr(gurobipy.GRB.Attr.UB, 0)

        # constraint: observation must be entailed.
        # d=1, forall d \in O
        for dvar in self.obscons:
            dvar.setAttr(gurobipy.GRB.Attr.LB, 1)

        # constraint: xvars <=> hvars
        for ls, xvars in self.hvars.iteritems():
            hvar, xvars = xvars[0], xvars[1:]

            # h=1 <=> x1=1 \lor x2=1 \lor ... \lor xn=1
            self.gm.addConstr(hvar <= sum(xvars))
            self.gm.addConstr(sum(xvars) <= len(xvars)*hvar)

        self.gm.update()

    def set_objective(self):
        '''set ILP objective.'''
        self.gm.setObjective(sum([math.log(l[-1]) * self.hvars[_sig(l)][0] for l in self.etcs]), gurobipy.GRB.MAXIMIZE)

        self.gm.update()

    def find_solutions(self, n):
        '''find n-best solutions. '''
        for i in xrange(n):

            # find the best assignment.
            self.gm.optimize()

            #
            # add new solution (if any).
            if self.gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
                yield []
                break

            yield [
                [l[0], l[-1]]
                for l in self.etcs
                if self.hvars[_sig(l)][0].getAttr(gurobipy.GRB.Attr.X) == 1.0
                ]

            # deny the current sol.
            if 1+i < n:
                self.gm.addConstr(sum([
                    self.hvars[_sig(l)][0]
                    if self.hvars[_sig(l)][0].getAttr(gurobipy.GRB.Attr.X) == 1.0 else
                    1.0 - self.hvars[_sig(l)][0]
                    for l in self.etcs
                    ]) <= len(self.etcs)-1)

def nbest_ilp(obs, kb, indexed_kb, maxdepth, n, verbose = False):

    gm = gurobipy.Model("etcabduction")

    time_ilp_gen, time_ilp_sol = 0, 0

    logging.info("Generating ILP problem...")
    time_start = time.time()

    # create ilp problem.
    iba = ilp_based_abduction_t(gm, indexed_kb, maxdepth)
    iba.encode_variables(obs)
    iba.encode_constraints()
    iba.set_objective()

    # output statistics.
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

    for sol in iba.find_solutions(n):
        if len(sol) == 0:
            logging.info("  No more solution.")

            if verbose:
                # output IIS for debug.
                gm.computeIIS()

                for c in gm.getConstrs():
                    if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                        print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

            break

        # sounds good.
        sols += [sol]

        logging.info("  Got %d-best solution!" % (len(sols)))

    time_ilp_sol = time.time() - time_start

    logging.info("  Inference time: [gen] %.2f, [opt] %.2f" % (time_ilp_gen, time_ilp_sol))

    return sols
