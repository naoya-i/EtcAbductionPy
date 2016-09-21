# etcetera_ilp.py
# Etcetera Abduction: Probability-ordered logical abduction for kb of definite clauses
# Andrew S. Gordon

import unify
import abduction
import bisect
import itertools

import gurobipy
import math
import collections
import time
import logging

def ilpsol(obs, kb, indexed_kb, maxdepth, n, verbose = False):
    res = []
    gm = gurobipy.Model("etcabduction")

    time_ilp_gen, time_ilp_sol = 0, 0

    hvars, xvars, cvars = {}, {}, {}
    etcliterals  = set([])

    def _sig(x):
        return "_".join([t for t in (x[:-1] if x[0].startswith("etc") else x)])

    def _conj2predsid(x):
        return ",".join([_sig(l) for l in x])

    #
    # add ILP variables.
    time_start = time.time()

    potential_conseq = list(abduction.comp_deduce_andor_assumptions(obs, indexed_kb, maxdepth))

    for literal, level, literal_conj, possible_expls in potential_conseq:
        signature = _sig(literal)

        # vars for hypothesis H.
        if signature.startswith("etc"):
            etcliterals |= set([(signature, literal[-1])])

            if not hvars.has_key(signature):
                hvars[signature] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="h_"+signature)

        # vars for logical consequences of H \cup B
        if not xvars.has_key(signature):
            xvars[signature] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="x_"+signature)

        # vars for conjunction.
        signature_conj = _conj2predsid(literal_conj)

        if not cvars.has_key(signature_conj):
            cvars[signature_conj] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="c_{%s}"%signature_conj)

    gm.update()

    #
    # add ILP constraints.
    l2conjs = collections.defaultdict(list)

    for literal, level, literal_conj, possible_expls in potential_conseq:
        signature = _sig(literal)

        l2conjs[signature] += [literal_conj]

        # constraint: conjunction is true iff all literals are concluded.
        # c_{l1 \land l2 \land ...}=1 <=> x_l1=1 \land x_l2=1 \land ...
        for conj in possible_expls:
            gm.addConstr(len(conj)*cvars[_conj2predsid(conj)] <= sum([xvars[_sig(l)] for l in conj]))
            gm.addConstr(sum([xvars[_sig(l)] for l in conj]) <= (len(conj)-1) + cvars[_conj2predsid(conj)])

        # encode condition of literal being concluded.
        if len(possible_expls) > 0:
            # constraint: p can be concluded iff at least one of its explanations is concluded.
            # x_p=1 <=> c_{Q_1}=1 \lor c_{Q_2}=1 or ...
            gm.addConstr(xvars[signature] <= sum([cvars[_conj2predsid(conj)] for conj in possible_expls]))
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= len(possible_expls)*xvars[signature])

            # constraint: explanations are mutually exclusive.
            gm.addConstr(sum([cvars[_conj2predsid(conj)] for conj in possible_expls]) <= 1)

        else:
            # constraint: p can be concluded iff it is assumed (for etc literals only).
            if signature.startswith("etc"):
                # x_p=1 <=> h_p=1
                gm.addConstr(xvars[signature] == hvars[signature])

            else:
                # x_p=0
                if literal not in obs:
                    gm.addConstr(xvars[signature] == 0)

        #

    # constraint: each consequent must come from rule.
    for sl, conjs in l2conjs.iteritems():
        gm.addConstr(xvars[sl] <= sum([cvars[_conj2predsid(conj)] for conj in conjs]))

    # constraint: observation must be concluded.
    # for all p \in O, x_p=1.
    gm.addConstr(sum([xvars[_sig(l)] for l in obs]) >= len(obs))

    # set ILP objective.
    gm.setObjective(sum([math.log(prob) * hvars[signature] for signature, prob in etcliterals]), gurobipy.GRB.MAXIMIZE)
    gm.update()

    time_ilp_gen = time.time() - time_start
    time_start   = time.time()

    gm.params.outputFlag = 0

    if verbose:
        gm.params.outputFlag = 1
        gm.write("test.lp")

    # get solutions.
    sols = []

    for i in xrange(n):

        # find the best assignment.
        gm.optimize()

        #
        # add new solution (if any).
        if gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
            if verbose:
                gm.computeIIS()

                for c in gm.getConstrs():
                    if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                        print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

            break

        sols += [[
            [signature, prob]
            for signature, prob in etcliterals
            if hvars[signature].getAttr(gurobipy.GRB.Attr.X) == 1.0
            ]]

        # deny the current sol.
        gm.addConstr(sum([
            hvars[signature]
            if hvars[signature].getAttr(gurobipy.GRB.Attr.X) == 1.0 else
            1.0 - hvars[signature]
            for signature, prob in etcliterals
            ]) <= len(etcliterals)-1)

    time_ilp_sol = time.time() - time_start

    logging.info("ILP-Gen: %s, ILP-Opt: %s" % (time_ilp_gen, time_ilp_sol))

    return sols
