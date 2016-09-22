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

def _sig(i, x, setty=False):
    ls = "_".join([t for t in (x[:-1] if x[0].startswith("etc") else x)])

    if setty:
        return ls
    else:
        return "%s@%s" % (ls, i)

def _conj2predsid(x):
    return ",".join([_sig(l_id, l) for l_id, l in x])

def ilpsol(obs, kb, indexed_kb, maxdepth, n, verbose = False):
    res = []
    gm = gurobipy.Model("etcabduction")

    time_ilp_gen, time_ilp_sol = 0, 0

    hvars, xvars, cvars = {}, {}, {}
    etcliterals         = set([])

    #
    # add ILP variables.
    logging.info("Generating ILP problem...")

    time_start = time.time()

    potential_conseq = list(abduction.comp_deduce_andor_assumptions(obs, indexed_kb, maxdepth))

    for literal_id, literal, level, literal_conj, possible_expls in potential_conseq:
        signature     = _sig(literal_id, literal)
        signature_set = _sig(literal_id, literal, setty=True)

        # vars for hypothesis H.
        if signature.startswith("etc"):
            etcliterals |= set([(signature_set, literal[-1])])

            if not hvars.has_key(signature_set):
                hvars[signature_set] = gm.addVar(vtype=gurobipy.GRB.BINARY, name="h_"+signature_set)

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
    conjcons = {}
    etc2etcs = collections.defaultdict(list)

    for literal_id, literal, level, literal_conj, possible_expls in potential_conseq:
        signature = _sig(literal_id, literal)
        signature_set = _sig(literal_id, literal, setty=True)
        signature_lconj = _conj2predsid(literal_conj)

        # constraint: conjunction is true iff all literals are concluded.
        # c_{l1 \land l2 \land ...}=1 <=> x_l1=1 \land x_l2=1 \land ...
        if not conjcons.has_key(signature_lconj):
            conjcons[signature_lconj] = 1

            gm.addConstr(len(literal_conj)*cvars[signature_lconj] <= sum([xvars[_sig(l_id, l)] for l_id, l in literal_conj]))
            gm.addConstr(sum([xvars[_sig(l_id, l)] for l_id, l in literal_conj]) <= (len(literal_conj)-1) + cvars[signature_lconj])

            # constraint: each consequent must coincide with the conjunction.
            for l_id, l in literal_conj:
                gm.addConstr(xvars[_sig(l_id, l)] <= cvars[signature_lconj])

            # constraint: to conclude a explanatory conjunction, I must be concluded.
            for conj in possible_expls:
                gm.addConstr(cvars[_conj2predsid(conj)] <= cvars[signature_lconj])

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
                etc2etcs[signature_set] += [signature]

            else:
                # x_p=0
                if level > 0:
                    # this literal cannot be concluded.
                    gm.addConstr(xvars[signature] == 0)

        # constraint: observation must be concluded.
        # for all p \in O, x_p=1.
        if level == 0:
            gm.addConstr(xvars[_sig(literal_id, literal)] == 1)

    # constraint: etc consequents are true iff it is hypothesized
    # x_etc1@1=1 \lor x_etc1@2=2 \lor ... \lor x_etc1@n=1 <=> h_etc1=1
    for etc, etcs in etc2etcs.iteritems():
        gm.addConstr(hvars[etc] <= sum([xvars[s] for s in etcs]))
        gm.addConstr(sum([xvars[s] for s in etcs]) <= len(etcs)*hvars[etc])

    # set ILP objective.
    gm.setObjective(sum([math.log(prob) * hvars[signature] for signature, prob in etcliterals]), gurobipy.GRB.MAXIMIZE)
    gm.update()

    logging.info("[ILP problem]")
    logging.info("  ILP variables: %d ([h] %d, [x] %d, [c] %d)" % (len(gm.getVars()), len(hvars), len(xvars), len(cvars)))
    logging.info("  ILP constraints: %d" % len(gm.getConstrs()))

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

        logging.info("  Got %d-best solution!" % (1+i))

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
        if 1+i < n:
            gm.addConstr(sum([
                hvars[signature]
                if hvars[signature].getAttr(gurobipy.GRB.Attr.X) == 1.0 else
                1.0 - hvars[signature]
                for signature, prob in etcliterals
                ]) <= len(etcliterals)-1)

    time_ilp_sol = time.time() - time_start

    logging.info("  Inference time: [gen] %.2f, [opt] %.2f" % (time_ilp_gen, time_ilp_sol))

    return sols
