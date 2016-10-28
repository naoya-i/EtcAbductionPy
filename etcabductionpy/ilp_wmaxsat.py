# ilp_wmaxsat.py
#  Integer Linear Programming implementation of Weighted Max Sat Solver.
# Naoya Inoue

import parse
import unify
import etcetera

import itertools
import sys

import gurobipy
import os
import logging
import math
import collections
import networkx as nx

def is_opr(x):
    return x == "^" or x == "v" or x == "<->"

class ilp_wmaxsat_solver_t:
    def __init__(self):
        self.gm = gurobipy.Model("ilp_wmaxsat_solver")
        self.gm.params.LazyConstraints = 1

        self.vars = {}
        self.lit_vars = {}
        self.eqlit_vars = {}
        self.cost_vars = {}
        self.uni_vars = collections.defaultdict(dict)

        self.eq_dep = collections.defaultdict(list)
        self.sol_related_eqs = {}
        self.trans_eq_cache = {}

        self.formula = None

    def encode(self, f, initial_h = []):
        '''Encode the WMAXSAT problem of f as an ILP problem.'''
        self.formula = f

        logging.info("  Variables...")
        self._encode_variables(f)

        logging.info("  Constraints...")
        self._encode_constraints(f)

        logging.info("  Objective...")
        self._encode_objective(f, initial_h)

    def write_lp(self, out):
        '''Write the encoded problem into a file.'''
        self.gm.write(out)

    def find_solutions(self, n):
        '''find n-best solutions. '''
        sols = set()

        while len(sols) < n:

            # find the best assignment.
            self._init_inference()

            self.gm.optimize(lambda model, where: self._cb_gurobi(model, where))

            #
            # add new solution (if any).
            if self.gm.getAttr(gurobipy.GRB.Attr.SolCount) == 0:
                yield []
                break

            sol = self._reduce_sol(self._get_currentsol())

            # assertion.
            if not self._check_sum(sol):
                raise Exception("Fatal error!")

            if frozenset(sol) in sols:
                logging.info("  ...")

            else:
                sols.add(frozenset(sol))
                yield sol

            # deny the current sol.
            if len(sols) < n:
                self.gm.addConstr(gurobipy.quicksum([
                    var
                    if var.getAttr(gurobipy.GRB.Attr.X) == 1.0 else
                    1.0 - var
                    for var in self.cost_vars.values()
                    ]) <= len(self.cost_vars)-1)
                self.gm.params.Cutoff = -gurobipy.GRB.INFINITY

    def print_iis(self):

        # output IIS for debug.
        wms.gm.computeIIS()

        for c in wms.gm.getConstrs():
            if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

    def print_costvars(self):
        for lit, var in self.cost_vars.iteritems():
            if var.getAttr(gurobipy.GRB.Attr.X) == 1.0:
                logging.info("Payment: %s" % repr(lit))

        for lit, var in self.eqlit_vars.iteritems():
            if var.getAttr(gurobipy.GRB.Attr.X) == 1.0:
                logging.info("Eq: %s" % repr(lit))

    def _init_inference(self):
        self.sol_related_eqs = {}
        self.trans_eq_cache = {}

    def _get_currentsol(self):
        return [
            k
            for k, var in self.lit_vars.iteritems()
            if var.getAttr(gurobipy.GRB.Attr.X) == 1.0
        ]

    def _reduce_sol(self, sol, reduce_eqs = True):

        # construct variable unification network.
        vargraph = nx.Graph()

        for l in sol:
            if l[0] == "=" and self.sol_related_eqs.has_key(l):
                vargraph.add_edge(l[1], l[2])

        # prepare "eq" literals and substitutor.
        theta = {}
        eqs   = []

        for cc in nx.connected_components(vargraph):
            uvars        = list(cc)
            new_var_name = uvars[0]
            eqs         += [tuple(["="] + uvars)]

            # find a better name.
            for t in uvars:
                if not unify.variablep(t):
                    new_var_name = t
                    break

            for t in uvars:
                if t != new_var_name:
                    theta[t] = new_var_name

        if not reduce_eqs: theta = {}
        else:              eqs   = []

        return parse.list2tuple(unify.skolemize(list(set([
                tuple(l)
                for l in unify.subst(theta, sol)
                if l[0] != "=" and parse.is_etc(l)
                ] + eqs))))

    def _check_sum(self, sol):
        p1, p2 = math.log(etcetera.jointProbability(sol)), self.gm.getAttr(gurobipy.GRB.Attr.ObjVal)

        if abs(p1-p2) >= 1e-6:
            logging.info("  FATAL ERROR: %f != %f" % (math.exp(p1), math.exp(p2)))
            return False

        return True

    def _create_var(self, node):
        if is_opr(node[1]):
            return self.gm.addVar(vtype=gurobipy.GRB.BINARY)

        if not self.lit_vars.has_key(node[1]):
            self.lit_vars[node[1]] = self.gm.addVar(vtype=gurobipy.GRB.BINARY)

            if node[1][0] == "=":
                self.eqlit_vars[node[1]] = self.lit_vars[node[1]]

        return self.lit_vars[node[1]]

    def _encode_variables(self, f):

        nonab = self.gm.addVar(vtype=gurobipy.GRB.BINARY, ub=0.0)

        # create varibles for equalities.
        for cc in nx.connected_components(f.unifiable_var_graph):
            for v1, v2 in itertools.combinations(cc, 2):
                v1, v2 = parse.varsort(v1, v2)

                # check unifiability
                if v1 != v2 and not unify.variablep(v1) and not unify.variablep(v2):
                    self.lit_vars[("=", v1, v2)] = nonab

                else:
                    self._create_var((-1, ("=", v1, v2)))

        # create unification variable.
        for arity, nodes in f.unifiables.iteritems():
            literals = set([n[1] for n in nodes])

            for l1 in literals:
                for l2 in literals:
                    self.uni_vars[l1][l2] = self.gm.addVar(vtype=gurobipy.GRB.BINARY)

                    for i in xrange(arity[1] - 1):
                        v1, v2 = parse.varsort(l1[2+i], l2[2+i])
                        self.eq_dep[("=", v1, v2)] += [(l1, l2)]

        # create node variable.
        for node in f.nxg.nodes_iter():

            # if it is non abducible, ...
            is_etc   = parse.is_etc(node[1])

            # create node variable.
            self.vars[node] = self._create_var(node)

            # create cost variable.
            if is_etc:
                if not self.cost_vars.has_key(node[1]):
                    self.cost_vars[node[1]] = self.gm.addVar(vtype=gurobipy.GRB.BINARY)

        self.gm.update()

    def _encode_constraints(self, f):

        conseq_minimizer = collections.defaultdict(list)

        # create and-or constraints.
        for node in f.nxg.nodes_iter():

            # root formula must be satisfied.
            if len(f.nxg.predecessors(node)) == 0:
                self.gm.addConstr(self.vars[node] == 1)

            if "^" == node[1]:
                self._encode_and(f, node)

                for child_node in f.nxg.successors(node):
                    conseq_minimizer[child_node[1]] += [self.vars[node]]

            elif "v" == node[1]:
                self._encode_or(f, node)

            elif "<->" == node[1]:
                self._encode_dimp(f, node)

        # for minimizing consequent.
        for lit, dependent_nodes in conseq_minimizer.iteritems():
            self.gm.addConstr(self.lit_vars[lit] <= gurobipy.quicksum(dependent_nodes))

        # for unification vars.
        for arity, nodes in f.unifiables.iteritems():
            literals = set([n[1] for n in nodes])

            for a1 in literals:
                for a2 in literals:
                    cvar = self.uni_vars[a1][a2]

                    if a1 == a2:
                        self.uni_vars[a1][a2] = self.lit_vars[a1]

                    else:
                        # if they are not unifiable, pretend like it is always satisfied.
                        if None == unify.unify(a1, a2):
                            self.gm.addConstr(cvar == 1)
                            continue

                        #
                        # y_p(x) <=> p(x) \land (p(y) \land y=x => \lnot y_p(y))
                        xvars = [1.0 - self.lit_vars[a2], 1.0 - self.cost_vars[a2]]

                        for i in xrange(arity[1]-1):
                            if a1[2+i] == a2[2+i]:
                                continue

                            v1, v2 = parse.varsort(a1[2+i], a2[2+i])
                            xvars += [1.0 - self.lit_vars[("=", v1, v2)]]

                        self.gm.addConstr(cvar <= gurobipy.quicksum(xvars))
                        self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*cvar)

        # constraints for cost variables.
        for lit, cvar in self.cost_vars.iteritems():
            ari = parse.arity(lit)

            if not f.unifiables.has_key(ari):
                self.gm.addConstr(cvar == self.lit_vars[lit])

            else:
                relatives = []

                for unilit in set([n[1] for n in f.unifiables[ari]]):
                    relatives += [self.uni_vars[lit][unilit]]

                self.gm.addGenConstrAnd(cvar, relatives)

        self.gm.update()

    def _encode_and(self, f, node):
        # c=1 <=> x1=1 \land x2=1 \land ... \land xn=1
        cvar, xvars = self.vars[node], [self.vars[x] for x in f.nxg.successors(node)]

        self.gm.addGenConstrAnd(cvar, xvars)

    def _encode_or(self, f, node):
        # dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1
        dvar, xvars = self.vars[node], [self.vars[x] for x in f.nxg.successors(node)]

        self.gm.addGenConstrOr(dvar, xvars)

        # to avoid redundant explanation
        if len(xvars) > 1:
            self.gm.addSOS(gurobipy.GRB.SOS_TYPE1, xvars)

    def _encode_dimp(self, f, node):
        # dvar <=> (xvar=1 <=> yvar=1)
        dvar       = self.vars[node]
        xvar, yvar = [self.vars[x] for x in f.nxg.successors(node)]

        self.gm.addConstr(1-xvar + 1-yvar +   dvar >= 1)
        self.gm.addConstr(  xvar +   yvar +   dvar >= 1)
        self.gm.addConstr(  xvar + 1-yvar + 1-dvar >= 1)
        self.gm.addConstr(1-xvar +   yvar + 1-dvar >= 1)

    def _encode_transitivity(self, x, y, z, lazy=False):

        # caching.
        k = frozenset((x, y, z))

        if self.trans_eq_cache.has_key(k):
            return

        self.trans_eq_cache[k] = 1

        # add transitivity constraints.
        v1, v2 = parse.varsort(x, y)
        vvar12 = self.lit_vars[("=", v1, v2)]
        v1, v2 = parse.varsort(y, z)
        vvar23 = self.lit_vars[("=", v1, v2)]
        v1, v2 = parse.varsort(x, z)
        vvar13 = self.lit_vars[("=", v1, v2)]

        _func = self.gm.cbLazy if lazy else \
                self.gm.addConstr

        _func(vvar12 + vvar23 - vvar13 - 1, gurobipy.GRB.LESS_EQUAL, 0)
        _func(vvar23 + vvar13 - vvar12 - 1, gurobipy.GRB.LESS_EQUAL, 0)
        _func(vvar13 + vvar12 - vvar23 - 1, gurobipy.GRB.LESS_EQUAL, 0)

    def _encode_transitivity_partially(self, nodes):
        """add transitivity constraint only related to @nodes"""
        for cc in nx.connected_components(
            self.formula.unifiable_var_graph.subgraph(nodes)
        ):
            for v1, v2, v3 in itertools.combinations(cc, 3):
                self._encode_transitivity(v1, v2, v3, lazy=True)

    def _encode_objective(self, f, initial_h = []):
        '''set ILP objective.'''

        # change to maximization.
        self.gm.setAttr(gurobipy.GRB.Attr.ModelSense, -1)

        # set coefficients
        for li, var in self.cost_vars.iteritems():
            var.setAttr(gurobipy.GRB.Attr.Obj, math.log(li[1]))

        # set initial solution
        for node in initial_h:
            self.vars[node].start = 1.0
            self.cost_vars[node[1]].start = 1.0

        self.gm.update()

    def _cb_gurobi(self, model, where):
        if where == gurobipy.GRB.Callback.MIPSOL:
            # set zeros to equalities not contained in current solution.

            self._cb_mipsol()

    def _cb_mipsol(self):
        """Gurobi callback."""
        self.sol_related_eqs = {}
        nodes = []
        sol   = self._cb_getsol()

        for l in self.eqlit_vars:
            for l1, l2 in self.eq_dep[l]:
                if sol[l1] == 1 and sol[l2] == 1:
                    nodes += [l[1], l[2]]
                    self.sol_related_eqs[l] = 1
                    break

        self._encode_transitivity_partially(nodes)

    def _cb_getsol(self):
        """returns dict object (lit: value) during callback."""
        literals = list(self.lit_vars)
        sol = self.gm.cbGetSolution([self.lit_vars[k] for k in literals])
        return dict([(literals[i], sol[i]) for i in xrange(len(literals))])
