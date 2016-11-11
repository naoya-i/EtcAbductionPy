# ilp_wmaxsat.py
#  Integer Linear Programming implementation of Weighted Max Sat Solver.
# Naoya Inoue

import parse
import unify
import etcetera

import itertools
import sys

import formula
import gurobipy
import os
import logging
import math
import collections
import networkx as nx

class ilp_wmaxsat_solver_t:
    def __init__(self):
        self.gm = gurobipy.Model("ilp_wmaxsat_solver")
        #self.gm.params.LazyConstraints = 1

        self.vars = {}
        self.lit_vars = {}
        self.eqlit_vars = {}
        self.cost_vars = {}
        self.uni_vars = collections.defaultdict(dict)

        self.eq_dep = collections.defaultdict(list)
        self.sol_related_eqs = {}
        self.sol_related_vars = set()
        self.trans_eq_cache = {}

        self.c0var, self.c1var = None, None

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

    def find_solutions(self, n, denial = 2):
        '''find n-best solutions. '''
        sols = []

        while len(sols) < n:

            # find the best assignment.
            self._init_inference()

            self.gm.reset()
            self.gm.optimize(lambda model, where: self._cb_gurobi(model, where))

            #
            # add new solution (if any).
            if self.gm.SolCount == 0:
                yield None
                break

            if self.gm.Status != gurobipy.GRB.Status.OPTIMAL:
                continue

            sol = solution_t(self)

            # assertion.
            if not sol.check_sum():
                raise Exception("Fatal error!")

            sols += [sol.literals]
            yield sol

            # deny the current sol.
            if len(sols) < n:
                if denial == 1:
                    self.gm.addConstr(gurobipy.quicksum([
                        var
                        if var.X > 0.5 else
                        1.0 - var
                        for var in self.lit_vars.values()
                        ]) <= len(self.lit_vars)-1)

                else:
                    sig = sol.get_signature()

                    self.gm.addConstr(gurobipy.quicksum([
                        self.lit_vars[l]
                        if self.lit_vars[l].X > 0.5 else
                        1.0 - self.lit_vars[l]
                        for l in sig
                        ]) <= len(sig)-1)

    def print_iis(self):

        # output IIS for debug.
        self.gm.computeIIS()

        for c in self.gm.getConstrs():
            if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

    def print_costvars(self):
        for lit, var in self.lit_vars.iteritems():
            if var.X > 0.5:
                logging.info("Literal: %s" % repr(lit))

        for lit, var in self.cost_vars.iteritems():
            if var.X > 0.5:
                logging.info("Payment: %s" % repr(lit))

        for lit, var in self.eqlit_vars.iteritems():
            if var.X > 0.5:
                logging.info("Eq: %s" % repr(lit))

    def _init_inference(self):
        self.sol_related_eqs = {}
        self.trans_eq_cache = {}

    def _create_var(self, f, node):
        if formula.is_opr(node[1]):
            return self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="%s%d" % (node[1], node[0]))

        l = parse.atom(node[1])

        if not self.lit_vars.has_key(l):
            self.lit_vars[l] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name=repr(l))

            if l[0] == "=":
                self.eqlit_vars[l] = self.lit_vars[l]

        return self.lit_vars[l]

    def _encode_variables(self, f):

        self.c0var = self.gm.addVar(vtype=gurobipy.GRB.BINARY, lb=0.0, ub=0.0)
        self.c1var = self.gm.addVar(vtype=gurobipy.GRB.BINARY, lb=1.0, ub=1.0)

        # create varibles for equalities.
        for cc in nx.connected_components(f.unifiable_var_graph):
            for v1, v2 in itertools.combinations(cc, 2):
                v1, v2 = parse.varsort(v1, v2)

                # check unifiability
                if not unify.variablep(v1) and not unify.variablep(v2):
                    self.lit_vars[("=", v1, v2)] = self.c0var

                else:
                    self._create_var(f, (-1, ("=", v1, v2)))

        # create unification variable.
        for arity, nodes in f.unifiables.iteritems():
            literals = set([n[1] for n in nodes])

            for l1 in literals:
                for l2 in literals:
                    if unify.unify(l1, l2) == None:
                        self.uni_vars[l1][l2] = self.c1var

                    else:
                        self.uni_vars[l1][l2] = self.gm.addVar(vtype=gurobipy.GRB.BINARY)

                        for i in xrange(arity[1] - 1):
                            v1, v2 = parse.varsort(l1[2+i], l2[2+i])
                            self.eq_dep[("=", v1, v2)] += [(l1, l2)]

        # create node variable.
        for node in f.nxg.nodes_iter():

            # create node variable.
            self.vars[node] = self._create_var(f, node)

            # create cost variable (for etc literals).
            if parse.is_etc(node[1]):
                if not self.cost_vars.has_key(node[1]):
                    self.cost_vars[node[1]] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="y_{%s}" % repr(node[1]))

        self.gm.update()

    def _encode_constraints(self, f):

        conseq_minimizer = collections.defaultdict(list)

        # for logical operators.
        for node in f.nxg.nodes_iter():

            if len(f.nxg.predecessors(node)) == 0:
                self.gm.addConstr(self.vars[node] == 1)

            if "^" == node[1]:
                self._encode_and(f, node)

                for child_node in f.nxg.successors(node):
                    if formula.is_opr(child_node[1]):
                        continue

                    conseq_minimizer[child_node[1]] += [self.vars[node]]

            elif "v" == node[1]:
                self._encode_or(f, node)

            elif "|" == node[1]:
                self._encode_xor(f, node)

            elif "<->" == node[1]:
                self._encode_dimp(f, node)

        # for consequent minimization.
        self._encode_conseqmin(conseq_minimizer)

        # for unification vars.
        self._encode_univars(f)

        # for cost variables.
        self._encode_costvars(f)

        for cc in nx.connected_components(f.unifiable_var_graph):
            cc = list(cc)
            const, var = [], []

            for v in cc:
                if not unify.variablep(v):
                    const += [v]
                else:
                    var   += [v]

            # for v1, v2, v3 in itertools.combinations(cc, 3):
            #     self._encode_transitivity(v1, v2, v3, lazy=False)

            for v in var:
                xvars = []

                for c in const:
                    v1, v2 = parse.varsort(v, c)
                    xvars += [self.lit_vars[("=", v1, v2)]]

                self.gm.addConstr(gurobipy.quicksum(xvars)<= 1)

        self.gm.update()

    def _nvar(self, node):
        if formula.is_opr(node[1]):
            return self.vars[node]

        return self._lvar(node[1])

    def _lvar(self, lit):
        if parse.is_negated(lit):
            return 1.0 - self.lit_vars[parse.atom(lit)]

        return self.lit_vars[lit]

    def _encode_costvars(self, f):
        for lit, cvar in self.cost_vars.iteritems():
            ari = parse.arity(lit)

            if not f.unifiables.has_key(ari):
                self.gm.addConstr(cvar == self.lit_vars[lit])

            else:
                relatives = []

                for unilit in set([n[1] for n in f.unifiables[ari]]):
                    relatives += [self.uni_vars[lit][unilit]]

                self.gm.addGenConstrAnd(cvar, relatives)

    def _encode_univars(self, f):
        for arity, nodes in f.unifiables.iteritems():
            literals = set([n[1] for n in nodes])

            for a1 in literals:
                for a2 in literals:
                    # semantics: u_{a1,a2} = 1 if a2 is equivalent to a2 with unification.
                    cvar = self.uni_vars[a1][a2]

                    if a1 == a2:
                        self.uni_vars[a1][a2] = self.lit_vars[a1]
                        continue

                    if None == unify.unify(a1, a2):
                        continue

                    # y_p(x) <=> p(x) \land (p(y) \land y=x => \lnot y_p(y))
                    xvars = [1.0 - self.lit_vars[a2], 1.0 - self.cost_vars[a2]]

                    for i in xrange(arity[1]-1):
                        if a1[2+i] == a2[2+i]:
                            continue

                        v1, v2 = parse.varsort(a1[2+i], a2[2+i])
                        xvars += [1.0 - self.lit_vars[("=", v1, v2)]]

                    self.gm.addConstr(cvar <= gurobipy.quicksum(xvars))
                    self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*cvar)

    def _encode_conseqmin(self, conseq_minimizer):
        for lit, dependent_nodes in conseq_minimizer.iteritems():
            self.gm.addConstr(self._lvar(lit) <= gurobipy.quicksum(dependent_nodes))

    def _encode_and(self, f, node):
        # c=1 <=> x1=1 \land x2=1 \land ... \land xn=1
        cvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.successors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= len(xvars))

        else:
            self.gm.addConstr(len(xvars)*cvar <= gurobipy.quicksum(xvars), name="^")
            self.gm.addConstr(gurobipy.quicksum(xvars) - len(xvars) + 1 <= cvar, name="^")

    def _encode_or(self, f, node):
        # dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1
        dvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.successors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= 1)

        else:
            self.gm.addConstr(dvar <= gurobipy.quicksum(xvars), name="v")
            self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*dvar, name="v")

    def _encode_xor(self, f, node):
        # dvar=1 <=> c1=1 \lxor c2=1 \lxor ... \lxor cn=1
        dvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.successors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= 1)

        else:
            self.gm.addConstr(dvar <= gurobipy.quicksum(xvars), name="|")
            self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*dvar, name="|")

        # to avoid redundant explanation
        if len(xvars) > 1:
            self.gm.addConstr(gurobipy.quicksum(xvars) <= 1)

    def _encode_dimp(self, f, node):
        # dvar=1 <=> (xvar=1 <=> yvar=1)
        dvar       = self._nvar(node)
        xvar, yvar = [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.successors(node)) == 0:
            self.gm.addConstr(xvar <= yvar)
            self.gm.addConstr(yvar <= xvar)

        else:
            self.gm.addConstr(1-xvar + 1-yvar +   dvar >= 1, name="<=>")
            self.gm.addConstr(  xvar +   yvar +   dvar >= 1, name="<=>")
            self.gm.addConstr(  xvar + 1-yvar + 1-dvar >= 1, name="<=>")
            self.gm.addConstr(1-xvar +   yvar + 1-dvar >= 1, name="<=>")

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
            self._cb_mipsol()

    def _cb_mipsol(self):
        """Gurobi callback."""
        return

        self.sol_related_eqs = {}

        #nodes = []
        sol   = self._cb_getsol()
        varg  = nx.Graph()

        for l in self.eqlit_vars:
            if sol[l] == 1:
                varg.add_edge(l[1], l[2])

        for l in self.lit_vars:
            if l[0] == "=": continue

            for a in l[1:]:
                self.sol_related_vars.add(a)

        for l in self.eqlit_vars:
            for l1, l2 in self.eq_dep[l]:
                if sol[l1] == 1 and sol[l2] == 1:
                    self.sol_related_eqs[l] = 1
                    break
        return

        self._encode_transitivity_partially(nodes)

    def _cb_getsol(self):
        """returns dict object (lit: value) during callback."""
        literals = list(self.lit_vars)
        sol = self.gm.cbGetSolution([self.lit_vars[k] for k in literals])
        return dict([(literals[i], sol[i]) for i in xrange(len(literals))])

class solution_t:
    def __init__(self, solver):
        self.solver = solver
        self.raw = self._get_raw_sol()
        self.raw_literals = [tuple(l) for l in self.raw if l[0] != "="]

        # construct variable unification network.
        self.vargraph, self.relvars = self._get_var_unification_graph(self.raw)

        # prepare "eq" literals and substitutor.
        self.theta, self.unification = self._get_substitutor(self.vargraph, self.relvars)
        self.unification_pairwise = []

        for eqs in self.unification:
            for v1, v2 in itertools.combinations(eqs[1:], 2):
                v1, v2 = parse.varsort(v1, v2)
                self.unification_pairwise += [("=", v1, v2)]

        # apply the substitution.
        self.literals_etc, self.literals_nonetc = [], []

        for l in parse.list2tuple(
            unify.skolemize(
                sorted(set([
                    tuple(l)
                    for l in unify.subst(self.theta, self.raw)
                    if l[0] != "="
                ]))
            )
        ):
            if parse.is_etc(l):
                self.literals_etc += [l]

            else:
                self.literals_nonetc += [l]

        self.literals = self.literals_etc+self.literals_nonetc

    def check_sum(self):
        p1, p2, p3 = math.log(etcetera.jointProbability(self.literals)), sum([v.obj for v in self.solver.gm.getVars() if v.X > 0.5]), self.solver.gm.objVal

        if abs(p1-p2) >= 1e-6 or abs(p2-p3) >= 1e-6:
            print self.solver.gm.Status
            logging.info("  FATAL ERROR: %f, %f, %f" % (math.exp(p1), math.exp(p2), math.exp(p3)))
            logging.info(parse.display(self.raw))
            return False

        return True

    def get_signature(self):
        return frozenset([l for l in self.raw_literals if parse.is_etc(l)] + [eq for eq in self.unification_pairwise if eq[1] in self.relvars and eq[2] in self.relvars])

    def _get_raw_sol(self):
        return [
            k
            for k, var in self.solver.lit_vars.iteritems()
            if var.X > 0.5
        ]

    def _get_var_unification_graph(self, sol):
        dsol = collections.Counter([l for l in sol if l[0] != "="])
        relvars = set()
        vargraph = nx.Graph()

        for l in sol:
            if l[0] == "=":
                related = True

                # check if the condition is satisfied.
                if l in self.solver.eq_dep:
                    related = False

                    for l1, l2 in self.solver.eq_dep[l]:
                        if l1 in dsol and l2 in dsol:
                            related = True
                            break

                if related:
                    vargraph.add_edge(l[1], l[2])

            else:
                # add all the arguments to related vars.
                for a in l[1:]:
                    relvars.add(a)

        return vargraph, relvars

    def _get_substitutor(self, vargraph, relvars):
        theta = {}
        eqs   = []

        for cc in nx.connected_components(vargraph):
            uvars        = list(cc)
            new_var_name = uvars[0]
            eqs += [tuple(["="] + uvars)]

            if len(relvars & set(uvars)) == 0:
                continue

            # find a better name.
            for t in uvars:
                if not unify.variablep(t):
                    new_var_name = t
                    break

            for t in uvars:
                if t != new_var_name:
                    theta[t] = new_var_name

        return theta, eqs

if "__main__" == __name__:
    #
    # sample input:
    #  (or (x1) (x2)) (or (~x2) (x3) (~x4)) (or (~x1) (x4))
    f = formula.maxsat_t(parse.parse(sys.stdin.read()))
    f.visualize(sys.stdout)

    wms = ilp_wmaxsat_solver_t()
    wms.encode(f)
    wms.write_lp("test.lp")

    wms.gm.params.outputFlag = 0

    for sol in wms.find_solutions(10, denial=1):
        print sol
