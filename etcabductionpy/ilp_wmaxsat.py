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

        self.node_vars = {}
        self.atom_vars = {}
        self.cost_vars = {}
        self.uni_vars = collections.defaultdict(dict)

        self.c0var, self.c1var = None, None

        self.formula = None

        # options.
        self.use_eqtransitivity = True
        self.use_lazyeqtrans = False

    def encode(self, f):
        '''encode the WMAXSAT problem of f as an ILP problem.'''
        self.formula = f

        logging.info("  Variables...")
        self._encode_variables(f)

        logging.info("  Constraints...")
        self._encode_constraints(f)

        logging.info("  Objective...")
        self._encode_objective(f)

    def write_lp(self, out):
        '''write the encoded problem into a file.'''
        self.gm.write(out)

    def find_solutions(self, n):
        '''find n-best solutions. '''
        sols = []

        while len(sols) < n:

            # find the best assignment.
            self.gm.reset()
            self.gm.optimize()

            #
            # add new solution (if any).
            if self.gm.SolCount == 0:
                yield None
                break

            sol = solution_t(self)

            # assertion.
            if not sol.check_sum():
                raise Exception("Fatal error!")

            sols += [sol.literals]
            yield sol

            # deny the current sol.
            if len(sols) < n:
                self.gm.addConstr(gurobipy.quicksum([
                    var
                    if var.X > 0.5 else
                    1.0 - var
                    for var in self.atom_vars.values()
                    ]) <= len(self.atom_vars)-1)

    def print_iis(self):
        '''output IIS for debug.'''
        self.gm.computeIIS()

        for c in self.gm.getConstrs():
            if c.getAttr(gurobipy.GRB.Attr.IISConstr) == 1:
                print("Infeasible: %s" % c.getAttr(gurobipy.GRB.Attr.ConstrName))

    def print_abduciblevars(self):
        '''print current solution.'''
        for atom, var in self.atom_vars.iteritems():
            if var.X > 0.5:
                logging.info("Atom: %s" % repr(atom))

        for atom, var in self.cost_vars.iteritems():
            if var.X > 0.5:
                logging.info("Payment: %s" % repr(atom))

    def _nvar(self, node):
        '''return node variable.'''
        if formula.is_opr(node[1]):
            return self.node_vars[node]

        if parse.is_negated(node[1]):
            return 1.0 - self.atom_vars[parse.atom(node[1])]

        return self.atom_vars[node[1]]

    def _encode_variables(self, f):
        '''encode ILP variables.'''
        self.c0var = self.gm.addVar(vtype=gurobipy.GRB.BINARY, lb=0.0, ub=0.0)
        self.c1var = self.gm.addVar(vtype=gurobipy.GRB.BINARY, lb=1.0, ub=1.0)

        # create node variable.
        for node in f.nxg.nodes_iter():

            # create node variable.
            if formula.is_opr(node[1]):
                # always fresh.
                self.node_vars[node] =  self.gm.addVar(vtype=gurobipy.GRB.BINARY, name="%s%d" % (node[1], node[0]))

            else:
                a = parse.atom(node[1])

                if not self.atom_vars.has_key(a):
                    self.atom_vars[a] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name=repr(a))

                self.node_vars[node] = self.atom_vars[a]

            # create cost variable (for etcetera literals).
            if parse.is_etc(node[1]):
                self.cost_vars[node[1]] = self.gm.addVar(vtype=gurobipy.GRB.BINARY)

        self._encode_unification_variables(f)

        self.gm.update()

    def _encode_constraints(self, f):
        '''encode ILP constraints.'''
        conseq_minimizer = collections.defaultdict(list)

        # for logical operators.
        for node in f.nxg.nodes_iter():

            if len(f.nxg.predecessors(node)) == 0:
                self.gm.addConstr(self.node_vars[node] == 1)

            if "^" == node[1]:
                self._encode_and(f, node)

                for child_node in f.nxg.successors(node):
                    if formula.is_opr(child_node[1]):
                        continue

                    conseq_minimizer[child_node[1]] += [self.node_vars[node]]

            elif "v" == node[1]:
                self._encode_or(f, node)

            elif "|" == node[1]:
                self._encode_xor(f, node)

            elif "<->" == node[1]:
                self._encode_dimp(f, node)

        # for consequent minimization.
        for lit, dependent_nodes in conseq_minimizer.iteritems():
            self.gm.addConstr(self._nvar((-1, lit)) <= gurobipy.quicksum(dependent_nodes))

        # for unification variables.
        for arity, nodes in f.unifiables.iteritems():
            literals = set([n[1] for n in nodes])

            for a1 in literals:
                for a2 in literals:

                    # do nothing for the same literal pair or non-unifiable pair,
                    if a1 == a2 or None == unify.unify(a1, a2):
                        continue

                    self._encode_univar(f, a1, a2)

        # for equality variables.
        if self.use_eqtransitivity:
            for cc in nx.connected_components(f.unifiable_var_graph):
                for v1, v2, v3 in itertools.combinations(cc, 3):
                    self._encode_eqtransitivity(v1, v2, v3, lazy=self.use_lazyeqtrans)

        # for cost vars.
        for atom in self.cost_vars:
            self._encode_costvar(f, atom)

        self.gm.update()

    def _encode_objective(self, f):
        '''set ILP objective.'''

        # change to maximization.
        self.gm.setAttr(gurobipy.GRB.Attr.ModelSense, -1)

        # set coefficients
        for atom, var in self.cost_vars.iteritems():
            var.setAttr(gurobipy.GRB.Attr.Obj, math.log(atom[1]))

        self.gm.update()

    '''variable encoder.'''
    def _encode_unification_variables(self, f):
        '''create ILP variables for unification.'''

        # create varibles for equalities.
        for cc in nx.connected_components(f.unifiable_var_graph):
            for v1, v2 in itertools.combinations(cc, 2):
                v1, v2 = parse.varsort(v1, v2)

                # check unifiability
                a = ("=", v1, v2)

                if not unify.variablep(v1) and not unify.variablep(v2):
                    self.atom_vars[a] = self.c0var

                else:
                    self.atom_vars[a] = self.gm.addVar(vtype=gurobipy.GRB.BINARY, name=repr(a))

        # create variables for unification.
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

    '''constraint encoder.'''
    def _encode_and(self, f, node):
        '''c=1 <=> x1=1 \land x2=1 \land ... \land xn=1'''
        cvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.predecessors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= len(xvars))

        else:
            self.gm.addConstr(len(xvars)*cvar <= gurobipy.quicksum(xvars), name="^")
            self.gm.addConstr(gurobipy.quicksum(xvars) - len(xvars) + 1 <= cvar, name="^")

    def _encode_or(self, f, node):
        '''dvar=1 <=> c1=1 \lor c2=1 \lor ... \lor cn=1'''
        dvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.predecessors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= 1)

        else:
            self.gm.addConstr(dvar <= gurobipy.quicksum(xvars), name="v")
            self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*dvar, name="v")

    def _encode_xor(self, f, node):
        '''dvar=1 <=> c1=1 \lxor c2=1 \lxor ... \lxor cn=1'''
        dvar, xvars = self._nvar(node), [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.predecessors(node)) == 0:
            self.gm.addConstr(gurobipy.quicksum(xvars) >= 1)

        else:
            self.gm.addConstr(dvar <= gurobipy.quicksum(xvars), name="|")
            self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*dvar, name="|")

        # to avoid redundant explanation
        if len(xvars) > 1:
            self.gm.addConstr(gurobipy.quicksum(xvars) <= 1)

    def _encode_dimp(self, f, node):
        '''dvar=1 <=> (xvar=1 <=> yvar=1)'''
        dvar       = self._nvar(node)
        xvar, yvar = [self._nvar(x) for x in f.nxg.successors(node)]

        if len(f.nxg.predecessors(node)) == 0:
            self.gm.addConstr(1 <= 1-xvar + yvar)
            self.gm.addConstr(1 <=   xvar + 1-yvar)

        else:
            # dvar=1 => xvar=0 v yvar=1
            # dvar=1 => xvar=1 v yvar=0
            # dvar=1 <= xvar=0 v yvar=1
            # dvar=1 <= xvar=1 v yvar=0
            self.gm.addConstr(dvar <= 1-xvar +   yvar, name="<=>")
            self.gm.addConstr(dvar <=   xvar + 1-yvar, name="<=>")
            self.gm.addConstr(1-xvar +   yvar <= 2*dvar, name="<=>")
            self.gm.addConstr(  xvar + 1-yvar <= 2*dvar, name="<=>")

    def _encode_costvar(self, f, atom):
        '''
        encode the contraint "y_p(x) <=> h_p(x) & u_{p(x), p(y)} & ...", where
        u_{p(x),p(y)} <=> h_{p(y)} & x=y => \lnot y_{p(y)} which is encoded in another function.
        '''
        cvar = self.cost_vars[atom]
        arity = parse.arity(atom)

        if parse.is_propositional(atom) or not f.unifiables.has_key(arity):
            self.gm.addConstr(cvar == self.atom_vars[atom])

        else:
            # y_p(x) <=> h_p(x) & u_{p(x), p(y)} & ...
            relatives = [self.atom_vars[atom]]

            for uniatom in set([n[1] for n in f.unifiables[arity]]):
                if atom != uniatom:
                    relatives += [self.uni_vars[atom][uniatom]]

            self.gm.addGenConstrAnd(cvar, relatives)

    def _encode_univar(self, f, a1, a2):
        # semantics: u_{a1,a2} = 1 iff a2 is not equivalent to a1 with unification,
        # nor a2 does not pay the cost.
        # formally: u_{p(x),p(y)} <=> (p(y) \land y=x => \lnot y_p(y))
        arity = parse.arity(a1)

        # u_{p(x),p(y)}
        uvar = self.uni_vars[a1][a2]

        # \lnot p(y)
        xvars = [1.0 - self.atom_vars[a2]]

        # \lnot y=x
        for i in xrange(arity[1]-1):
            if a1[2+i] == a2[2+i]:
                continue

            v1, v2 = parse.varsort(a1[2+i], a2[2+i])
            xvars += [1.0 - self.atom_vars[("=", v1, v2)]]

        # \lnot y_p(y)
        xvars += [1.0 - self.cost_vars[a2]]

        # create the constraint.
        self.gm.addConstr(uvar <= gurobipy.quicksum(xvars))
        self.gm.addConstr(gurobipy.quicksum(xvars) <= len(xvars)*uvar)

    def _encode_eqtransitivity(self, x, y, z, lazy=False):

        # add transitivity constraints.
        v1, v2 = parse.varsort(x, y)
        vvar12 = self.atom_vars[("=", v1, v2)]
        v1, v2 = parse.varsort(y, z)
        vvar23 = self.atom_vars[("=", v1, v2)]
        v1, v2 = parse.varsort(x, z)
        vvar13 = self.atom_vars[("=", v1, v2)]

        c1 = self.gm.addConstr(vvar12 + vvar23 - vvar13 - 1, gurobipy.GRB.LESS_EQUAL, 0)
        c2 = self.gm.addConstr(vvar23 + vvar13 - vvar12 - 1, gurobipy.GRB.LESS_EQUAL, 0)
        c3 = self.gm.addConstr(vvar13 + vvar12 - vvar23 - 1, gurobipy.GRB.LESS_EQUAL, 0)

        if lazy:
            c1.Lazy = 2
            c2.Lazy = 2
            c3.Lazy = 2

class solution_t:
    def __init__(self, solver):
        self.solver = solver
        self.raw = [
            tuple(k)
            for k, var in self.solver.atom_vars.iteritems()
            if var.X > 0.5
        ]

        eqs, noneqs = [a for a in self.raw if a[0] == "="], [a for a in self.raw if a[0] != "="]

        # get the substitution from equality literals.
        self.theta = self._get_substitutor(eqs)
        self.literals_etc, self.literals_nonetc = [], []

        # convert and distribute.
        for l in sorted(set(parse.list2tuple(
            unify.skolemize(unify.subst(self.theta, noneqs))
            ))):
            if parse.is_etc(l):
                self.literals_etc += [l]

            else:
                self.literals_nonetc += [l]

        self.literals = self.literals_etc+self.literals_nonetc

    def check_sum(self):
        '''ensure that the sum of weights of literals is equal to the objective (debug purpose).'''
        p1, p2, p3 = math.log(etcetera.jointProbability(self.literals_etc)), sum([v.obj for v in self.solver.gm.getVars() if v.X > 0.5]), self.solver.gm.objVal

        if abs(p1-p2) >= 1e-6 or abs(p2-p3) >= 1e-6:
            print self.solver.gm.Status
            logging.info("  FATAL ERROR: %f, %f, %f" % (math.exp(p1), math.exp(p2), math.exp(p3)))
            logging.info(parse.display(self.raw))
            return False

        return True

    def get_signature(self):
        '''return a unique signature for this solution.'''
        return frozenset([l for l in self.raw if parse.is_etc(l)])

    def _get_substitutor(self, eqs):
        theta = {}
        eqgraph = nx.Graph()

        for l in eqs:
            eqgraph.add_edge(l[1], l[2])

        # for each equality cluster, look for the representative.
        for cc in nx.connected_components(eqgraph):
            uvars        = list(cc)
            new_var_name = uvars[0]

            # find a better name.
            for t in uvars:
                if not unify.variablep(t):
                    new_var_name = t
                    break

            for t in uvars:
                if t != new_var_name:
                    theta[t] = new_var_name

        return theta

    def _get_raw_sol(self):
        '''return raw solution.'''
        return

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
