
import unify
import parse

import itertools

import sys
import math
import collections
import networkx as nx
import bisect

def is_opr(x):
    return x == "^" or x == "v" or x == "|" or x == "<->"

class formula_t(object):
    def __init__(self):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.levels = {}
        self.parents = {}
        self.dat2node = {}

    def copy(self):
        f = formula_t()
        f.nxg = self.nxg.copy()
        f.levels = self.levels.copy()
        f.parents = self.parents.copy()
        f.unique_id = self.unique_id
        return f

    def visualize(self, out):
        '''visualize the formula as a DAG.'''
        gvz = nx.nx_agraph.to_agraph(self.nxg)
        gvz.layout()
        gvz.draw(out)

    def print_info(self):
        print nx.info(self.nxg)

    def add_facts(self, facts):
        for f in facts:
            if f[0] == "or":
                gnid_or = self._create_node("v")

                for l in f[1:]:
                    gnid_l = self._create_node(tuple(l))
                    self.nxg.add_edge(gnid_or, gnid_l)
    def add_observations(self, obs):
        gnid_conj = self._create_node("^")

        for ob in obs:
            self.nxg.add_edge(gnid_conj, self._create_node(tuple(ob)))

    def add_nonabs(self, nonab):
        gnid_conj = self._create_node("^")

        for l in nonab:
            self.nxg.add_edge(gnid_conj, self._create_node(parse.negate(l)))

    def _create_node(self, dat, level = 0, parent = None):
        self.unique_id += 1
        self.levels[(self.unique_id, dat)] = level
        self.parents[(self.unique_id, dat)] = parent
        self.dat2node[dat] = (self.unique_id, dat)

        if parse.is_etc(dat):
            self.nxg.add_node((self.unique_id, dat), color='red', fontcolor='red')

        return (self.unique_id, dat)

class maxsat_t(formula_t):
    def __init__(self, kb):
        super(maxsat_t, self).__init__()

        def _parse(f, parent = -1):
            if f[0] == "and":
                gnid_conj = self._create_node("^")

                if parent != -1:
                    self.nxg.add_edge(parent, gnid_conj)

                for cjt in f[1:]:
                    _parse(cjt, gnid_conj)

            elif f[0] == "or":
                gnid_disj = self._create_node("v")

                if parent != -1:
                    self.nxg.add_edge(parent, gnid_disj)

                for djt in f[1:]:
                    _parse(djt, gnid_disj)

            else:
                gnid_lit = self._create_node(tuple(f))

                if parent != -1:
                    self.nxg.add_edge(parent, gnid_lit)

        for rule in kb:
            _parse(rule)

class clark_completion_t(formula_t):
    """Assumes knowledge base is in the form of Normal Logic Programs."""

    def __init__(self, kb):
        super(clark_completion_t, self).__init__()

        explanations = collections.defaultdict(list)

        # collect a set of bodies with the same head.
        for rule in kb:
            explanations[tuple(parse.consequent(rule))] += [parse.antecedent(rule)]

        # complete knowledge base.
        for head, bodies in explanations.iteritems():
            gnid_dimp = self._create_node("<->")
            gnid_head = self._create_node(tuple(head))
            self.nxg.add_edge(gnid_dimp, gnid_head)

            # create "OR" node for representing disjunction of explanations.
            gnid_expl_from = gnid_dimp

            if len(bodies) > 1:
                gnid_disj = self._create_node("|")
                self.nxg.add_edge(gnid_dimp, gnid_disj)
                gnid_expl_from = gnid_disj

            for body in bodies:
                gnid_body_from = gnid_expl_from

                # create "AND" node for representing conjunction of body literals.
                if len(body) > 1:
                    gnid_conj = self._create_node("^")
                    self.nxg.add_edge(gnid_expl_from, gnid_conj)
                    gnid_body_from = gnid_conj

                for literal in body:
                    gnid_lit = self._create_node(tuple(literal))
                    self.nxg.add_edge(gnid_body_from, gnid_lit)

class clark_completion_cnf_t(formula_t):
    """Assumes knowledge base is in the form of Normal Logic Programs."""

    def __init__(self, kb):
        super(clark_completion_cnf_t, self).__init__()

        explanations = collections.defaultdict(list)

        # collect a set of bodies with the same head.
        for rule in kb:
            explanations[tuple(parse.consequent(rule))] += [parse.antecedent(rule)]

        # complete knowledge base.
        for head, bodies in explanations.iteritems():

            # h <=> e1 v e2 v ...

            # from each body to head.
            # e1 => h, e2 => h, ...
            for body in bodies:
                gnid_or   = self._create_node("v")
                gnid_head = self._create_node(tuple(head))
                self.nxg.add_edge(gnid_or, gnid_head)

                for b in body:
                    gnid_b = self._create_node(tuple(parse.negate(b)))
                    self.nxg.add_edge(gnid_or, gnid_b)

            # h => e1a v e2a v ...
            # h => e1a v e2b v ...
            for body in itertools.product(*bodies):
                gnid_or   = self._create_node("v")
                gnid_head = self._create_node(tuple(parse.negate(head)))
                self.nxg.add_edge(gnid_or, gnid_head)

                for b in body:
                    gnid_b = self._create_node(tuple(b))
                    self.nxg.add_edge(gnid_or, gnid_b)
