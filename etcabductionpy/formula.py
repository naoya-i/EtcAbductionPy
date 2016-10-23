
import unify
import parse

import itertools

import sys
import math
import collections
import networkx as nx
import bisect

class formula_t(object):
    def __init__(self):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.levels = {}
        self.parents = {}
        self.unifiables = collections.defaultdict(list)

    def copy(self):
        f = formula_t()
        f.nxg = self.nxg.copy()
        f.levels = self.levels.copy()
        f.parents = self.parents.copy()
        f.unique_id = self.unique_id
        return f

    def visualize(self, out):
        '''visualize the formula as a DAG.'''
        gvz = nx.to_agraph(self.nxg)
        gvz.layout()
        gvz.draw(out)

    def print_info(self):
        print nx.info(self.nxg)

    def _scan_unifiables(self):
        '''store list of literals with the same predicates.'''
        _unifiables = collections.defaultdict(list)

        for node in self.nxg.nodes_iter():
            if node[1] in ["^", "v", "<->"]:
                continue

            _unifiables[node[1]] += [node]

            if len(_unifiables[node[1]]) >= 2:
                self.unifiables[node[1]] = _unifiables[node[1]]

    def _create_node(self, dat, level = 0, parent = None):
        self.unique_id += 1
        self.levels[(self.unique_id, dat)] = level
        self.parents[(self.unique_id, dat)] = parent

        if parse.is_etc(dat):
            self.nxg.add_node((self.unique_id, dat), color='red', fontcolor='red')

        return (self.unique_id, dat)


class explanation_formula_t(formula_t):
    def __init__(self, ikb, maxdepth):
        super(explanation_formula_t, self).__init__()

        self.ikb = ikb
        self.maxdepth = maxdepth
        self.lower_bound_logprob  = 0
        self.lb_node_choice = {}

    def derive(self, obs):
        _, self.lower_bound_logprob = self.generate(obs, 0)
        self._scan_unifiables()

    def traverse_lower_bound(self, node = (1, "^")):
        if node[1] == "v":
            for n in self.traverse_lower_bound(self.lb_node_choice[node]):
                yield n

        elif node[1] == "^":
            for child in self.nxg.successors(node):
                for n in self.traverse_lower_bound(child):
                    yield n

        else:
            yield node

    def generate(self, conj, level, from_id = -1):
        '''generate an explanation formula for the conjunction F of literals. The formula is encoded as an AND-OR tree (networkx.DiGraph). At the same, this function returns a lower bound.'''

        # creat "and" node if necessarry.
        if from_id == -1 or len(conj) > 1:
            gnid_conj    = self._create_node("^")

            if -1 != from_id:
                self.nxg.add_edge(from_id, gnid_conj)

            from_id = gnid_conj

        lower_bound_prob = 0.0

        for literal in conj:
            predicate = literal[0]
            best_prob = 0.0

            if (level < self.maxdepth) and (predicate in self.ikb):

                # create "or" node if necessary.
                gnid_disj = None
                from_node = from_id

                if len(self.ikb[predicate]) > 1:
                    gnid_disj = self._create_node("v")
                    from_node = gnid_disj
                    self.nxg.add_edge(gnid_conj, gnid_disj)

                # expand!
                best_node, best_prob, num_qualified = self.expand(from_node, literal, level)

                if None != gnid_disj:
                    if 0 == num_qualified:

                        # delete the "or" node if nothing is hypothesized.
                        self.nxg.remove_node(gnid_disj)

                    else:
                        self.lb_node_choice[gnid_disj] = best_node

            else:
                if 0 == level:
                    continue

                # create new node for literal
                gnid_lit = self._create_node(tuple(literal))
                self.nxg.add_edge(from_id, gnid_lit)

                if parse.is_etc(literal):
                    best_prob = math.log(literal[-1])

                if len(conj) == 1:
                    gnid_conj = gnid_lit

            lower_bound_prob += best_prob

        return gnid_conj, lower_bound_prob

    def expand(self, from_node, literal, level):
        """backchain on the literal"""
        predicate = literal[0]
        probs = []

        for rule in self.ikb[predicate]:
            qualified = True

            if level == self.maxdepth-1:
                # does it contain non-abducible?
                for lit in parse.antecedent(rule):
                    if not parse.is_etc(lit):
                        qualified = False
                        break

            if qualified:
                probs += [self.generate(parse.antecedent(rule), level+1, from_node)]

        # find the best node.
        best_node, best_prob = max(probs, key=lambda x: x[1])

        return best_node, best_prob, len(probs)
