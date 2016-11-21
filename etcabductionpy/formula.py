
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

def obtain_relevant_kb(kb, conj, maxdepth):
    """obtain relevant axioms to conj."""

    # relevant reasoning.
    ret, bkon, queue = set(), set(), []
    etcized          = collections.defaultdict(int)

    # add observations to the queue.
    for ob in conj:
        queue += [(0, tuple(ob))]

    while len(queue) > 0:
        lv, p = queue.pop()

        if (lv, p) in bkon or parse.is_etc(p):
            continue

        bkon.add((lv, p))

        if not parse.is_negated(p):
            etcized[p] += 0

        if lv == maxdepth:
            continue

        # add rule to the result and prepare for next queue.
        for relevant_rule in kb[p[0]]:
            if not parse.is_propositional(p):
                theta = unify.unify(p, parse.consequent(relevant_rule))

                if theta == None:
                    continue

                relevant_rule = unify.standardize(unify.subst(theta, relevant_rule))

            etcized[p] += 1

            ret.add(parse.list2tuple(relevant_rule))

            for lit in parse.antecedent(relevant_rule):
                lit = tuple(lit)

                if not parse.is_etc(lit):
                    queue += [(lv+1, lit)]

    return list(ret), kb.get_facts(), [l for l in etcized if etcized[l] == 0]

class formula_t(object):
    def __init__(self):
        self.nxg = nx.DiGraph()
        self.unique_id = 0
        self.levels = {}
        self.parents = {}
        self.dat2node = {}
        self.unifiables = collections.defaultdict(list)
        self.unifiable_var_graph = nx.Graph()

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

    def scan_unifiables(self):
        '''store list of literals with the same predicates.'''
        _unifiables = collections.defaultdict(list)

        for node in self.nxg.nodes_iter():
            if is_opr(node[1]):
                continue

            if not parse.is_etc(node[1]):
                continue

            ari = parse.arity(node[1])
            _unifiables[ari] += [node]

            if len(_unifiables[ari]) >= 2:
                self.unifiables[ari] = _unifiables[ari]

        for arity, nodes in self.unifiables.iteritems():
            for n1, n2 in itertools.combinations(nodes, 2):
                theta = unify.unify(n1[1], n2[1])

                if None == theta:
                    continue

                for t in theta:
                    self.unifiable_var_graph.add_edge(t, theta[t])

    def visualize_var_graph(self, out):
        gvz = nx.nx_agraph.to_agraph(self.unifiable_var_graph)
        gvz.layout()
        gvz.draw(out)

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

    def add_observations(self, obs):

        # add observations.
        gnid_conj = self._create_node("^")

        for ob in obs:
            self.nxg.add_edge(gnid_conj, self._create_node(tuple(ob)))

    def add_nonabs(self, nonab):

        # add observations.
        gnid_conj = self._create_node("^")

        for l in nonab:
            self.nxg.add_edge(gnid_conj, self._create_node(parse.negate(l)))

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

    def add_observations(self, obs):

        # add observations.
        gnid_conj = self._create_node("^")

        for ob in obs:
            self.nxg.add_edge(gnid_conj, self._create_node(tuple(ob)))

    def add_nonabs(self, nonab):

        # add observations.
        gnid_conj = self._create_node("^")

        for l in nonab:
            self.nxg.add_edge(gnid_conj, self._create_node(parse.negate(l)))

class explanation_formula_t(formula_t):
    def __init__(self, ikb, maxdepth):
        super(relevant_formula_t, self).__init__()

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
                    gnid_disj = self._create_node("|")
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
