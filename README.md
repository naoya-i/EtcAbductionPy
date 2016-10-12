# EtcAbductionPy

## An implementation of Etcetera Abduction in Python

This software is a reference implementation of Etcetera Abduction. Given a knowledge base of first-order definite clauses and a set of observables, this software identifies the most probable set of assumptions that logically entails the observations, assuming the conditional independence of each assumption.

For more information, see the following:

* Gordon, Andrew S. (2016) Commonsense Interpretation of Triangle Behavior. In Proceedings of the Thirtieth AAAI Conference on Artificial Intelligence (AAAI-16), February 12-17, 2016, Phoenix, Arizona.

# Short memo on updates from the original version

This is a forked project from Andrew Gordon's EtcAbductionPy (https://github.com/asgordon/EtcAbductionPy).

## Efficient S-expression parsing

The use of collections.deque makes S-expression parsing much faster.

## Knowledge base caching

* `--kbcache [FILE]` or `-kc [FILE]`: create cache of knowledge base on FILE.


    python etcabductionpy -k knowledge_base.lisp -kc knowledge_base.pickle


* `--kbpickle [FILE]` or `-kp [FILE]`: use cached knowledge base from FILE.


    python etcabductionpy -kp knowledge_base.pickle -d 4


## Integer Linear Programming-based inference for propositional abduction

* `--ilp` or `-l`: use ILP solver (gurobi) to search the (n-)best solution(s).
* `--ilp-verbose` or `-lv`: output an ILP solver log.
* `--expf-graph` or `-expfg`: output graph of explanation formula in dot format.
