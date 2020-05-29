<script type="text/javascript"
        src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.0/MathJax.js?config=TeX-AMS_CHTML"></script>

\\[a^2+b^2\\]

# Project "LogicalTime"

## Coq Model of Logical Time

Co-authors:

* Grygoriy Zholtkevych g.zholtkevych@karazin.ua
* Anna Zozulya avzozulya@gmail.com

Department of Theoretical and Applied Computer Science  
School of Mathemetics and Computer Science at V.N. Karazin Kharkiv National University  
4 Svobody Sqr, Kharkiv, 61022, Ukraine

For correct work please, run command  
...$ coqide -f _CoqProject  
in the directory containing this repository  then you can load any v-file

## Project Files

* README.md is this file
* _CoqProject contains configuration of LogicalTime Library
* preliminaries.v contains preliminary facts about natural numbers; the file depends on Coq.Sets.Ensembles and Coq.Sets.Finite_sets.
* causal_def.v contains definitions of classes EventSet and Causet; the file depends on Coq.Sets.Relations_1, Coq.Sets.Ensembles, and Coq.Sets.Finite_sets.
* timer.v contains definitions of the EventSet-instance and Causet-instance for natural numbers; the file depends on causal_def and preliminaries.
