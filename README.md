LogicSolver
===========

A small logic language implemented in SML for solving first-order logic. 

The main logic solver resides in logic.sml. 

To use, import "logictest.sml". This will import all the functions and initialize a bunch of variables (a to z actually). This avoid having to type (v "a") to construct a variable. Currently all expression building is handled via datatype, since there is no parser. 

Example:
use "logictest.sml"
- val e1 = a & (b or c);
val e1 = v "a" & (v "b" or v "c") : oper
- val e2 = (a & b) or (a & c);
val e2 = v "a" & v "b" or v "a" & v "c" : oper
- satisfies [e1 equals e2];
val it = (["a","b","c"],SOME [[A,A,A]]) : string list * oper list list option


- truth_table [e1 equals e2]
val it =
  ((["a","b","c"],["((a ^ (b v c)) <=> ((a ^ b) v (a ^ c)))"]),
   [([T,T,T],[T]),([T,T,F],[T]),([T,F,T],[T]),([T,F,F],[T]),([F,T,T],[T]),
    ([F,T,F],[T]),([F,F,T],[T]),([F,F,F],[T])])
  : (string list * string list) * (oper list * oper list) list
-
