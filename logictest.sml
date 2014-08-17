use "logic.sml";
use "varnames.sml";

val p1 = a & b or c;
val p = [a, b];
p entails p1;
val t1 = a or b & c : oper
val t2 = a or (b & c) : oper
val t3 = (a or b) & c : oper	
