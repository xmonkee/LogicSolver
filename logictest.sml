use "logic.sml";

val p1 = v "a" & v "b" or v "c";
val vlist = ["a", "b", "c"];
binary_table vlist;
eval vlist [T, F, F] p1;
val p = [v "a", v "b"];
entails p p1;
val t1 = v "a" or v "b" & v "c" : oper
val t2 = v "a" or (v "b" & v "c") : oper
val t3 = (v "a" or v "b") & v "c" : oper
	