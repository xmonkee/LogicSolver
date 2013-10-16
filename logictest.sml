use "logic.sml";

val p1 = v "a" & v "b" or v "c";
replace_var p1 "a" T;
val vlist = ["a", "b", "c"];
replace_all_vars p1  vlist [T, F, F];
binary_table vlist;
truth p1 vlist [T, F, F];
truth p1 vlist [T, T, F];
truth p1 vlist [T, F, T];
val p = [v "a", v "b"];
entails p p1;
val t1 = v "a" or v "b" & v "c" : oper
val t2 = v "a" or (v "b" & v "c") : oper
val t3 = (v "a" or v "b") & v "c" : oper