use "logic.sml";

val p1 = AND (VAR "A", NOT ( OR (VAR "C", VAR "B")));
val p2 = OR (AND (VAR "A", NOT (VAR "B")), AND (NOT (VAR "A"), VAR "B"));

satisfies ["A", "B", "C", "D"] [p1, p2]