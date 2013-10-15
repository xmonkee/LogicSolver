datatype boolean = TRUE | FALSE 
datatype oper = AND of oper*oper | OR of oper*oper | NOT of oper | IMPL of oper*oper | EQ of oper*oper | CONST of boolean | VAR of string

exception VarCantEval

fun eval e = case e of
CONST x 			=> x
| NOT 	(e 	)		=> (case eval e of TRUE 	=> FALSE 	| FALSE => TRUE)
| AND 	(e1, e2) 	=> (case eval e1 of TRUE 	=> eval e2 	| FALSE => FALSE)
| OR 	(e1, e2) 	=> (case eval e1 of TRUE 	=> TRUE 	| FALSE => eval e2)
| IMPL 	(e1, e2)	=> (case eval e1 of FALSE 	=> TRUE 	| TRUE	=> eval e2)
| EQ 	(e1, e2) 	=> (case eval e1 of 
						TRUE 	=> (case eval e2 of TRUE => TRUE | FALSE => FALSE) 
						|FALSE 	=> (case eval e2 of TRUE => FALSE | FALSE => TRUE) )
| VAR x 			=> raise VarCantEval

fun append_to_each (v, l) = case l of
	[] => []
	|x::xs => (v::x) :: append_to_each(v, xs)
	
	
fun binary_table (num, t, f) = case num of 
	0 => []
	|1 => [[t], [f]]
	|n => append_to_each (t, binary_table (n-1, t, f)) @ append_to_each(f, binary_table (n-1,t ,f))

	
fun evaltable t = case t of
	[] => []
	|x::xs => eval x :: evaltable xs	

fun replace_var (prop, chr, bln) =
	case prop of 
	VAR c => if c=chr then CONST bln else VAR c
	| CONST bln => CONST bln
	| NOT (e1) => NOT (replace_var(e1, chr, bln))
	| AND (e1, e2) => AND (replace_var(e1, chr, bln), replace_var(e2, chr, bln))
	| OR (e1, e2) => OR (replace_var(e1, chr, bln), replace_var(e2, chr, bln))
	| IMPL (e1, e2) => IMPL (replace_var(e1, chr, bln), replace_var(e2, chr, bln))
	| EQ (e1, e2) => EQ (replace_var(e1, chr, bln), replace_var(e2, chr, bln))

fun replace_all_vars(prop, vlist, tlist) = case vlist of
	[] => prop
	|_ => replace_all_vars(replace_var(prop, hd vlist, hd tlist), tl vlist, tl tlist)

fun add_to_list(clist, c) =
	case clist of
	[] => c::[]
	|x::xs => if x=c then x::xs else x::add_to_list(xs, c)
	
fun vars_list (prop) =
	let fun aux (prop, acc) =
		case prop of 
			VAR c => add_to_list(acc, c)
			| CONST bln => acc
			| NOT (e1) => aux(e1, acc)
			| AND (e1, e2) => aux(e2, aux(e1, acc))
			| OR (e1, e2) => aux(e2, aux(e1, acc))
			| IMPL (e1, e2) => aux (e2, aux(e1, acc))
			| EQ (e1, e2) => aux (e2, aux(e1, acc))
	in aux(prop, [])
	end

fun all_props (prop) =
	let	
		val vlist = vars_list prop
		val tlistlist = binary_table (length vlist, TRUE, FALSE)
		fun aux (tlistlist') = case tlistlist' of
			[] => []
			|x::xs => replace_all_vars(prop, vlist, x)::aux(xs)
	in 
		aux(tlistlist)	
	end

fun truth_table (prop) =
	let	
		val vlist = vars_list prop
		val tlistlist = binary_table (length vlist, TRUE, FALSE)
		val table = all_props(prop)
		val truths = evaltable table
		fun cat (xs, ys) = case xs of
			[] => []
			|_ => (hd xs, hd ys) :: cat(tl xs, tl ys)
	in 
		cat (tlistlist, truths)
	end
