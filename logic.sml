use "helpers.sml";

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

fun replace_var prop chr bln =
	case prop of 
	VAR c => if c=chr then CONST bln else VAR c
	| CONST bln => CONST bln
	| NOT (e1) => NOT (replace_var e1 chr bln)
	| AND (e1, e2) => AND (replace_var e1 chr bln, replace_var e2 chr bln)
	| OR (e1, e2) => OR (replace_var e1 chr bln, replace_var e2 chr bln)
	| IMPL (e1, e2) => IMPL (replace_var e1 chr bln, replace_var e2 chr bln)
	| EQ (e1, e2) => EQ (replace_var e1 chr bln, replace_var e2 chr bln)

fun replace_all_vars prop vlist tlist = case vlist of
	[] => prop
	|_ => replace_all_vars (replace_var prop (hd vlist) (hd tlist))  (tl vlist) (tl tlist)
	
fun binary_table vlist t f = 
	let 
		val num = length vlist
		fun append_to_each v l = case l of
			[] => []
			|x::xs => (v::x) :: append_to_each v xs
		fun aux num = case num of 
			0 => []
			|1 => [[t], [f]]
			|n => append_to_each t (aux (n-1)) @ append_to_each f  (aux (n-1))
	in 
		aux num
	end

fun truth prop vlist tlist = eval (replace_all_vars prop vlist tlist)
	
fun join_tables ll1 ll2 = case ll1 of
	[] => []
	|_ => (hd ll1, hd ll2) :: join_tables (tl ll1) (tl ll2)

fun truth_list vlist prop = 
	let	
		val tlistlist = binary_table vlist TRUE FALSE
		fun aux tll = case tll of
			[] => []
			|tl::tls =>  truth prop vlist tl :: aux tls
	in 
		aux tlistlist
	end

fun truth_lists vlist proplist = 
	listify(truth_list(vlist))(proplist)
		
fun satisfies vlist proplist =
	let 
		fun aux tls = case tls of
			[] => []
			|tl::tls => if (all (fn prop => (truth prop vlist tl)=TRUE) proplist) 
				then tl::aux tls 
				else aux tls
	in
		aux (binary_table vlist TRUE FALSE) 
	end