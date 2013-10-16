use "helpers.sml";

datatype oper = ! of oper | & of oper*oper | or of oper*oper | gives of oper*oper | equals of oper*oper | T | F | v of string
infixr 2 &
infixr 1 or
infixr 0 gives
infixr 0 equals

exception VarCantEval

fun lookupvar vlist tlist c =
	let val table = (zip vlist tlist)
		fun aux table = case table of
			[] => v c
			(v, t)::xs => if v=c then t else (aux xs)
			

fun eval e vlist tlist = case e of
 T	 			=> T
|F				=> F		
| !e1 			=> ( case eval e1 of T => F 	| F => T		)
| e1 & e2	 	=> (case eval e1 of T => eval e2| F => F		)
| e1 or e2	 	=> (case eval e1 of T => T	 	| F => eval e2	)
| e1 gives e2	=> (case eval e1 of F => T 		| T	=> eval e2	)
| e1 equals e2	=> (case eval e1 of T => eval e2| F => eval (!e2))
| v x 			=> lookupvar vlist tlist c


fun vars_list (proplist) =
	let 
		fun aux (prop, acc) = case prop of 
			v c => add_to_list(acc, c)
			| F => acc
			| T => acc
			| ! e1 => aux(e1, acc)
			| e1 & e2 => aux(e2, aux(e1, acc))
			| e1 or e2 => aux(e2, aux(e1, acc))
			| e1 gives e2 => aux (e2, aux(e1, acc))
			| e1 equals e2 => aux (e2, aux(e1, acc))
	in
		case proplist of
		[] 		=>	[]
		|x::[]	=>	aux(x, [])
		|x::xs	=>	aux(x, vars_lists(xs))
	end
	
fun replace_var prop chr bln =
	case prop of 
	v c => if c=chr then bln else v c
	| T => T
	| F => F
	| ! e1 => ! (replace_var e1 chr bln)
	| e1 & e2 =>  (replace_var e1 chr bln) & (replace_var e2 chr bln)
	| e1 or e2 =>  (replace_var e1 chr bln) or (replace_var e2 chr bln)
	| e1 gives e2 =>  (replace_var e1 chr bln) gives (replace_var e2 chr bln)
	| e1 equals e2 => (replace_var e1 chr bln) equals (replace_var e2 chr bln)

fun toString prop = case prop of
	v c => c
	|T => "T"
	|F => "F"
	| ! e => "~" ^ (toString e)
	|e1 & e2 => "(" ^ (toString e1) ^ " ^ " ^ (toString e2) ^ ")"
	|e1 or e2 => "(" ^ (toString e1) ^ " v " ^ (toString e2) ^ ")"
	|e1 gives e2 => "(" ^ (toString e1) ^ " => " ^ (toString e2) ^ ")"
	|e1 equals e2 => "(" ^ (toString e1) ^ " <=> " ^ (toString e2) ^ ")"
	
fun replace_all_vars prop vlist tlist = case vlist of
	[] => prop
	|_ => replace_all_vars (replace_var prop (hd vlist) (hd tlist))  (tl vlist) (tl tlist)
	
fun binary_table vlist = 
	let 
		val num = length vlist
		fun append_to_each a blist = case blist of
			[] => []
			|x::xs => (a::x) :: append_to_each a xs
		fun aux num = case num of 
			0 => []
			|1 => [[T], [F]]
			|n => append_to_each T (aux (n-1)) @ append_to_each F (aux (n-1))
	in 
		aux num
	end

fun truth prop vlist tlist = 
	eval (replace_all_vars prop vlist tlist)

fun truth_table proplist = 
	let val vlist = vars_list proplist
	in
		((vlist, 
		map 
			(fn prop => toString prop) 
		proplist), 
		
		map 
			(fn tlist => (tlist, 
			(map 
				(fn prop => (truth prop vlist tlist)) 
			proplist))) 
		(binary_table vlist))
	
	end
	
fun satisfies proplist =
	let 
		val vlist = vars_list proplist
		fun aux tls = case tls of
			[] => []
			|tl::tls => if (all (fn prop => (truth prop vlist tl)=T) proplist) 
				then tl::aux tls 
				else aux tls
	in
		(vlist, aux (binary_table vlist) )
	end

fun entails proplist conc = 
		case satisfies (!conc :: proplist) of
		(_ , []) => true
		|(_ , _) => false