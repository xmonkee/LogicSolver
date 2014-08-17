use "helpers.sml";

(* This defines the language of 
 * constructing logical sentences. 
 * sentences look like * "F or b & c gives b & c". 
 * Variables are makred with v (a = v"a")i
 * A indicates "ANY", when we are not sure if it's T of F  *)
datatype oper = ! of oper | & of oper*oper | or of oper*oper | gives of oper*oper | equals of oper*oper | T | F | A | v of string
infixr 2 &
infixr 1 or
infixr 0 gives
infixr 0 equals


(* Auxillary function. Looks up a variable.
 * Environment is modeled as a list of varnames
 * and a list of their values.*)
fun lookupvar vlist tlist x =
  let 
    val table = (zip vlist tlist)
    fun aux table = case table of
      [] => v x
      |(var, t)::xs => if var=x then t else (aux xs)
  in
    aux table
  end

(* "eval" function. Evaluates logical expressions based on FOL *)
fun eval vlist tlist e = 
  let  
    fun eval e = case e of
     T         => T
    |F        => F    
    | !e1          => ( case eval e1 of T => F       | F => T          | _ => !e1                       )
    | e1 & e2      => ( case eval e1 of T => eval e2 | F => F          | _ => (eval e1) &     (eval e2) )
    | e1 or e2     => ( case eval e1 of T => T       | F => eval e2    | _ => (eval e1) or    (eval e2) )
    | e1 gives e2  => ( case eval e1 of F => T       | T => eval e2    | _ => (eval e1) gives (eval e2) )
    | e1 equals e2 => ( case eval e1 of T => eval e2 | F => eval (!e2) | _ => (eval e1) equals(eval e2) )
    | v x          => lookupvar vlist tlist x
  in
    eval e
  end

(* Auxillary function, returns true if all expressions in a list are T *)
fun evaltrue vlist tlist plist = all (fn p => (eval vlist tlist p) = T) plist

(* Auxillary function, returns false if all expressions in a list are F*)
fun evalfalse vlist tlist plist = exists (fn p => (eval vlist tlist p) = F) plist

(* Auxillary function, evalutes each expression in a list *)
fun evalist vlist tlist plist = map (eval vlist tlist) plist
 
(* Auxillary function, replaces each variable in a variable list with A *)
fun v2p vlist = case vlist of [] => [] | x::xs => A::v2p(xs)

fun toString prop = case prop of
    v c            => c
  | T              => "T"
  | F              => "F"
  | !e             => "~" ^ (toString e )
  | e1 & e2        => "(" ^ (toString e1) ^ " ^ "   ^ (toString e2) ^ ")"
  | e1 or e2       => "(" ^ (toString e1) ^ " v "   ^ (toString e2) ^ ")"
  | e1 gives e2    => "(" ^ (toString e1) ^ " => "  ^ (toString e2) ^ ")"
  | e1 equals e2   => "(" ^ (toString e1) ^ " <=> " ^ (toString e2) ^ ")"

(* Determines all the free variables in a list of expressions
 * Useful for creating truth tables and other interface functions *)
fun vars_list (proplist) =
  let 
    fun aux (prop, acc) = case prop of 
      v c          => add_to_list(acc, c)
    | F            => acc
    | T            => acc
    | ! e1         => aux (e1, acc)
    | e1 & e2      => aux (e2, aux(e1, acc))
    | e1 or e2     => aux (e2, aux(e1, acc))
    | e1 gives e2  => aux (e2, aux(e1, acc))
    | e1 equals e2 => aux (e2, aux(e1, acc))
  in
    case proplist of
    []     =>  []
    |x::[]  =>  aux(x, [])
    |x::xs  =>  aux(x, vars_list(xs))
  end
  
(* Generates permutations of {T,F} for any number of variables *)  
fun binary_table vlist = 
  let 
    val num = length vlist
    fun aux num = case num of 
      0 => []
      |1 => [[T], [F]]
      |n => append_to_each T (aux (n-1)) @ append_to_each F (aux (n-1))
  in 
    aux num
  end

(* Takes a list of expressions,
 * Extracts the free variables,
 * Generates the truth table for variables, 
 * and returns corresponding truth values of expressions *)
fun truth_table proplist = 
  let val vlist = vars_list proplist
  in
    ((vlist, map toString proplist), 
    map 
      (fn tlist => (tlist, 
        (map (fn prop => (eval vlist tlist prop)) proplist))
      ) 
    (binary_table vlist))
  end
  
(* Satisfying Truth Table, 
 * Shows all possible {T,F} permutations
 * that make all expressions in input list true *)
fun satisfies_tt proplist =
  let 
    val vlist = vars_list proplist
    val tlist = binary_table vlist
    val tlistf = filter (fn tl => evaltrue vlist tl proplist) tlist
  in
    case tlistf of
      [] => (vlist, NONE)
      |_ => (vlist, SOME tlistf)
  end

(* Shows all possible variable combinations
 * that make all expressions in a list true, 
 * different from satisfies_tt in that it
 * return A for variables who's truth value 
 * does not matter. It's also faster since
 * it does not evaluate every permutation *) 
fun satisfies plist =
  let
    fun satisfies (vlist, plist) = 
      if (evaltrue [] [] plist) 
        then SOME [(v2p vlist)]
        else if (evalfalse [] [] plist)
          then NONE
          else case vlist of
            x::xs => 
              let 
                val t = satisfies(xs, evalist [x] [T] plist)
                val f = satisfies(xs, evalist [x] [F] plist)
              in 
                (case (t,f) of 
                (NONE,NONE) => NONE
                |(SOME ts, NONE) => SOME (append_to_each T ts)
                |(NONE, SOME fs) => SOME (append_to_each F fs)
                |(SOME ts, SOME fs) => SOME ((append_to_each T ts)@(append_to_each F fs)) 
                )
              end
             |[] => if (evaltrue [] [] plist)
              then SOME []
              else NONE
    val vlist = vars_list plist
    val sat = satisfies (vlist, plist)
  in
    (vlist, sat)
  end

(* Simply checks if a list of expressions 
 * entail or imply another. *)
fun op entails (proplist, conc) = 
    case satisfies (!conc :: proplist) of
    (_ , NONE) => true
    |(_ , _) => false
infix entails
