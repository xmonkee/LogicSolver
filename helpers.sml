fun add_to_list(clist, c) =
	case clist of
	[] => c::[]
	|x::xs => if x=c then x::xs else x::add_to_list(xs, c)

fun listify f ilist =
	case ilist of 
	[] => []
	|x::xs => f x :: listify f xs

fun all f ilist = case ilist of
	[] => true
	|x::xs => (f x) andalso (all f xs)
	