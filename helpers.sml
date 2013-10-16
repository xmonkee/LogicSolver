fun add_to_list(clist, c) =
	case clist of
	[] => c::[]
	|x::xs => if x=c then x::xs else x::add_to_list(xs, c)

fun all f ilist = case ilist of
	[] => true
	|x::xs => (f x) andalso (all f xs)

fun zip xs ys = case xs of
	[] => []
	|_  => (hd xs, hd ys) :: (zip (tl xs) (tl ys))
	