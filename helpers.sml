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

fun filter f xs = case xs of
	[] => []
	|x::xs' => if (f x) 
		then x::(filter f xs')
		else (filter f xs')

fun exists f xs = case xs of
	[] => false
	|x::xs' => if f(x) 
		then true
		else exists f xs'

fun rev xs = 
	let fun rev (xs, acc) = case xs of
		[] => acc
		|x::xs' => rev (xs', x::acc)
	in rev (xs, [])
	end

fun append_to_each a blist = 
	map (fn b => a::b) blist


