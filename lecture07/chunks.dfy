include "../core-list.dfy"

function take<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil 
    case Cons(h,t) => if n == 0 then Nil else Cons(h,take(n-1,t))
}
function drop<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => if n == 0 then l else drop(n-1,t)
}

// chunks (2, [1,2,3,4]) == [[1,2], [3,4]]
// chunks (3, [1,2]) == [[1,2]]
// chunks (2, [1,2,3]) == [[1,2], [3]]
// chunks (0, [1,2,3]) == ??
function chunks<T>(n : nat, l:list<T>) : list<list<T>>
  requires 0 < n 
{
    match l case Nil => Nil
    case _ => Cons(take(n,l),chunks(n,drop(n,l)))
}

// chunks (3, [1,2]) == Cons(take(3, [1,2]), chunks(3, drop(3, [1,2]))
//                == Cons([1,2], chunks(3, []))
//                == Cons([1,2], [])
//                == [[1,2]]
