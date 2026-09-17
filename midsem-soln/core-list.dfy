datatype list<T> = Nil | Cons(hd: T, tl: list<T>)
type ilist = list<int>

predicate member(i : int, l : list<int>)
{
    match l case Nil => false
    case Cons(j,js) => i == j || member(i,js)
}

function length<T>(l : list<T>) : nat
{
    match l case Nil => 0
    case Cons(x,xs) => 1 + length(xs)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T>
{
    match l1 case Nil => l2
    case Cons(x,xs) => Cons(x,append(xs, l2))
}

function reverse<T>(l: list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
}

function take<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(x,xs) => if n == 0 then Nil
    else Cons(x,take(n-1, xs))
}

function drop<T>(n:nat, l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(x,xs) => if n == 0 then l
    else drop(n-1,xs)
}