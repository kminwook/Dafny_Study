datatype list<T> = Nil | Cons(hd : T, tl : list<T>)
datatype option<T> = None | Some(T)
type lset = list<int>

function length<T>(l:list<T>) : nat
{
    match l case Nil => 0 case Cons(_,xs) => length(xs) + 1
}

function append<T> (l1:list<T>, l2:list<T>) : list<T>
{
    match l1 case Nil => l2
    case Cons(x,xs) => Cons(x,append(xs,l2))
}

function member(x : int, l : list<int>) : bool
{
  match l
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}