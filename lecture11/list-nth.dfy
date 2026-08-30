include "../core-list.dfy"

function member(i : int, l : list<int>) : bool
{
    match l case Nil => false case Cons(h,t) => h == i || member(i,t)
}

function nth<T>(l : list<T>, n : nat) : T
  requires n < length(l)
{
    match l 
    case Cons(h,t) => if n == 0 then h else nth(t, n - 1)
}

lemma mem_nth(i : int, l : list<int>)
  ensures member(i, l) <==> exists n : nat | n < length(l) :: nth(l,n) == i
