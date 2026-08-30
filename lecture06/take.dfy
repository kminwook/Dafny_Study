include "../core-list.dfy"

// take with signature:
function take<T> (n:nat, l : list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(h,t) => if n == 0 then Nil 
                      else Cons(h,take(n-1,t))
}

function takePartical<T>(n : nat, l:list<T>) : list<T>
requires n <= length(l)
{
    match l
    case Nil => Nil
    case Cons(h,t) => if n == 0 then Nil else Cons(h,takePartical(n-1,t))
}

method Main()
{
    print"take(5,Cons(2,Cons(3,Nil))) ==", take(5,Cons(2,Cons(3,Nil))), "\n";
    print"takePartical(5,Cons(2,Cons(3,Nil))) ==", takePartical(5,Cons(2,Cons(3,Nil))), "\n";
}
// and what's the right lemma to prove about the 
// length of take(n,l) ?
function min(i:int, j :int) : int
{
    if i < j then i else j
}

lemma length_take<T>(n : nat, l :list<T>)
ensures length(take(n,l)) == min(n,length(l)){}

lemma length_takePartical<T>(n:nat, l:list<T>)
requires n <= length(l)
ensures length(takePartical(n,l)) == n {}

lemma take_equals_nil<T>(n : nat, l :list<T>)
ensures take(n,l) == Nil <==> 
// take + append: 
// - take n elements from an append

// take equals Nil when?
