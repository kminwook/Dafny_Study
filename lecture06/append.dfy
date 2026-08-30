datatype list<T> = Nil | Cons(hd:T, tl: list<T>)

function length<T>(l : list<T>) : nat
{
    match l
    case Nil => 0
    case Cons(h,t) => 1 + length(t)
}

function append<T> (l1:list<T>, l2 : list<T>) : list<T>
{
    match l1
    case Nil => l2
    case Cons(h,t) => Cons(h, append(t, l2))
}

function bogus_append<T>(l1: list<T>, l2:list<T>) : list<T>
{
    match l2
    case Nil => l1
    case Cons(h,t) => append(append(l1, Cons(h, Nil)),t)
}

lemma length_append<T>(l1 : list<T>, l2:list<T>)
ensures length(append(l1,l2)) == length(l1) + length(l2) {}

lemma append_nil<T>(l1:list<T>)
ensures append(l1,Nil) == l1{}

lemma add_cancel(x:int,y:int,z:int)
ensures x + y == x + z <==> y == z {}

lemma mult_cancel(x:int,y:int,z:int)
ensures x*y == x*z <==> y==z || x == 0{}

lemma append_cancel<T>(x:list<T>, y :list<T>, z:list<T>)
ensures append(x,y) == append(x,z) <==> y==z {}

lemma append_cancelR<T>(x:list<T>, y :list<T>, z:list<T>)
ensures append(x,y) == append(x,z) <==> y==z {}
