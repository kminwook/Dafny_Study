// though Dafny gets this one "for free", we can still try 
// providing our own decreases clause
function fib(n:nat) :nat
{
    if n < 2 then 1 else fib(n-1) + fib(n-2)
}

datatype list<T> = Nil | Cons(T, list<T>)

// similarly, what can we provide here?
function length<T>(l : list<T>) : nat
{
    match l case Nil => 0 case Cons(_,t) => 1 + length(t)
}

// once length is defined you can always write 
//   decreases length(l)
// instead of 
//   decreases l
function ontoback<T>(l : list<T>, x : T) : list<T>
{
    match l 
    case Nil => Cons(x,Nil) 
    case Cons(h,t) => Cons(h, ontoback(t,x))
}

// weird, *and* inefficient as well!
function weird_append<T>(l1 : list<T>, l2:list<T>) : list<T>
decreases l2 
{
    match l2
    case Nil => l1
    case Cons(h,t) => weird_append(ontoback(l1,h), t)
}


function up(x:nat) : nat
decreases 100-x 
{
    if x > 100 then x else 1 + up(x + 1)
}

function M(x:int, b:bool) : int 
decreases if b then 0 else 1
{
    if b then x else M(x + 25, true)
}
