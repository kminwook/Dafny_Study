datatype list<T> = Nil | Cons(hd: T, tl: list<T>)

// write these
function length<T>(l : list<T>) : nat {
    match l
    case Nil => 0
    case Cons(_,tl) => 1 + length(tl)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T> {
    match l1
    case Nil => l2
    case Cons(hd,tl) => Cons(hd,append(tl,l2))
}

// some lemma might connect these two notions
// lemma ...
  