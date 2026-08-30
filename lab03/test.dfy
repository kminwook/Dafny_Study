datatype list<T> = Nil | Cons(hd : T, tl : list<T>)
datatype option<V> = None | Some(v : V)
datatype btree<V> = Lf | Node(k : int, value : V, left : btree, right : btree)

type lset = list<int>   // a set of ints, stored as a list

function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, xs) => 1 + length(xs)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T>
{
  match l1
  case Nil => l2
  case Cons(x, xs) => Cons(x, append(xs, l2))
}

function member(x : int, l : list<int>) : bool
{
  match l
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}

// Two already-proved helper lemmas you may CALL later if you need them.
lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

lemma member_append(x : int, l1 : list<int>, l2 : list<int>)
  ensures member(x, append(l1, l2)) <==> member(x, l1) || member(x, l2)
{}


 //  PART A -- Set operations and their characterising lemmas
