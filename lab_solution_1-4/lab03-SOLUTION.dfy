/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 3  (Week 4) -- SOLUTIONS  (private -- do not distribute)

   Reference version of lab03.dfy. Parts A and C verify cleanly.
   Two Part B lemmas (Exercises 11 and 12) genuinely need a helper
   call and are shown with their proofs. 
   ============================================================ */


// -------- Given infrastructure --------

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)
datatype option<V> = None | Some(v : V)

type lset = list<int>

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

lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

lemma member_append(x : int, l1 : list<int>, l2 : list<int>)
  ensures member(x, append(l1, l2)) <==> member(x, l1) || member(x, l2)
{}


/* ---- PART A -- Set operations and their characterising lemmas ---- */

function insert(x : int, A : lset) : lset
{
  Cons(x, A)
}

function delete(x : int, A : lset) : lset
{
  match A
  case Nil => Nil
  case Cons(y, ys) => if x == y then delete(x, ys) else Cons(y, delete(x, ys))
}

function anyElement(A : lset) : int
  requires A.Cons?
{
  A.hd
}

lemma member_insert(x : int, y : int, A : lset)
  ensures member(x, insert(y, A)) <==> x == y || member(x, A)
{}

lemma member_delete(x : int, y : int, A : lset)
  ensures member(x, delete(y, A)) <==> x != y && member(x, A)
{}


/* ---- PART B -- Binary search trees ---- */

datatype btree<V> = Lf 
  | Node(k : int, value : V, left : btree, right : btree)

function size<V>(t : btree) : nat
{
  match t
  case Lf => 0
  case Node(_, _, l, r) => 1 + size(l) + size(r)
}

function lookup<X>(t : btree, key : int) : option
{
  match t
  case Lf => None
  case Node(j, v, l, r) =>
    if key == j then Some(v)
    else if key < j then lookup(l, key)
    else lookup(r, key)
}

function insertT<V>(key : int, v : V, t : btree<V>) : btree
{
  match t
  case Lf => Node(key, v, Lf, Lf)
  case Node(j, u, l, r) =>
    if key == j then Node(key, v, l, r)
    else if key < j then Node(j, u, insertT(key, v, l), r)
    else Node(j, u, l, insertT(key, v, r))
}

function keys<V>(t : btree<V>) : list<int>
{
  match t
  case Lf => Nil
  case Node(j, _, l, r) => append(keys(l), Cons(j, keys(r)))
}

// Exercise 8 -- {} suffices
lemma lookup_insert1<V>(key : int, v : V, t : btree)
  ensures lookup(insertT(key, v, t), key) == Some(v)
{}

// Exercise 9 -- {} suffices
lemma lookup_insert2<V>(k1 : int, k2 : int, v : V, t : btree)
  requires k1 != k2
  ensures lookup(insertT(k1, v, t), k2) == lookup(t, k2)
{}

// Exercise 10 -- {} suffices
lemma size_insert_le<V>(key : int, v : V, t : btree<V>)
  ensures size(insertT(key, v, t)) <= size(t) + 1
{}

// Exercise 11 -- needs member_append; {} does NOT close it
lemma size_insert_new<V>(key : int, v : V, t : btree<V>)
  requires !member(key, keys(t))
  ensures size(insertT(key, v, t)) == size(t) + 1
{
  match t
  case Lf =>
  case Node(j, u, l, r) =>
    member_append(key, keys(l), Cons(j, keys(r)));
}

// Exercise 12 -- capstone; needs lengthAppend; {} does NOT close it
lemma keys_size<V>(t : btree<V>)
  ensures length(keys(t)) == size(t)
{
  match t
  case Lf =>
  case Node(j, u, l, r) =>
    lengthAppend(keys(l), Cons(j, keys(r)));
    // auto-induction supplies keys_size(l) and keys_size(r)
}


/* ---- PART C -- Termination and decreases (extension) ---- */

function upList(lo : int, hi : int) : list<int>
  requires lo <= hi
  decreases hi - lo
{
  if lo == hi then Nil else Cons(lo, upList(lo + 1, hi))
}

/* fi = i'th fib number; fpi = fib number of i - 1 ("previous to i") */
function fib_loop(fi : nat, fpi : nat, i : nat, n : nat) : nat
  requires i <= n decreases n - i
{
  if n == i then fi
  else fib_loop (fi + fpi, fi, i + 1, n)
}

function fib(n:nat) : nat 
{ 
  if n == 0 then 0 
  else fib_loop(1,0,1,n) 
}

// bonus!
function FIB(n:nat) : nat { 
  match n 
  case 0 => 0
  case 1 => 1
  case _ => FIB(n - 1) + FIB(n - 2)
}

lemma fib_loop_correct(fi : int, fpi : int, i : nat, n : nat)
  requires i <= n 
  requires 0 < i 
  requires FIB(i - 1) == fpi
  requires FIB(i) == fi
  ensures fib_loop(fi,fpi,i,n) == FIB(n) 
  decreases n - i 
{}

lemma fib_correct(n:nat) ensures fib(n) == FIB(n)
{
  if n != 0 { fib_loop_correct(1,0,1,n); }
}