/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 2  (Week 3) -- SOLUTIONS

   Reference version of lab02.dfy. Every function is defined and
   every lemma is intended to verify with the empty body {}. Where a
   {} proof is less certain, a commented fallback inductive hint is
   given in case a particular Dafny version needs the help.
   ============================================================ */


// -------- Given (recap) --------

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)

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

function min(a : nat, b : nat) : nat
{
  if a < b then a else b
}


/* ---- PART A -- More recursion over lists ---- */

function take<T>(n : nat, l : list<T>) : list<T>
{
  if n == 0 then Nil
  else
    match l
    case Nil => Nil
    case Cons(x, xs) => Cons(x, take(n - 1, xs))
}

function drop<T>(n : nat, l : list<T>) : list<T>
{
  if n == 0 then l
  else
    match l
    case Nil => Nil
    case Cons(x, xs) => drop(n - 1, xs)
}

function reverse<T>(l : list<T>) : list<T>
{
  match l
  case Nil => Nil
  case Cons(x, xs) => append(reverse(xs), Cons(x, Nil))
}


/* ---- PART B -- zip and unzip ---- */

function zip<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>
{
  match (l1, l2)
  case (Cons(x, xs), Cons(y, ys)) => Cons((x, y), zip(xs, ys))
  case _ => Nil
}

function unzip<A, B>(l : list<(A, B)>) : (list<A>, list<B>)
{
  match l
  case Nil => (Nil, Nil)
  case Cons((x, y), rest) =>
    var (xs, ys) := unzip(rest);
    (Cons(x, xs), Cons(y, ys))
}

// Includes the required precondition
function zipPartial<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>
  requires length(l1) == length(l2)
{ // pattern-matching version also works
  if l1.Nil? then Nil
  else Cons((l1.hd, l2.hd), zipPartial(l1.tl, l2.tl))
}


/* ---- PART C -- Lemmas: let Dafny do the induction ---- */

// induction over the numbers (the Lecture 5 example)
function sumUpTo(n : nat) : nat
{
  if n == 0 then 0 else n + sumUpTo(n - 1)
}

lemma triangle(n : nat)
  ensures 2 * sumUpTo(n) == n * (n + 1)
{}

lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

lemma takeLength<T>(n : nat, l : list<T>)
  ensures length(take(n, l)) == min(n, length(l))
{}

lemma dropLength<T>(n : nat, l : list<T>)
  ensures length(drop(n, l)) == length(l) - min(n, length(l))
{}

lemma takeDropAppend<T>(n : nat, l : list<T>)
  ensures append(take(n, l), drop(n, l)) == l
{}

lemma unzipLength<A, B>(l : list<(A, B)>)
  ensures var (l1,l2) := unzip(l); length(l1) == length(l) && length(l2) == length(l)
 {}

lemma zipPartialLength<A, B>(l1 : list<A>, l2 : list<B>)
  requires length(l1) == length(l2)
  ensures length(zipPartial(l1, l2)) == length(l1)
{}

/* ---- PART D -- Recursion over trees ---- */

datatype tree<T> = Leaf | Node(left : tree<T>, val : T, right : tree<T>)

function treeSize<T>(t : tree<T>) : nat
{
  match t
  case Leaf => 0
  case Node(l, _, r) => 1 + treeSize(l) + treeSize(r)
}

function mirror<T>(t : tree<T>) : tree<T>
{
  match t
  case Leaf => Leaf
  case Node(l, v, r) => Node(mirror(r), v, mirror(l))
}

lemma mirrorSize<T>(t : tree<T>)
  ensures treeSize(mirror(t)) == treeSize(t)
{}

lemma mirrorMirror<T>(t : tree<T>)
  ensures mirror(mirror(t)) == t
{}

function max(a : int, b : int) : int
{
  if a > b then a else b
}

function maxDepth<T>(t : tree<T>) : nat
{
  match t
  case Leaf => 0
  case Node(l, _, r) => 1 + max(maxDepth(l), maxDepth(r))
}

// the relation to be discovered is  <=
lemma depthAndSize<T>(t : tree<T>)
  ensures maxDepth(t) <= treeSize(t)
{}
