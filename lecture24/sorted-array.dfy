/* Lecture 24: a sorted list of integers, kept in a single array.

   a[0] holds the number of elements, n; the elements themselves live in
   a[1..n+1], in order.  Everything from a[n+1] up is unused junk.

   The data invariant (valid, below) has to be
     - established by the method that makes a list (empty), and
     - assumed and re-established by every operation on it. */

predicate sorted(s: seq<int>)
{ forall i:nat, j | i < j < |s| :: s[i] <= s[j] }


// Example 1: writing the invariant down

ghost predicate validBroken(a: array<int>)
  reads a
{
  0 <= a[0] < a.Length && sorted(a[1..a[0]+1])
}
// Nothing calls this yet, and Dafny already objects.  To what?


// Example 2: making an empty list

method emptyBroken(cap: nat) returns (a: array<int>)
  ensures fresh(a) && valid(a)
  ensures elems(a) == [] && a.Length == cap + 1
{
  a := new int[cap + 1];
}
// What does Dafny know about the contents of a brand new array?


// Example 3: insertion

method insertBroken(a: array<int>, x: int)
  requires valid(a)
  modifies a
  ensures valid(a) && size(a) == old(size(a)) + 1
  ensures multiset(elems(a)) == multiset(old(elems(a))) + multiset{x}
{
  ghost var s := elems(a);
  var p := find(a, x);
  var n := size(a);
  shiftUp(a, p + 1, n + 1);
  a[p + 1] := x;
  a[0] := n + 1;
  insertedOK(s, a[1..n+2], x, p);
}
// Sortedness is fine.  What else can go wrong when you add something?


// Example 4: deletion

method deleteBroken(a: array<int>, x: int)
  requires valid(a)
  modifies a
  ensures valid(a)
  ensures multiset(elems(a)) == multiset(old(elems(a))) - multiset{x}
{
  ghost var s := elems(a);
  var p := find(a, x);
  var n := size(a);
  if p < n && get(a, p) == x {
    shiftDown(a, p + 1, n);
    deletedOK(s, a[1..n], p);
  }
}








































/* --- Repair 1: the invariant has a precondition of its own.

   a[0] only makes sense if the array has a slot 0, so a.Length > 0 has
   to come first.  (&& is short-circuiting, so the later conjuncts may
   assume the earlier ones.)  The two halves of the invariant proper:
     - the count is a legal index:  0 <= a[0] < a.Length
     - the live region is sorted:   sorted(a[1..a[0]+1])
   Nothing at all is said about a[a[0]+1..]: like the unknown region in
   the Dutch flag, saying nothing is what makes it easy to maintain. */
ghost predicate valid(a: array<int>)
  reads a
{
  a.Length > 0 && 0 <= a[0] < a.Length && sorted(a[1..a[0]+1])
}

/* What the client thinks it has: a sorted sequence.  Every
   specification below is written in terms of elems, never a[0]. */
ghost function elems(a: array<int>): seq<int>
  reads a
  requires valid(a)
{ a[1..a[0]+1] }

/* --- Repair 2: establish the invariant.

   A fresh array's contents are unknown, so a[0] might be anything.
   Setting it to 0 is all it takes: the live region is then empty, and
   the empty sequence is sorted. */
method empty(cap: nat) returns (a: array<int>)
  ensures fresh(a) && valid(a)
  ensures elems(a) == [] && a.Length == cap + 1
{
  a := new int[cap + 1];
  a[0] := 0;
}

/* Queries need valid(a), but have no modifies clause, so they cannot
   break the invariant: preservation is free. */
function size(a: array<int>): nat
  reads a
  requires valid(a)
  ensures size(a) == |elems(a)|
{ a[0] }

function get(a: array<int>, i: nat): int
  reads a
  requires valid(a) && i < size(a)
  ensures get(a, i) == elems(a)[i]
{ a[i + 1] }

/* Binary search for the insertion point, as in Lecture 22 -- and it is
   the sortedness half of the invariant that makes this legal. */
method find(a: array<int>, x: int) returns (p: nat)
  requires valid(a)
  ensures p <= size(a)
  ensures forall i | 0 <= i < p :: elems(a)[i] < x
  ensures forall i | p <= i < size(a) :: x <= elems(a)[i]
{
  var lo: nat, hi: nat := 0, size(a);
  while lo < hi
    decreases hi - lo
    invariant lo <= hi <= size(a)
    invariant forall i | 0 <= i < lo :: elems(a)[i] < x
    invariant forall i | hi <= i < size(a) :: x <= elems(a)[i]
  {
    var mid := (lo + hi) / 2;
    if get(a, mid) < x { lo := mid + 1; } else { hi := mid; }
  }
  p := lo;
}

method contains(a: array<int>, x: int) returns (b: bool)
  requires valid(a)
  ensures b <==> x in elems(a)
{
  var p := find(a, x);
  if p < size(a) && get(a, p) == x { return true; }
  return false;
}

/* a[lo+1..hi+1] := old(a[lo..hi]); a[lo] keeps its value */
method shiftUp(a: array<int>, lo: nat, hi: nat)
  requires lo <= hi < a.Length
  modifies a
  ensures forall k | 0 <= k <= lo :: a[k] == old(a[k])
  ensures forall k | lo < k <= hi :: a[k] == old(a[k-1])
  ensures forall k | hi < k < a.Length :: a[k] == old(a[k])
{
  var i := hi;
  while i > lo
    invariant lo <= i <= hi
    invariant forall k | 0 <= k <= i :: a[k] == old(a[k])
    invariant forall k | i < k <= hi :: a[k] == old(a[k-1])
    invariant forall k | hi < k < a.Length :: a[k] == old(a[k])
  {
    a[i] := a[i - 1];
    i := i - 1;
  }
}

/* a[lo..hi] := old(a[lo+1..hi+1]); a[hi] keeps its value */
method shiftDown(a: array<int>, lo: nat, hi: nat)
  requires lo <= hi < a.Length
  modifies a
  ensures forall k | 0 <= k < lo :: a[k] == old(a[k])
  ensures forall k | lo <= k < hi :: a[k] == old(a[k+1])
  ensures forall k | hi <= k < a.Length :: a[k] == old(a[k])
{
  var i := lo;
  while i < hi
    invariant lo <= i <= hi
    invariant forall k | 0 <= k < lo :: a[k] == old(a[k])
    invariant forall k | lo <= k < i :: a[k] == old(a[k+1])
    invariant forall k | i <= k < a.Length :: a[k] == old(a[k])
  {
    a[i] := a[i + 1];
    i := i + 1;
  }
}

/* The sequence reasoning, kept out of the methods.  Each lemma
   talks only about sequences, so Dafny proves them quickly; the
   methods then only have to describe, index by index, what the array
   now looks like. */
lemma absent(s: seq<int>, x: int, p: nat)
  requires sorted(s) && p <= |s|
  requires forall i | p <= i < |s| :: x <= s[i]
  
  requires forall i | 0 <= i < p :: s[i] < x
  ensures (p == |s| || s[p] != x) ==> x !in s
{}

lemma insertedOK(s: seq<int>, t: seq<int>, x: int, p: nat)
  requires sorted(s) && p <= |s| && |t| == |s| + 1
  requires forall i | 0 <= i < p :: s[i] < x
  requires forall i | p <= i < |s| :: x <= s[i]
  requires forall i | 0 <= i < p :: t[i] == s[i]
  requires t[p] == x
  requires forall i | p < i < |t| :: t[i] == s[i-1]
  ensures sorted(t)
  ensures multiset(t) == multiset(s) + multiset{x}
{
  assert t == s[..p] + [x] + s[p..];
  assert s == s[..p] + s[p..];
}

lemma deletedOK(s: seq<int>, t: seq<int>, p: nat)
  requires sorted(s) && p < |s| && |t| == |s| - 1
  requires forall i | 0 <= i < p :: t[i] == s[i]
  requires forall i | p <= i < |t| :: t[i] == s[i+1]
  ensures sorted(t)
  ensures multiset(t) == multiset(s) - multiset{s[p]}
{
  assert t == s[..p] + s[p+1..];
  assert s == s[..p] + [s[p]] + s[p+1..];
}

/* --- Repair 3: insertion needs room.

   The invariant says a[0] < a.Length, so after the increment we need
   n + 1 < a.Length, i.e. the list is not already full.  That is a
   precondition on the CLIENT, and it is not part of the invariant:
   a full list is perfectly valid. */
method insert(a: array<int>, x: int)
  requires valid(a) && size(a) < a.Length - 1
  modifies a
  ensures valid(a) && size(a) == old(size(a)) + 1
  ensures multiset(elems(a)) == multiset(old(elems(a))) + multiset{x}
{
  ghost var s := elems(a);
  var p := find(a, x);
  var n := size(a);
  shiftUp(a, p + 1, n + 1);
  a[p + 1] := x;
  a[0] := n + 1;
  insertedOK(s, a[1..n+2], x, p);
}

/* --- Repair 4: shrink the count.

   Forgetting a[0] := n - 1 leaves the list claiming n elements, the
   last of which is a stale copy of the old maximum.  That is still
   sorted (so the invariant is in fact true), but Dafny cannot see that
   without help -- and the multiset postcondition is genuinely false.

   Note the specification: multiset difference removes ONE copy of x,
   or nothing if x is absent, so the "not there" case needs no special
   treatment in the spec. */
method delete(a: array<int>, x: int)
  requires valid(a)
  modifies a
  ensures valid(a)
  ensures multiset(elems(a)) == multiset(old(elems(a))) - multiset{x}
{
  ghost var s := elems(a);
  var p := find(a, x);
  var n := size(a);
  if p < n && get(a, p) == x {
    shiftDown(a, p + 1, n);
    a[0] := n - 1;
    deletedOK(s, a[1..n], p);
  } 
}

/* A client never looks inside the array.  It only ever sees valid(a)
   handed from one call to the next. */
method client()
{
  var a := empty(10);
  insert(a, 3); insert(a, 1); insert(a, 2);
  assert 2 in multiset(elems(a));
  var b := contains(a, 2);
  assert b;
  delete(a, 2);
  assert 2 !in multiset(elems(a));
  assert 1 in multiset(elems(a));
}
