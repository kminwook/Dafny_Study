/* Lecture 22: binary search.
   Ported from COMP1600 2025, week12-code.dfy (sorted, find, find2). */

predicate sorted(s: seq<int>)
{ forall i:nat, j | i < j < |s| :: s[i] <= s[j] }

/* idx is where elem would go: everything below it is smaller,
   everything from it up is not. If you want to know if the array
   contains elem, you can check easily (see below) */
method find_incomplete(a: array<int>, elem: int) returns (idx: nat)
  requires sorted(a[..])
  ensures idx <= a.Length
  ensures forall i:nat | i < idx :: a[i] <  elem
  ensures forall j:nat | idx <= j < a.Length :: elem <= a[j]
{
  var lo, hi := 0, a.Length;
  while (lo < hi)
    // during the loop there is no idx -- there is lo and there is hi.
    // rewrite each postcondition in terms of one of them.
    // what is the third, boring, invariant that makes them meet?
  {
    var mid := (lo + hi) / 2;
    if a[mid] < elem { lo := mid + 1; } 
    else             { hi := mid; }
  }
  idx := lo;
}









/* Below lo: too small.  From hi up: not too small.  Between lo and
   hi: unknown, and that is the part still to search.  At the end
   lo >= hi from the guard and lo <= hi from the invariant, so the
   two halves meet and idx is both of them.

   Edge case a.Length == 0: idx == 0 and both quantifiers are vacuous,
   which is the right thing to say about an empty array. */
method find(a: array<int>, elem: int) returns (idx: nat)
  requires sorted(a[..])
  ensures idx <= a.Length
  ensures forall i:nat | i < idx :: a[i] <  elem
  ensures forall j:nat | idx <= j < a.Length :: elem <= a[j]
{
  var lo, hi := 0, a.Length;
  while (lo < hi)
    decreases hi - lo
    invariant lo <= hi <= a.Length
    invariant forall i:nat | i < lo :: a[i] <  elem
    invariant forall j | hi <= j < a.Length :: elem <= a[j]
  {
    var mid := (lo + hi) / 2;
    if a[mid] < elem { lo := mid + 1; } else { hi := mid; }
  }
  idx := lo;
}

method is_member(a : array<int>, elem : int) returns (memp : bool)
  requires sorted(a[..])
  ensures true
    // try memp ==> exists i:nat :: i < a.Length && a[i] == elem
{
  var i := find(a, elem);
  return i < a.Length && a[i] == elem;
}


/* what's wrong with strict_find here? */
predicate strictly_sorted(s: seq<int>)
{ forall i:nat, j | i <= j < |s| :: s[i] < s[j] }

method strict_find(a: array<int>, elem: int) returns (idx: nat)
  requires strictly_sorted(a[..])
  ensures idx <= a.Length
  ensures forall i:nat | i < idx :: a[i] < elem
  ensures forall j:nat | idx <= j < a.Length :: elem <= a[j]
{
  var lo, hi : nat := 0, a.Length;
  while (lo < hi)
    decreases hi - lo
    invariant lo <= hi <= a.Length
    invariant forall i:nat | i < lo :: a[i] <  elem
    invariant forall j | hi <= j < a.Length :: elem <= a[j]
  {
    var mid := (lo + hi) / 2;
    if a[mid] < elem { lo := mid + 1; } 
    // because of strictness we can stop immediately if we find elem
    else if a[mid] == elem { return mid; } 
    else { hi := mid; }
  }
  idx := lo;
}