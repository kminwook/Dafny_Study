/* Lecture 23: selection sort, with the two-clause specification.
   Ported from COMP1600 2025, tutorial 12 exercise 3. */

ghost predicate sorted(a: seq<int>)
{ forall i:nat, j | i < j < |a| :: a[i] <= a[j] }

/* everything in s1 is <= everything in s2 */
ghost predicate seqleq(s1:seq<int>, s2:seq<int>)
{
  forall i, j | i in s1 && j in s2 :: i <= j
}

/* the same idea, expressed with indices over one common, 
   underlying sequence s */
ghost predicate parted(s: seq<int>, p: nat)
{ forall i:nat, j | i < p <= j < |s| :: s[i] <= s[j] }

/* Proof that these *are* the "same idea" */
lemma seqleq_parted(s:seq<int>, p:nat)
  requires p < |s|
  ensures seqleq(s[..p], s[p..]) <==> parted(s,p)
{
  if seqleq(s[..p], s[p..]) {
    forall i:nat, j | i < p <= j < |s| ensures s[i] <= s[j] {
      assert s[i] in s[..p];
      assert s[j] in s[p..];
    }
  } /* Dafny gets the other direction for free; 
       make sure *you* understand what the "other direction" is! 
    */
}

/* given to you: this method, which finds the index of a smallest 
   element at position p or above.
*/
method sel(a: array<int>, p: nat) returns (q: nat)
  requires p < a.Length
  ensures p <= q < a.Length
  ensures forall i | p <= i < a.Length :: a[q] <= a[i]
{
  q := p;  /* q is our initial "index of smallest so far" */
  var k := p + 1;
  while (k < a.Length)
    invariant k <= a.Length /* counting heuristic */
    /* replace a.Length in ensures clauses with k: ... */
    invariant p <= q < k    
    invariant forall i | p <= i < k :: a[q] <= a[i]
  {
    if (a[k] < a[q]) { q := k; }
    k := k + 1;
  }
}

method sel_srt_incomplete(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var p := 0;
  while (p < a.Length)
    // "the first p are sorted" is the obvious place to start.
    // What else has to hold between the finished part and the 
    // unfinished part?
  {
    var q := sel(a, p);
    a[p], a[q] := a[q], a[p];
    p := p + 1;
  }
}








/* sorted(a[0..p]) alone is not preserved when the next element lands on
   the end, so we need to know that everything in the unprocessed suffix
   is bigger than everything in the prefix (which is also sorted).  The
   permutation invariant is free, because every step is a swap and
   Dafny knows a swap leaves the multiset alone. */
method sel_srt1(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var p:nat := 0;
  while (p < a.Length)
    invariant p <= a.Length
    invariant sorted(a[0..p])
    invariant seqleq(a[..p], a[p..])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var q := sel(a, p);
    // next 3 lines are new proof material
    // want that q >= than everything in a[..p]
    // sel already gives us that q <= everything in a[p..]
    forall i:nat | i < p ensures a[i] <= a[q] {
      assert a[q] in a[p..];
      assert a[i] in a[..p];
    }
    // OR: seqleq_parted(a[..],p);
    a[p], a[q] := a[q], a[p];
    p := p + 1;
  }
}

/* a version using parted instead; Dafny likes this better than the version
   above because it doesn't have to cope with the 'in' clauses of seqleq */
method sel_srt2(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var p:nat := 0;
  while (p < a.Length)
    invariant p <= a.Length
    invariant sorted(a[0..p])
    invariant parted(a[..], p)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var q := sel(a, p);
    a[p], a[q] := a[q], a[p];
    p := p + 1;
  }
}
