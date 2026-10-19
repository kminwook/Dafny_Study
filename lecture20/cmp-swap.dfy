/* Lecture 20: saying "and I did not touch anything else".
   Ported from COMP1600 2025, week12-code.dfy (cmp_swp .. cmp_swp3). */

/* Swap a[i] and a[j] if they are the wrong way round.
   This specification is true -- and far too weak.  The body below is
   allowed to zero the whole array instead, and still satisfy it. */
method cmp_swp_incomplete(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] <= a[j]
  // what ELSE do we want to promise?  two sorts of answer:
  //   - something about the two elements we touched, and
  //   - something about the array as a whole.
  // (the second one is the one that will scale to sorting)
{
  if (a[i] > a[j]) { a[i], a[j] := a[j], a[i]; }
  /* 
  var c := 0;
  while c < a.Length 
    invariant c <= a.Length
    invariant forall c0 :: 0 <= c0 < c ==> a[c0] == 0
  { a[c] := 0; c := c + 1; }
  */
}









/* Attempt: ghost variables can see the old values, but they live in
   the body, and the specification is where we need them. */
method cmp_swp_ghost(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] <= a[j]
{
  ghost var ai := a[i];
  ghost var aj := a[j];
  if (a[i] > a[j]) { a[i], a[j] := a[j], a[i]; }
  assert a[i] == ai || a[i] == aj;
}

/* old() is how you say it in the specification */
method cmp_swp2(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] <= a[j]
  ensures a[i] == old(a[i]) || a[i] == old(a[j])
{
  if (a[i] > a[j]) { a[i], a[j] := a[j], a[i]; }
}

/* and the idiom that scales: same elements, rearranged */
method cmp_swp3(a: array<int>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] <= a[j]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if (a[i] > a[j]) { a[i], a[j] := a[j], a[i]; }
}

/* A trap worth showing: old(a) is the old REFERENCE, which is the
   same reference, so this ensures clause says nothing at all. */
method oldref(a: array<int>, i: int)
  requires a.Length > 0
  modifies a
  ensures old(a)[0] == a[0]
{
  a[0] := a[0] + 1;
}
