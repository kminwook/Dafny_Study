/* Lecture 21, level 2: the invariant about what we have NOT done.
   Ported from COMP1600 2025, week12-code.dfy (inc, inc2).

   The failure below is the point of the example, so run it before
   changing anything. */

method inc_incomplete(a: array<int>)
  modifies a
  ensures forall i:nat | i < a.Length :: a[i] == old(a[i]) + 1
{
  var i := 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall j:nat | j < i :: a[j] == old(a[j]) + 1
    // the same recipe as level 1's ‘zero’`, but it is not enough.
    // read the complaint: which of the three questions failed?
    // then ask what we need to know about a[i] JUST BEFORE we
    // increment it -- and who was supposed to tell us.
  {
    a[i] := a[i] + 1;
    i := i + 1;
  }
}









/* With a mutable structure (the array) the verifier will not 
   assume that the bit you have not reached is untouched.  
   
   You have to say so. */
method inc(a: array<int>)
  modifies a
  ensures forall i:nat | i < a.Length :: a[i] == old(a[i]) + 1
{
  var i:nat := 0;
  while i < a.Length
    invariant i <= a.Length
    invariant forall j:nat | j < i :: a[j] == old(a[j]) + 1
    invariant forall j | i <= j < a.Length :: a[j] == old(a[j])
      /* ^--- later bits still the same as before ---^ */
  {
    a[i] := a[i] + 1;
    i := i + 1;
  }
}
