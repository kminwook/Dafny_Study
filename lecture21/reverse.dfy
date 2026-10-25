/* Lecture 21, level 3: two ends done, the middle untouched.

   Reversing in place.  Apply both earlier lessons mechanically and
   see which one breaks. */

function seq_reverse<T>(s : seq<T>) : seq<T>
  ensures |seq_reverse(s)| == |s|
{
  if |s| == 0 then s else seq_reverse(s[1..]) + [s[0]]
}

lemma reverse_by_indexes<T>(s:seq<T>)
  ensures forall k : nat | k < |s| :: seq_reverse(s)[k] == s[|s| - 1 - k]
{
}

method reverse_incomplete(a: array<int>)
  modifies a
  ensures forall k:nat | k < a.Length :: a[k] == old(a[a.Length - 1 - k])
{
  var i := 0;
  while (i < a.Length / 2)
    invariant 0 <= i <= a.Length / 2
    invariant forall k:nat | k < i :: a[k] == old(a[a.Length-1-k])
    invariant forall k | i <= k < a.Length :: a[k] == old(a[k])
    // Level 1's recipe for the part we have done; 
    // Level 2's for the part we have not.  
    // One of these is now false: which? (squiggles give it away :-), 
    // but WHY?
    // (hint: how many elements does one iteration change?)
  {
    a[i], a[a.Length-1-i] := a[a.Length-1-i], a[i];
    i := i + 1;
  }
}









/* The array has three regions, not two: done at the front, done at
   the back, untouched in the middle.  Delete any one of the three
   quantified invariants and verification fails.

   Nothing explicitly says what happens to the middle element of an
   odd-length array: the "untouched" invariant covers it, because
   that element is its own mirror image. */
method reverse(a: array<int>)
  modifies a
  ensures forall k:nat | k < a.Length :: a[k] == old(a[a.Length-1-k])
{
  var i := 0;
  while (i < a.Length / 2)
    invariant 0 <= i <= a.Length / 2
    invariant forall k:nat | k < i :: a[k] == old(a[a.Length-1-k])
    invariant forall k | a.Length-i <= k < a.Length :: a[k] == old(a[a.Length-1-k])
    invariant forall k | i <= k < a.Length-i :: a[k] == old(a[k])
  {
    a[i], a[a.Length-1-i] := a[a.Length-1-i], a[i];
    i := i + 1;
  }
}
