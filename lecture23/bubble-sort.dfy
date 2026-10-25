/* Lecture 23: bubble sort -- four invariants in the inner loop.
   Ported from COMP1600 2025, week12-code.dfy (bubble, bubble2). */

predicate sorted(s: seq<int>)
{ forall i:nat, j | i < j < |s| :: s[i] <= s[j] }


/* ASCII art for a few repetitions of the inner loop:
   (initial array might have been: [13,1,7,6,..junk..])


step 0:   [ 1, 7, 13, 6, ..junk..]     j == i == 3 
step 1:   [ 1, 7, 6, 13, ..junk..]     j == 2, i == 3
step 2:   [ 1, 6, 7, 13, ..junk..]     j == 1, i == 3
  and then break happens
*/

method bubble_incomplete(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length == 0 { return; }
  var i : nat := 1;
  while (i < a.Length)
    // outer: how much is in order so far?
  {
    var j : nat := i;
    while (j > 0)
      // inner: the element being bubbled is somewhere in the middle
      // of the prefix: there is a sorted part below it, a sorted part 
      // above it, and though the element may be somewhat out of place, 
      // there is a relation BETWEEN those two parts that neither one states.
      // (three invariants here, plus the bound on j)
    {
      if a[j-1] > a[j] { 
        a[j-1], a[j] := a[j], a[j-1]; 
      } else { break; }
      j := j - 1;
    }
    i := i + 1;
  }
}









/* Compare with selection sort: the same specification, a shorter
   program, and four times the annotation.  Worth saying out loud. */
method bubble(a: array<int>)
  modifies a
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  if a.Length == 0 { return; }
  var i : int := 1;
  while (i < a.Length)
    invariant i <= a.Length
    invariant sorted(a[..i])
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j : nat := i;
    while 0 < j 
      invariant j <= i
      invariant sorted(a[..j])
      invariant sorted(a[j..i+1])
      invariant forall u, v :: 0 <= u < j < v < i+1 ==> a[u] <= a[v]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j-1] > a[j] { 
        a[j-1], a[j] := a[j], a[j-1]; 
      } else {break;}
      j := j - 1;
    }
    i := i + 1;
  }
}
