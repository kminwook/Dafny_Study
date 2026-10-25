/* Lecture 21, level 1: the postcondition, cut off at i.
   Ported from COMP1600 2025, week12-code.dfy (zero, zero2). */

method zero_incomplete(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
{
  var i : int := 0;
  while (i < a.Length)
    // the postcondition talks about the whole array.
    // in here we have only got as far as i ...
  {
    a[i] := 0;
    i := i + 1;
  }
}









/* Nothing is new except `modifies a': the postcondition never
   mentions what the array used to hold. */
method zero(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
{
  var i : int := 0;
  while (i < a.Length)
    invariant i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1;
  }
}
