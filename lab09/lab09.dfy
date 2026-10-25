/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 9  (Week 11) -- Arrays and Some Invariants
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. YOUR JOB is to fill every hole so 
   the file is error-free: every method defined, every claim checked 
   by Dafny.

   This lab builds on some results about sequence summing; these are
   at the bottom of the file.
*/

// ------------------------------------------------------------------
/* Q1: Give this method the specification material it needs in order
   to capture that it is setting every element of the array to take
   on the value k
*/

method setToK(a : array<int>, k : int) 
  ensures forall i : nat | i < a.Length :: a[i] == k
  modifies a
{
  var c : nat := 0;
  while c < a.Length 
    invariant c <= a.Length
    invariant forall i : nat | i < c :: a[i] == k
  {
    a[c] := k;
    c := c + 1;
  }
}

// ------------------------------------------------------------------
/* Q2: Give this method the specification *it* needs in order to 
   capture that it is setting every element of the array a to be 
   equal to the first element of the array squared
*/
method setToFirstSquared(a : array<int>)
  modifies a
  requires a.Length > 0
  ensures forall i : nat | i < a.Length :: a[i] == old(a[0] * a[0])
{
  setToK(a, a[0] * a[0]);
}

// ------------------------------------------------------------------
/* Q3: if your setToFirst spec is good enough, the following method should 
   work, but it will need a lemma proved about the sum of a sequence of
   values, all of which are the same...  Prove that below in the lemma
   constantSeqSum, and then use your lemma after the call to 
   setToFirstSquared.
*/
method arrayOfNines() returns (a:array<int>)
  ensures sum(a[..]) == 36
  ensures a.Length == 4
{
  a := new int[4];
  a[0] := -3;
  setToFirstSquared(a);
  constantSeqSum(a[..],9);
  // call constantSeqSum here.
}


/*

function sum(s:seq<int>) : int
{ if s == [] then 0 else s[0] + sum(s[1..])}
*/
/* with the right precondition, this goes through automatically, with the 
  {} proof
*/
lemma constantSeqSum(s : seq<int>, k : int)
  requires forall i : nat | i < |s| :: s[i] == k
  ensures sum(s) == k * |s|
{
}


// ------------------------------------------------------------------
/* Q4: this method changes the array so that its elements are equal
   to the sum of all elements in the array up to that point.  If the
   incoming array has values [1,2,3,4], then it will change to be
   [1,3,6,10]. 
   The lemma sumRight is given in the right place, but you must provide
   the appropriate invariant statements, both about what's changed in 
   the loop so far, and what hasn't...
*/

method prefixSum(a : array<int>)
  modifies a
  ensures forall i :nat :: i < a.Length ==> a[i] == sum(old(a[..i+1]))
{ 
    if a.Length == 0 { return ; }
    var i := 1;
    while i < a.Length 
      invariant i <= a.Length
      invariant forall k : nat :: k < i ==> a[k] == sum(old(a[..k+1]))
      invariant forall j : nat :: i <= j < a.Length ==> a[j] == old(a[j])
    {
      a[i] := a[i] + a[i-1];
      sumRight(old(a[..]), i);
      i := i + 1;
    }
}

/* provided definitions and lemmas about sequence summing... */

function sum(s:seq<int>) : int
{ if s == [] then 0 else s[0] + sum(s[1..])}

lemma sumAppend(s1:seq<int>, s2:seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
    if s1 == [] { 
      assert s1 + s2 == s2; 
    } else {
      assert s1 == [s1[0]] + s1[1..];
      assert [s1[0]] + s1[1..] + s2 == [s1[0]] + (s1[1..] + s2);
    }
}

lemma sumRight(s:seq<int>, i:nat)
  requires i < |s|
  ensures sum(s[..i+1]) == sum(s[..i]) + s[i]
{
  assert s[..i+1] == s[..i] + [s[i]];
  sumAppend(s[..i], [s[i]]);
}
