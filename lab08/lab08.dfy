/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 8  (Week 10) -- Mostly Sequences, and Proofs About Them
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. YOUR JOB is to fill every hole so 
   the file is error-free: every method defined, every claim checked 
   by Dafny.
*/

/* Q1 */
/* Provide the invariants to make the loop go through */
method minMax(a : seq<int>) returns (mn:int, mx:int)
  requires |a| > 0
  ensures mn in a[..] && mx in a[..]
    /* both of these could also be written with indexes, e.g.:
         forall ix : nat :: ix < |a| ==> a[ix] <= mx
    */
  ensures forall i :: i in a[..] ==> i <= mx
  ensures forall i :: i in a[..] ==> mn <= i
{
    mn, mx := a[0], a[0];
    var i := 1;
    while (i < |a|)
    invariant i <= |a|
    invariant mn in a[..i] && mx in a[..i]
    invariant forall k:nat :: k < i ==> mn <= a[k] <= mx
    {
        if a[i] < mn { mn := a[i]; }
        if a[i] > mx { mx := a[i]; }
        i := i + 1;
    }
}

/* Q2 */
/* A simple array problem: we're updating the array "in place" to 
   make all of its elements 0. The method header needs an addition
   (talk to your tutor), and the loop needs invariants */
method zeroIt(a : array<int>)
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
  modifies a
{
  var i := 0;
  while i < a.Length 
  invariant i <= a.Length
  invariant forall k : nat :: k < i ==> a[k] == 0
  { 
    a[i] := 0; 
    i := i + 1; 
  }
}

// ---------------------------------------------
/* A function used in the rest of the lab, 
   for flipping a sequence: */
function reverse<T>(s : seq<T>) : seq<T>
  // it is useful elsewhere for all callers of reverse to have 
  // this extra fact about reverse available
  ensures |reverse(s)| == |s|
{
    if |s| == 0 then [] 
    else reverse(s[1..]) + [s[0]]
}

/* Q3 */
/* Prove that reverse distributes over sequence-append, as per the 
   statement below, and remember the slogan: "structure of proof is
   reflected in structure of function".  */
lemma reverse_append<T>(s1:seq<T>, s2:seq<T>) 
  ensures reverse(s1 + s2) == reverse(s2) + reverse(s1)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  }else{
    assert reverse(s1 + s2) == reverse((s1 + s2)[1..]) + [(s1 + s2)[0]];
    //assert reverse(s1 + s2) == reverse(s1[1..] + s2) + [s1[0]] ;
    // 윗줄에서 에러떠서 그거 해결
    assert [s1[0]] + (s1[1..] + s2) ==  s1 + s2;

  }
}

/* Q4 */
/* Come up with the universally (forall) quantified statement relating the
   values of a reversed sequence with the original.  Replace the unachievable
   false below with your own statement.

   For example, if we have s == [1,2,3,4], then reverse(s) = [4,3,2,1] and we
   know that element 0 of s is now at position 3 of reverse(s), that element 
   1 of s is at position 2 of reverse(s), all the way up to element 3 of s being
   at position 0 of reverse(s). 

   Generalise this for all possible sequences of any length and state it.
   If you have the statement right, the proof should be automatic, just {} 
*/
lemma reverseIndices<T>(s:seq<T>)
  ensures forall i : nat :: i < |s|==> reverse(s)[i] == s[ |s| - i - 1]
{
}


/* Q5 */
/* Now write a function that adds up all the elements in a 
   sequence */
function sum(s:seq<int>) : int
{
  // this is deliberately bogus and breaks all the lemmas below...
  if s == [] then 0 else s[0] + sum(s[1..])
}

/* these results should follow */
lemma sum123() ensures sum([1,2,3]) == 6 {}
lemma sum_empty() ensures sum([]) == 0 {}


/* Q6 */
/* Prove the following. The empty s1 and non-empty s1 cases will need 
   handling separately.  This hinges on associativity of concatenation
   I expect you will have to make an assertion in that line. */
lemma sumAppend(s1:seq<int>, s2:seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else{
    //assert sum([s1[0]] + (s1[1..] + s2)) == sum(s1 + s2);
    // 윗줄이 실패함
    assert [s1[0]] + (s1[1..] + s2) == s1 + s2;
  }
}

/* Q7 */
/* Prove the following; Dafny gets the s == [] case for free, but the 
   other case will need a call to the sumAppend result.  */
lemma sumReverse(s:seq<int>)
  ensures sum(reverse(s)) == sum(s)
{
  if |s| == 0 {

  } else {
    assert reverse(s[1..]) + [s[0]] == reverse(s);
    //assert sum(reverse(s[1..])) + sum([s[0]]) == sum(reverse(s[1..]) + [s[0]]);
    //윗줄이 실패함
    sumAppend(reverse(s[1..]), [s[0]]);
  }
}


