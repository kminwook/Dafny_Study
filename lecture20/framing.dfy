/* Lecture 20: modifies governs the OBJECT, not the NAME.
   Ported from COMP1600 2025, week12-code.dfy (nuke0, nuke1). */

method nuke0(a: array<int>) returns (i:int)
  requires a.Length > 0
  modifies a
{ a[0] := 3; 
  i := 0;
  if a.Length > 1 { i := a[1]; }
}

method nuke1(a: array<int>, b: array<int>)
  requires a.Length > 1 && b.Length > 1
  modifies a
{
  if a == b { 
    b[1] := 0;      /* legal: here b IS a */
    // important consquences!
    var c : array<int> := b;
    c[1] := 10;
    assert a == b;      // even though we changed b and not a ?!
    assert a[1] == 10;   // actually a changed too
  } else {
    var c : array<int> := b;
    c[1] := 3;
    if a[0] != b[0] && a.Length == 1 && b.Length == 1
    {
      // a and b have one element each, but are different
      // arrays. Let's make those elements the same:
      a[0] := b[0];

      // yet a is still NOT the same array as b:
      assert a != b;

      // they have the same sequence of values:
      assert a[..] == b[..]; 
    }
  }


  var c : array<int> := new int[20];
  c[1] := 42;                  /* legal: c is fresh */
  c := b; 
  //c[0] := 7;                 /* ILLEGAL: b is not in modifies */
}

/* reads, for functions and predicates that look at the heap */
predicate sorted(a: array<int>)
  reads a
{ forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }
