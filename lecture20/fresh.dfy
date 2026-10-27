/* Lecture 20: fresh, and why a new array needs no modifies.
   Ported from COMP1600 2025, week12-code.dfy (n, mod_id). */

method mkfresh(a: array<int>) returns (b: array<int>)
  ensures b.Length > 0
  ensures fresh(b)
  ensures a.Length > 0 ==> b[0] == a[0] 
{ b := new int[42]; 
  if a.Length > 0 { b[0] := a[0]; }
}

/* no modifies clause needed: b is fresh, so it is nobody else's */
method use_it(a: array<int>) returns (c:array<int>)
  requires a.Length > 0
  ensures c.Length > 0
  ensures fresh(c)
{
  c := mkfresh(a);
  c[0] := 15;
  //c := a;
}















method use_itagain(a:array<int>, b:array<int>) returns (i:int)
  requires a.Length > 0 && b.Length > 0 //&& a != b
  modifies b
{
  var c : array<int> := use_it(b); // when i have fresh(output) in ensures,
  //that's like having  written output := new ... at this level
  c[0] := 1;
  return 3;
}