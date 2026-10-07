/* Lecture 16: counting + computing.
   Ported from COMP1600 2025, week10-code.dfy (mult). */

method mult(m: int, n: nat) returns (r: int)
  ensures r == n * m
{
  var x: int;
  r, x := 0, 0;
  while (x < n)
    invariant x <= n     // counting
    invariant r == x * m  // computing
  {
    x := x + 1;
    r := r + m;
  }
  assert x == n; //invariant && !gd
  assert r == m * x; //invariant
  assert r == m * n; //substitute one into the other
}

/* Try deleting each invariant in turn, and read the complaint. */
