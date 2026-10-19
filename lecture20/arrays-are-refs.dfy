/* Lecture 20: aliasing, and what equality means.
   Ported from COMP1600 2025, week12-code.dfy (m, eq). */

method aliasing()
{
  var a : array<int> := new int[20];
  a[0] := 12;
  var b : array<int> := a;      /* NOT a copy */
  assert b[0] == 12;
  a[0] := 17;                   /* changes b as well */
  assert b[0] == 17;
  b[1] := 3;
  assert a[1] == 3;
}

method equality(c : array<int>)
{
  var a : array<int> := new int[3]; a[0], a[1], a[2] := 0, 1, 10;
  var b : array<int> := new int[3]; b[0], b[1], b[2] := 0, 1, 10;
  assert a != b;                /* same contents, different arrays */
  assert a[..] == b[..];        /* ... but the same contents */
  b[2] := 11;
  assert a[..2] == b[..2];        /* ... but the same contents */
  assert a[..] == [0,1,10];
  assert b[..] == [0,1,11];
  assert [0,1,11][2 := 10] == [0,1,10];
  assert (b[..])[2 := 10] == a[..];
  b := a;
  assert a == b;
  a[0] := 17;
  assert b[0] == 17;
  b[1] := 3;
  assert a[1] == 3;
}

method changing_arrays(a:array<int>)
  requires a.Length > 0
  modifies a
{
  var b := a;
  b[0] := 3;
}