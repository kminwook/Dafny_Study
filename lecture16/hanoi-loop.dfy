/* Lecture 16: the lecture-13 bridge.
   hanoi2 is lecture 13's accumulator version, unchanged. */

function f(i:int) : int

method find_max(lo : int, hi:int) returns(max:int)
requires lo <= hi
ensures forall j :: lo <= j <= hi ==> f(j) <= f(max)
ensures lo <= max <= hi
{
  max := lo;
  var i := lo;
  while i < hi
  invariant i <= hi
  invariant forall j :: lo <= j <= i ==> f(j) <= f(max)
  invariant lo <= max <= hi 
  {
    i := i +1;
    if f(i) > f(max){max := i;}
  }
  assert i == hi;
}

function hanoi1(n: nat) : nat { if n == 0 then 0 else 1 + 2 * hanoi1(n-1) }

function hanoi2(n: nat, a: nat) : nat
{ if n == 0 then a else hanoi2(n-1, 2*a + 1) }

method hanoi2loop(n0: nat) returns (a: nat)
  ensures a == hanoi2(n0, 0)
{
  var n :nat := n0;
  a := 0;
  while n > 0
    //invariant 0 <= n
    invariant hanoi2(n,a) == hanoi2(n0,0)
  {
    assert n != 0;
    assert hanoi2(n,a) == hanoi2(n0,0);
    assert hanoi2(n,a) == hanoi2(n-1,2*a + 1);
    n := n - 1;
    a := 2*a + 1;
    assert hanoi2(n,a) == hanoi2(n0,0);
  }
  assert n == 0;
  assert hanoi2(n,a) == a;
  assert hanoi2(n,a) == hanoi2(n0,0);
}


lemma hanoi_gen(n: nat, a: nat)
  ensures hanoi2(n, a) == hanoi1(n) + a*(hanoi1(n) + 1)
{}

lemma hanoi12(n: nat)
  ensures hanoi1(n) == hanoi2(n, 0)
{ hanoi_gen(n, 0); }

/* and hence, via lecture 13's hanoi_gen: */
method hanoi1loop(n0: nat) returns (a: nat)
  ensures a == hanoi1(n0)
{
  a := hanoi2loop(n0);
  assert a == hanoi2(n0,0);
  hanoi12(n0);
  assert hanoi2(n0,0) == hanoi1(n0);
}
