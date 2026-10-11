/* Lecture 17: "the answer we want is the answer to what is left".
   Ported from COMP1600 2025, tutorial 9 exercise 5. */

function euclid(n: nat, m: nat) : nat
  requires m <= n
{ if m == 0 then n else euclid(m, n % m) }

method gcd(n: nat, m: nat) returns (g: nat)
  requires m <= n
  ensures g == euclid(n, m)
{
  var f: nat;
  f, g := m, n;
  while (0 < f) 
    invariant f <= g
    // invariant g == euclid(g,f)  이건 g 가 변화하기도 하니까 루프 끝날때만 참이다
    //dafny 는 중간것도 막 들어가는데 그때 g 는 기존값이니까 틀리는경우가 생기지 그래서 변치 않는 euclud(n,m) 으로비교
    invariant euclid(n,m) == euclid(g,f)
  {
    g, f   :=   f, g % f;
  }
  assert f == 0;
  assert g == euclid(g,f);
}
