/* This is a very "maths-y" example; next one will be 
   more Computer Science... */

ghost predicate divides(m:nat, n:nat)
{
    // "ghost" means we (don't want to/can't) run this as code
    exists q:nat :: q * m == n
}

lemma divides_transitive(m:nat, n:nat, p:nat)
  requires divides(m,n)
  requires divides(n,p)
  ensures divides(m,p)
  {
    var q1 :| q1 * m == n;
    var q2 :| q2 * n == p;
    assert p == q2 * q1 * m;
  }
