/* MID-SEMESTER EXAM 2026: Question 6.  

   5 marks in total

   This question is only for COMP6260 students. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to 
   have a proof.  Remember to include the {} and any 
   necessary proof-steps within the braces !

*/

ghost predicate divides(m:nat, n:nat)
{
    exists q : nat :: q * m == n
}

/* 6A. 

   Prove that the divisibility relation, defined above is 
   reflexive: i.e., any natural number n divides itself.

   2 marks
*/
lemma divides_refl(n:nat)
  ensures divides(n,n)
{
    assert 1 * n == n;
}

/* 6B.

   Prove that the divisibility relation is transitive. 
   In other words, if m divides n, and n divides p, then 
   m also divides p.

   3 marks
*/
lemma divides_trans(m:nat, n:nat, p:nat)
  requires divides(m,n) requires divides(n,p)
  ensures divides(m,p)
{
        var q1 :nat :| q1 * m == n;
        var q2 :nat :| q2 * n == p;
        assert p == q2 * n;
        assert n == q1 * m;
        assert p == q2 * (q1 * m);
        assert p == (q2 * q1) * m;
        assert exists q :nat :: q * m == p;
}