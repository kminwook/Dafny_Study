/* MID-SEMESTER EXAM 2026: Question 2.  

   10 marks in total

   All students to answer all questions. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to 
   have a proof.  In this question, if your definition of
   mt_lt below is correct, all proofs will be immediate; 
   just remember to include the {} !
*/

datatype medal_tally = MT(golds: nat, silvers:nat, bronzes:nat)

/* 2A.
   Define the "standard" newspaper-reporting ordering on 
   medal tallies, where golds are most significant, and 
   bronzes the least.  This is with predicate mt_lt(mt1,mt2)
   which returns true if tally mt1 is strictly less-than/worse
   than mt2. This is a lexicographic ordering, and (HINT), 
   your predicate can be naturally expressed with a boolean
   expression with 3 disjuncts.

   1 mark
*/
predicate mt_lt(mt1:medal_tally, mt2:medal_tally){
   if mt2.golds > mt1.golds then true
   else if mt2.silvers > mt1.silvers then true
   else if mt2. bronzes > mt1.bronzes then true
   else false
}
/* YOUR WORK GOES HERE */

/* 2B.

   State and prove the testing lemma that 
      3 golds, 2 silvers and 10 bronzes 
   is less-then
      3 golds, 3 silvers and 2 bronzes

   1 mark
*/
lemma t3_2_10__lt__3_3_2()
ensures mt_lt(MT(3,2,10),MT(3,3,2)){}
/* YOUR WORK GOES HERE */

/* 2C.

   State and prove the fact that a medal-tally is never less-than
   itself.  (It is "irreflexive".)

   2 marks
*/
lemma mt_lt_irreflexive(mt:medal_tally)
ensures !mt_lt(mt,mt){}
/* YOUR WORK GOES HERE */

/* 2D.

   State and prove the result that it is impossible for a pair
   of medal-tallies to both be less than each other.

   2 marks
*/
lemma mt_lt_antisym(mt1:medal_tally, mt2:medal_tally)
ensures mt_lt(mt1,mt2)
/* YOUR WORK GOES HERE */

/* 2E.

   State and prove that given a pair of tallies, mt1 and mt2,
   one must be less than the other, or they must be equal

   2 marks
*/
lemma mt_lt_trichotomous(mt1:medal_tally, mt2:medal_tally)
ensures mt_lt(mt1,mt2) || mt_lt(mt2,mt1) || mt1 == mt2 {}

/* YOUR WORK GOES HERE */

/* 2F.

   Figure out the smallest possible medal-tally, and prove
   that it is either less than or equal to all possible 
   medal tallies.

   2 marks
*/

lemma mt_lt_least(mt:medal_tally)

/* YOUR WORK GOES HERE */

/* use an auxiliary definition of this shape, if you wish: */

// const smallest_tally : medal_tally := ???

/* 
To do so, uncomment the const-line above and fill in the 
appropriate value, and then use that value in the lemma 
statement.

WARNING: if you uncomment the const-line, you must replace 
??? with an actual value — leaving ??? in place will stop 
the whole file from verifying
*/
