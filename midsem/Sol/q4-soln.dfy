/* MID-SEMESTER EXAM 2026: Question 4.  

   10 marks in total

   All students to answer all questions. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to 
   have a proof.  Remember to include the {} and any 
   necessary proof-steps within the braces !

   The functions member and reverse from core-list.dfy
   are particularly relevant in this question.
*/

include "core-list.dfy"

function max(i:int, j:int) : int { if i < j then j else i }

/* 4A.

   Define the function that returns the maximum element of a 
   list of integers. Use a precondition to require that your 
   function is not called on an empty list. You may use the 
   max function above if desired.

   2 marks
*/
function maxList(l : ilist) : int
  requires !l.Nil?
{
   match l case Cons(j,Nil) => j
   case Cons(j,js) => max(j,maxList(js))
}

/* 4B. 
  
   State and prove the testing lemma stating that maxList of the
   value l123321, given below, is equal to 3

   1 mark
*/
const l123321 := 
  Cons(1, Cons(2, Cons(3, Cons(3, Cons(2, Cons(1,Nil))))))

lemma maxList_l123321()
  ensures maxList(l123321) == 3 {}

/* 4C. 

   State and prove that the max element of a non-empty list is a
   member of that list

   2 marks
*/
lemma maxList_member(l:ilist)
  requires !l.Nil?
  ensures member(maxList(l), l)
{}

/* 4D.

   State and prove that if i is a member of an ilist, then it is
   less-than or equal to the max value of that list

   2 marks
*/
lemma maxList_maximal(i:int, l:ilist)
  requires member(i,l)
  ensures i <= maxList(l)
{}

/* 4E. 

   State and prove that if l is a non-empty ilist, then the maximum
   of the reverse of the list is the maximum of the original list

   You will need to state, prove and use an auxiliary result along the 
   way to get this result to come out.

   3 marks
*/

lemma maxList_append(l1: ilist, l2:ilist)
  requires !l1.Nil? requires !l2.Nil?
  ensures maxList(append(l1,l2)) == max(maxList(l1), maxList(l2))
  {}

lemma maxList_reverse(l:ilist)
  requires !l.Nil? 
  ensures maxList(reverse(l)) == maxList(l)
{
   match l case Cons(j,Nil) => {}
   case Cons(j,js) => {
      maxList_append(reverse(js), Cons(j,Nil));
   }
}