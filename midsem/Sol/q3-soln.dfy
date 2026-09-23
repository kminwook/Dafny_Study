/* MID-SEMESTER EXAM 2026: Question 3.  

   10 marks in total

   All students to answer all questions. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to 
   have a proof.  Remember to include the {} and any 
   necessary proof-steps within the braces !
*/


include "core-list.dfy"

/* 3A.

   Define the function that checks whether or not every 
   element of a list of integers (an "ilist") is even 

   1 mark.
*/
predicate listIsAllEven(l : ilist)
{
    match l case Nil => true
    case Cons(j,js) => j % 2 == 0 && listIsAllEven(js)
}

/* 3B. 
 
   Prove the testing lemma stating that the list containing 
   2 and 4, in that order, is all even.

   1 mark
*/
lemma list24_isAllEven() 
  ensures listIsAllEven(Cons(2, Cons(4, Nil))) {}

/* 3C. 

   Define the function that returns, in order, the 
   list of all elements from the input list l that are 
   even.

   1 mark
*/
function filterEvens(l:ilist) : ilist
{
    match l case Nil => Nil
    case Cons(j,js) => if j % 2 == 0 then Cons(j,filterEvens(js))
    else filterEvens(js)
}

/* 3D.

   Prove the testing lemma that states that filterEvens on the 
   list containing 2, 3, and 4, in that order returns the list
   containing just 2 and 4, in that order.

   1 mark
*/
lemma test_filterEvens234()
  ensures filterEvens(Cons(2,Cons(3, Cons(4,Nil)))) == 
        Cons(2, Cons(4, Nil)) {}

/* 3E.

   State and prove the lemma that if a list is all evens, then
   filterEvens on that list just returns the same list

   2 marks
*/
lemma filterEvens_onAllEvensUnchanged(l:ilist)
  requires listIsAllEven(l)
  ensures filterEvens(l) == l
{}

/* 3F.

   State and prove the lemma that filterEvens on a list always
   returns a list that has length less-than or equal to the length
   of the input.

   2 marks
*/
lemma length_filterEvens(l:ilist)
  ensures length(filterEvens(l)) <= length(l) {}

/* 3G.

   State and prove the lemma that if a list is not all evens,
   then filterEvens on that list returns a result that is shorter
   than the input.  HINT: use the length_filterEvens result.

   2 marks
*/
lemma filterEvens_onNotAllEvensShorter(l:ilist)
  requires !listIsAllEven(l)
  ensures length(filterEvens(l)) < length(l)
{
    match l case Nil => {}
    case Cons(j,js) => {
            length_filterEvens(js);
    }
}