/* MID-SEMESTER EXAM 2026: Question 5.  

   10 marks in total

   All students to answer all questions. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched (exception:
   question 5E requires you to tweak an existing piece of 
   text).

   Remember that when asked to prove a lemma, you need to 
   have a proof.  Remember to include the {} and any 
   necessary proof-steps within the braces !

   The functions take and drop from core-list.dfy
   are particularly relevant in this question.
*/

include "core-list.dfy"

/* 5A.

   Define the function div3List which takes a list of 
   integers and returns a new list where each element 
   of the original has been divided by 3. (This is integer
   division represented by the '/' operator.)
   
   1 mark
*/

function div3List(l : ilist) : ilist{
   match l
   case Nil => Nil
   case Cons(x,xs) => Cons(x/3,div3List(xs))
}
/* YOUR WORK GOES HERE */

/* 5B. 

   State and prove the testing lemma stating that the
   div3List function applied to elements 1 .. 6 returns
   the list 0,0,1,1,1,2.

   1 mark.
*/
const l123456 : ilist := 
  Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Cons(6,Nil))))))
lemma div3_123456()
ensures div3List(l123456) == Cons(0,Cons(0,Cons(1,Cons(1,Cons(1,Cons(2,Nil)))))){}
/* YOUR WORK GOES HERE */

/* 5C.

   State and prove the lemma stating that the length of 
   div3List(l) is equal to the length of l.

   1 mark.
*/
lemma length_div3List(l:ilist)
ensures length(l) == length(div3List(l)){}
/* YOUR WORK GOES HERE */

/* 5D.

   State and prove the lemma stating an integer i is a 
   member of div3List(l) iff there exists a member of l 
   which when divided by 3 is equal to i.

   4 marks
*/
lemma member_div3(i:int, l : ilist)
ensures exists x : int | member(x,l) :: member(x/3,div3List(l)) 

/* YOUR WORK GOES HERE */

/* 5E. 

   Give the sumInThrees function below a termination argument
   so that Dafny accepts it, proving any necessary lemmas 
   along the way.  (take and drop come from core-list.dfy)

   In other words: the definition of sumInThrees is broken 
   because Dafny cannot prove that it terminates.
   Write the necessary changes so it becomes something that 
   Dafny accepts, while preserving the intended behaviour: 
   test-cases for that intended behaviour include (using 
   Haskell notation):
     sumInThrees [1,2,3] == [6]
     sumInThrees [1,2,3,4] == [6,4]
     sumInThrees [] == [0]
     sumInThrees [4,5,6,1,2,3,10] == [15,6,10]

   There is no /* YOUR WORK GOES HERE */ tag in this question,
   you should fix sumInThrees "in place".

   3 marks
*/    
function sumInThrees(l:ilist) : ilist
{
    if length(l) <= 3 then Cons(sumList(l), Nil)
    else Cons(sumList(take(3,l)), sumInThrees(drop(3,l)))
}

/* auxiliary used above */
function sumList(l:ilist) : int
{
    match l case Nil => 0 case Cons(j,js) => j + sumList(js)
}
