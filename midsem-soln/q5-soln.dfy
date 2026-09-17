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

/* 5A.

   Define the function div3List which takes a list of 
   integers and returns a new list where each element 
   of the original has been divided by 3. (This is integer
   division represented by the '/' operator.)
   
   1 mark
*/

function div3List(l : ilist) : ilist
{
    match l case Nil => Nil
    case Cons(j,js) => Cons(j/3, div3List(js))
}

/* 5B. 

   State and prove the testing lemma stating that the
   div3List function applied to elements 1 .. 6 returns
   the list 0,0,1,1,1,2.

   1 mark.
*/
const l123456 : ilist := 
  Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Cons(6,Nil))))))
lemma div3_123456()
  ensures div3List(l123456) == 
          Cons(0,Cons(0,Cons(1,Cons(1,Cons(1,Cons(2,Nil))))))
{}

/* 5C.

   State and prove the lemma stating that the length of 
   div3List(l) is equal to the length of l.

   1 mark.
*/
lemma length_div3List(l:ilist)
  ensures length(div3List(l)) == length(l) {}

/* 5D.

   State and prove the lemma stating an integer i is a 
   member of div3List(l) iff there exists a member of l 
   which when divided by 3 is equal to i.

   4 marks
*/
lemma member_div3(i:int, l : ilist)
  ensures member(i,div3List(l)) <==> 
          exists j | member(j,l) :: j / 3 == i
{
    match l case Nil => 
    case Cons(j,js) => {
        if i == j / 3 {
            assert member(i,div3List(l));
            assert member(j,l);
            assert exists j | member(j,l) :: j / 3 == i;
        } else {
            if member(i, div3List(js)) {
                var j0 :| member(j0,js) && j0 / 3 == i;
                assert member(j0,l);
                assert exists j | member(j,l) :: j / 3 == i;
            }
        }
    }
}

/* 5E. 

   Give the sumInThrees function below a termination argument
   so that Dafny accepts it, proving any necessary lemmas 
   along the way.  (take and drop come from core-list.dfy)

   3 marks
*/
function sumList(l:ilist) : int
{
    match l case Nil => 0 case Cons(j,js) => j + sumList(js)
}

lemma length_drop(n:nat, l:ilist)
  requires n <= length(l)
  ensures length(drop(n,l)) == length(l) - n {}

function sumInThrees(l:ilist) : ilist
  decreases(length(l))
{
    if length(l) <= 3 then Cons(sumList(l), Nil)
    else length_drop(3,l);
         Cons(sumList(take(3,l)), sumInThrees(drop(3,l)))
}

