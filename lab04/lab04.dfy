/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 4  (Week 5) -- Functional Dafny and Proofs
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. Most exercises leave a
   function without a body for you to write; some ask you to add a
   specification (a combination of "requires", "ensures", and 
   "decreases" lines). 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. YOUR JOB is to fill every hole so 
   the file is error-free: every function defined, every claim checked 
   by Dafny.

   This particular lab aims to cover everything we've done so far in 
   the course, giving you a practice version of the mid-semester exam 
   that will happen in week 6.
*/

/********************************************/
/****** Part I : Simple programs and proofs */
/********************************************/

// ******** Q1
/* Complete definition of the daysInMonth function below.

   Use January as month 0, up to December as month 11.
   Use a requires clause to restrict the m parameter to only
   fall into acceptable range.

   The write and prove a lemma stating that your function's 
   outputs all fall into the range 28..31 inclusive.
*/
function daysInMonth(m : nat, isLeapYear : bool) : nat 
  requires m < 12
{
  if m == 1 then (if isLeapYear then 29 else 28)
  else if m == 3 || m == 5 || m == 8 || m == 10 then 30
  else 31
}

lemma daysInMonthOutputOK(m:nat, isLeapYear:bool)
requires m < 12
ensures 25 <= daysInMonth(m,isLeapYear) <= 31
{}


// ******** Q2
/* Complete the function for determining if a year is a leap-year.
   A year y is a leap year if 
   - y is divisible by 4, and 
   - when y is divisible by 100, it's also divisible by 400
*/
predicate isLeapYear(y : nat) {
   if y % 400 == 0 then true
   else if y % 100 == 0 then false
   else if y % 4 == 0 then true
   else false
}

// ******** Q3
/* write the function that for a month number m, and given the 
   information about whether or not it is a leap-year, determines 
   how many days in the year come before the first of that month.

   For example, 
     daysUpToStartOf(0, true) == 0 == daysUpToStart(0, false)
   because there are no days in the year before 1 January, and
   whether or not it is a leap-year makes no difference.

   And
     daysUpToStartOf(3, true) == 91
   because there are 91 days in a leap-year before 1 April
   (31 in January, 29 in February and 31 in March)

   [YOUR FUNCTION WILL BE EASIEST TO WRITE IF IT IS RECURSIVE.]

   Follow up with a lemma checking the daysUpToStartOf(3,true) example.
*/
function daysUpToStartOf (m:nat, isLeapYear : bool) : nat
requires 0 <= m < 12
{
match m case 0 => 0
case _ => daysUpToStartOf(m-1,isLeapYear) + daysInMonth(m-1,isLeapYear)
}

lemma dAprilTrue() 
ensures daysUpToStartOf(3,true) == 91{}

// ******** Q4
/* Using the date datatype below, write the predicate for 
   determining the if one date is earlier in a year 
   than another. 
   I.e., date_lt(d1,d2) is true when d1 is an earlier date
   than d2 
   */
datatype date = D (day : nat, month : nat)
predicate date_lt(d1 : date, d2 : date) {
   if (d2.month == d1.month) then 
      d1.day < d2.day
   else 
      d1.month < d2.month
}

// ******** Q5
/* State and prove the lemma stating that 
     date_lt(12 October, 2 December) 
   is true. 
   (You will need to convert the dates to use the date datatype, with 
    constructor 'D'.)   
*/

lemma twelveOct_lt_twoDec()
ensures date_lt(D(12,9), D(2,11)){}

// ******** Q6
/* State and prove the lemma stating that for a pair of dates d1 and d2, 
   they are either equal or one is less (date_lt) than the other. 
   (Relations satisfying this property are known as "trichotomous".)
*/

lemma date_lt_trichotomy(d1:date, d2:date)
ensures date_lt(d1,d2) || d1 == d2 || date_lt(d2,d1){}


/********************************************/
/****** Part II : Simple requires           */
/********************************************/

/* this and later exercises will use the type of 
   lists with length, append, membership and 
   subset (of int lists) provided for you (along with an 
   important lemma about subset and member):
*/
datatype list<T> = Nil | Cons(hd:T, tl: list<T>)
type ilist = list<int>
predicate member(i : int, l : ilist) {
    match l case Nil => false case Cons(h,t) => i == h || member(i,t)
}
function length<T>(l : list<T>) : nat {
    match l case Nil => 0 case Cons(_, t) => 1 + length(t)
}
function append<T>(l1 : list<T>, l2:list<T>) : list<T> {
    match l1 case Nil => l2 case Cons(h,t) => Cons(h,append(t,l2))
}
predicate subset(l1 : ilist, l2 : ilist) {
    match l1 case Nil => true 
    case Cons(x,xs) => member(x,l2) && subset(xs,l2)
}
lemma subset_member(x:int, A:ilist, B:ilist)
  requires member(x,A) requires subset(A,B)
  ensures member(x,B) {}


// ******** Q7
/* Write a function div12 which divides the first element of a list
   by the second element.   

   Use appropriate preconditions to make this function well-defined.
   HINT: use the .Cons? test in combination with .hd and .tl selectors; 
        OR: use a match-expression (or two?) in your requires clause
*/
function div12(l : ilist) : int
requires l.Cons? && l.tl.Cons?
requires l.tl.hd != 0
{
   l.hd / l.tl.hd
}

// ******** Q8 
/* State and prove the testing lemma
   asserting that div12(Cons(14,Cons(6,Cons(3,Nil)))) == 2 */
lemma testing_div12()
ensures div12(Cons(14,Cons(6,Cons(3,Nil)))) == 2{}

/********************************************/
/****** Part III : List Programming         */
/********************************************/

// ******** Q9
/* Define the interleave function which takes 
   two lists and interleaves them so that 
   elements from each list appear alternating, 
   starting with the first element of the first 
   list.

   E.g., in Haskell notation
     interleave of [1,2,3] [4,5,6] == [1,4,2,5,3,6]
   If the lists are not of equal length, remaining
   elements from the longer list should appear at 
   the end
*/
function interleave<T>(l1 : list<T>, l2 : list<T>) : list<T>
 {
   match l1
   case Nil => l2
   case Cons(x,xs) => match l2 
                      case Nil => l1
                      case Cons(y,ys) => 
                      Cons(x,Cons(y,interleave(xs,ys)))
}

// ******** Q10
/* write a testing lemma for interleave checking 
   the example in the comment above */
lemma testInterleave()
ensures interleave(Cons(1,Cons(2,Cons(3,Nil))),Cons(4,Cons(5,Cons(6,Nil)))) ==
Cons(1,Cons(4,Cons(2,Cons(5,Cons(3,Cons(6,Nil)))))){}

// ******** Q11
/* write and prove the lemma that the length of
   the result of interleaving two lists is the sum
   of the lengths of the lists */
lemma length_interleave<T>(l1:list<T>, l2:list<T>)
ensures length(interleave(l1,l2)) == length(l1) + length(l2){}
// ******** Q12
/* write and prove the lemma stating that if an 
   integer i is in l1, then it is also in the 
   interleave of two lists l1 and l2
*/
lemma member_interleave1(i : int, l1: ilist, l2:ilist)
requires member(i,l1)
ensures member(i,interleave(l1,l2)){}

/********************************************/
/****** Part IV : Termination               */
/********************************************/

// ******** Q13
/* provide the appropriate requires and decreases 
   clauses for the following function, which produces 
   ascending lists of numbers up to some limit */
function upToNList(start: int, end : int) : ilist
requires end >= start
decreases end - start
{
    if start == end then Nil
    else Cons(start, upToNList(start + 1, end))
}

// ******** Q14
/* prove that the length of upToNList(start,end) is
   equal to end - start. */
lemma length_upToNList(start : int, end : int)
requires end >= start
decreases end-start
ensures length(upToNList(start,end)) == end - start{}

/********************************************/
/****** Part V : Trickier Proofs            */
/********************************************/

// ******** Q15
/* Prove that the subset relation is transitive */

lemma subset_transitive(A : ilist, B : ilist, C : ilist)
requires subset(A,B) requires subset(B,C)
ensures subset(A,C)
{
   match A
   case Nil => 
   case Cons(hd,tl) =>{subset_member(hd,B,C);}
}

// ******** Q16
/* Prove that if A and B are subsets of each other, then
   i is a member of A iff it is a member of B */
lemma subset_antisym(i : int, A : ilist, B : ilist)
requires subset(A,B) requires subset(B,A)
ensures member(i,B) == member(i,A)
decreases A
{  
   if member(i,A) {subset_member(i,A,B);}
   if member(i,B) {subset_member(i,B,A);}
}


/********************************************/
/****** Part VI : Quantifiers               */
/********************************************/

// ******** Q17
/* this function returns the nth element of a list
   Add the requires clause that we need to make
   Dafny happy */
function nth<T>(n : nat, l : list<T>) : T
requires n < length(l) 
{
    match l 
    case Cons(h,t) => if n==0 then h else nth(n-1,t)
}

// ******** Q18
/* prove the following result; that an integer i is a 
   member of l iff there's an index n such that nth(n,l) == i
*/
lemma member_nth(i:int, l : list<int>)
  ensures member(i, l) <==> exists n : nat | n < length(l) :: nth(n,l) == i
  {
   if member(i,l) {
      match l case Cons(j,js) => {
        if i == j {
          assert nth(0,l) == i;
        } else {
          assert member(i,js);
          var n0:nat :| n0 < length(js) && nth(n0,js) == i;
          assert nth(n0 + 1, l) == i;
          assert n0 + 1 < length(l);
          assert exists n : nat | n < length(l) :: nth(n,l) == i;
        }
      } 
   }
}

// ***** Feedback *****
// Please rate the following course activities in terms of usefulness to you, 
// where 1 is not useful at all, and 10 is extremely useful:
//
// ** Lectures : 
// ** Lab-work : 
// ** Lab-dropin (last half hour of each lab):
//
// One sentence: what is the best part of this course?
//
// ...
//
// One sentence: what is the worst part of this course?
//
// ...