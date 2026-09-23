/* MID-SEMESTER EXAM 2026: Question 1.  

   10 marks in total

   All students to answer all questions. 

   Replace /* YOUR WORK GOES HERE */ comments with your 
   work.  Leave everything else untouched.

   Remember that when asked to prove a lemma, you need to 
   have a proof; sometimes {} will be enough, sometimes not,
   but remember to always include the {}!

*/

datatype traffic_light = Red | Orange | Green

/* 1A. 
   Define the next_colour function with signature below so it 
   returns the next colour after the input in the the standard
   sequence of traffic light changes:
      red -> green 
      green -> orange
      orange -> red

   1 mark
*/

function next_colour(c : traffic_light) : traffic_light{
   match c
   case Red => Green
   case Green => Orange
   case Orange => Red
}
/* YOUR WORK GOES HERE */


/* 1B. 
   State and prove the lemma saying that 
   Red's next colour is Green.
   
   1 mark
*/
lemma reds_next_colour()
ensures next_colour(Red) == Green{}
/* YOUR WORK GOES HERE */ 

/* 1C. 
   Define the n_step version of the above. This function takes 
   n, a natural number, and c, a colour, and returns the result
   of taking the next_colour n times. E.g., 
     n_step(3, Red) == Red and n_step(2, Red) == Orange

   2 marks
*/
function n_step(n : nat, c : traffic_light) : traffic_light
{
   if n == 0 then  c 
   else n_step(n-1,next_colour(c))

}
/* YOUR WORK GOES HERE */

/* 1D.
   State and prove that the result of n_step(m+n,c) is 
   the same as n_step(m, n_step(n, c))

   2 marks
*/
lemma n_step_sum(m:nat, n : nat, c:traffic_light)
ensures n_step(m+n,c) == n_step(m,n_step(n,c)){}
/* YOUR WORK GOES HERE */

/* 1E. 
   State and prove that n_step(3,c) is always just c

   1 mark
*/
lemma n_step3(c:traffic_light)
ensures n_step(3,c) == c{}
/* YOUR WORK GOES HERE */

/* 1F. 
   State and prove that n_step(3 * n, c) is always just c
   You will need to use the n_step_sum result from above.

   3 marks
*/
lemma n_step3n(n:nat, c:traffic_light)
ensures n_step(3*n,c) == c

/* YOUR WORK GOES HERE */
