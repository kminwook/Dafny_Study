datatype traffic_light = Red | Orange | Green

/* 1A. 
   Define the next_colour function with signature below so it 
   cycles through the standard sequence of traffic light changes:
   red -> green -> orange -> red -> ...

   1 mark
*/

function next_colour(c : traffic_light) : traffic_light
{
   match c case Red => Green case Green => Orange 
   case Orange => Red
}

/* 1B. 
   Write the lemma stating that Red's next colour is Green.
   
   1 mark
*/
lemma reds_next_colour()
  ensures next_colour(Red) == Green {}

/* 1C. 
   Define the n_step version of the above. This function takes 
   n, a natural number, and c, a colour, and returns the result
   of taking the next_colour n times. E.g., 

     n_step(3, Red) == Red, and n_step(2, Red) == Orange.

   2 marks
*/
function n_step(n : nat, c : traffic_light) : traffic_light
{
   if n == 0 then c else n_step(n-1, next_colour(c))
}

/* 1D.
   State and prove that the result of n_step(m+n,c) is 
   the same as n_step(m, n_step(n, c))

   2 marks
*/
lemma n_step_sum(m:nat, n : nat, c:traffic_light)
  ensures n_step(m+n,c) == n_step(m, n_step(n, c))
{
}

/* 1E. 
   State and prove that n_step(3,c) is always just c

   1 mark
*/
lemma n_step3(c:traffic_light)
  ensures n_step(3, c) == c {}

/* 1F. 
   State and prove that n_step(3 * n, c) is always just c
   You will need to use the n_step_sum result from above.

   3 marks
*/
lemma n_step3n(n:nat, c:traffic_light)
  ensures n_step(3 * n, c) == c 
{
  if n == 0 {}
  else { n_step_sum(3*(n-1), 3, c); }
}