/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 6  (Week 8) -- Loop Invariants Every Which Way
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. YOUR JOB is to fill every hole so 
   the file is error-free: every method defined, every claim checked 
   by Dafny.
*/

// ******** Q1
/* Fix the invariant and final assertion (only; don't touch the code)
   so that the method is accepted by Dafny, and you have a final
   assertion of the form j == <somenumber>
*/
method nine () {
    var j : int := 9;
    var i : int := 0;
    while i < 10
      invariant j == 9 - i
    {
        j := j - 1;
        i := i + 1;
    }
    assert j == -1;
}


// ******** Q2
/* Add invariant(s) to the loop so that this function verifies */
method multiply_via_addition(m : nat, n:nat) returns (r:nat)
  ensures r == m * n
{
    var c := 0;
    r := 0;
    while c < n 
      invariant c <= n
      invariant r == m * c
    {
        r := r + m;
        c := c + 1;
    }
}

// ******** Q3
/* Add invariant(s) to the loop so that the function verifies.
   The definition of factorial follows the method */
method factM(n:nat) returns (r:nat)
  ensures r == factorial(n)
{
  var c := 0;
  r := 1;
  while c < n 
    invariant c <= n
    invariant r == factorial(c)
  {
    c := c + 1;
    r := c * r;
  }
}

function factorial(n:nat) : nat
{
    if n == 0 then 1 else n * factorial(n-1)
}

// ******** Q4
/* Implement a while-loop version of factorial again, but this time, have your 
   loop initialise its counter to n, and count downwards. The code below shows
   some of this; provide the rest of the code */
method factM2(n:nat) returns (r:nat)
  ensures r == factorial(n)
{
    var c:nat := n;
    r := 1;
    // this loop is deliberately INCOMPLETE; write more loop; write an
    // invariant and get it all to work
    while 0 < c 
      invariant 0 <= c
      invariant r * factorial(c) == factorial(n)
    {
      r := r * c;
      c := c - 1;
    }
}

// ******** Q5
/* This function implements exponentiation by repeatedly multiplying;
   provide the invariant to make it verify. The exp function is written
   below the method code. */
method exponentiate_via_multiplication(m:nat, n:nat) returns (r:nat)
  ensures r == exp(m,n)
{
    var c0 := 0;
    r := 1;
    while c0 < n 
      invariant c0 <= n
      invariant r  == exp(m,c0)
      {
        r := r * m;
        c0 := c0 + 1;
      }
}

function exp(m:nat, n:nat) : nat
{
    if n == 0 then 1
    else m * exp(m,n-1)
}

// ******** Q6
/* sumList is a linked-list method that calculates the sum
   of the lists (integer) elements.  (The mathematical
   functions and the type declaration come after the method.)
   Add the invariant to make the method verify.
*/
method sumList(l : list) returns (s:int)
  ensures s == sum(l)
{
    s := 0;
    var tail := l;
    while tail != Nil
      decreases length(tail)
      invariant s + sum(tail) == sum(l)
    {
        s := s + tail.elem; 
        tail := tail.next; 
    }
}

datatype list = Nil | Cons(elem:int,next:list)
function length(l:list):nat
{
    match l case Nil => 0 case Cons(_,js) => 1 + length(js)
}

function sum(l:list) : int
{
    match l case Nil => 0
    case Cons(j,js) => j + sum(js)
}

// ******** Q7 (TOUGH EXTENSION)
/* This next method implements exponentiation again, but 
   does so more efficiently by occasionally squaring.
   Verify it too.  You will almost certainly need to insert
   the exp_basesquared lemma (written out after the method) 
   into the code so that Dafny can see your invariant is 
   maintained.
*/
method exp_done_smart(m:nat, n:nat) returns (r:nat)
  ensures r == exp(m,n)
{
    var b,e := m,n;
    r := 1;
    while 0 < e
     invariant 0 <= e
     invariant r * exp(b,e) == exp(m,n)
     //invariant exp(b*b,e/2) == exp(b,e)
    {
        if e % 2 == 0 {
          exp_basesquared(b,e/2);
          b := b * b;
          e := e / 2;
        } else {
          r := r * b;
          e := e - 1;
        }
    }
}

lemma exp_basesquared(m:nat, n:nat)
  ensures exp(m * m, n) == exp(m, 2 * n) {}




