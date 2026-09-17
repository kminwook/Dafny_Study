function sumUpTo(n : nat) : nat
{
    if n == 0 then 0 
    else n + sumUpTo(n-1)
}

lemma {:induction false} sumUpTo_closedForm(n:nat)
  ensures sumUpTo(n) == n * (n + 1) / 2 
{
  if n == 0 {}
  else{
    sumUpTo_closedForm(n-1);
  }
}

// let's ramp it up:

function sumSquares(n:nat) : nat {
    if n == 0 then 0 else n*n + sumSquares(n-1)
}

lemma {:induction false}sumSquares_closedForm(n:nat)
  ensures sumSquares(n) == n * (n + 1) * (2 * n + 1) / 6 
{
  if n == 0{}
  else{
    sumSquares_closedForm(n-1);
  }
}
