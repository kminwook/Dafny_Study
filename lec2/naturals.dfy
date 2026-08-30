function f(x:int) :int { x + 1 }

/* Using + works, but what about subtraction */
function g(n:int) :int { n - f(n) }

/* absolute difference, but on nats */
function h(n:nat) : int {n-1}

function ebs_diff(m:nat,n:nat) : nat
{
    if m < n then n-m else m-n
}

method Main()
{
    print "g(10) = ", g(10), "\n";
}