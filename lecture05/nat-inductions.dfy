function sumUpTo(m:nat) : nat
{
    if m == 0 then 0 else m + sumUpTo(m - 1)
}

lemma sumUpTo_results()  
    ensures sumUpTo(6) == 21
    ensures sumUpTo(3) == 6
    {}

  // test on arguments 2, 3 and 100, a conjunctive claim

method Main()
{
    print "sum(2) ==", sumUpTo(2), "\n";
    print "sum(3) ==", sumUpTo(3), "\n";
    print "sum(100) == ", sumUpTo(100), "\n";
}

// what's the formula?
lemma triangle(m:nat)
    ensures sumUpTo(m) == m*(m+1)/2 {}

lemma sum100()
    ensures sumUpTo(100) == 5050 {
        triangle(100);
    }



