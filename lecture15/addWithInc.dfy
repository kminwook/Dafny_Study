// add with increments (+1s)
method addWI(m : nat, n:nat) returns (r:nat)
  ensures r == m + n
{
    var n0 := 0;
    r := m;
    while n0 < n  // try with != too
        invariant n0 <= n
        invariant r == m + n0
    { 
        n0 := n0 + 1; 
        r := r + 1; 
    }
    //assert n0 == n;
}