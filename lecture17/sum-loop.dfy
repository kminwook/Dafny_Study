/* Lecture 17: the same loop, two invariants.
   Ported from COMP1600 2025, tutorial 10 exercise 2. */

function f(i : int) : int

// calculates f(l) + f(l + 1) + ... f(h-1)
function sum(lo: int, hi: int) : int
  decreases hi - lo
{ if hi <= lo then 0 else f(lo) + sum(lo+1, hi) }

/* CANDIDATE B -- work still to do.  
   One trip round the loop is one unfolding of sum. */
method sum_loop(lo: int, hi: int) returns (s: int)
  ensures s == sum(lo, hi)
{
  var l, h := lo, hi;
  s := 0;
  while (l < h)
    //invariant true
    invariant s + sum(l,hi) == sum(lo,hi)
  {
    s := f(l) + s;
    //now we have s == sum(lo,l) + f(l)
    
    
    l := l + 1;
  }
}


/* CANDIDATE A -- work already done.  True, but sum recurses at 
   the LEFT end, so Dafny needs an additional lemma to get round the 
   loop. */
method sum_loop2(lo: int, hi: int) returns (s: int)
  ensures s == sum(lo, hi)
{
  var l, h := lo, hi;
  s := 0;
  if lo >= hi { return s; }
  while (l < h)
    invariant s  == sum(lo, l)
    invariant l <= h
    decreases h - l
  {
    //assert s == sum(lo,l);
    s := f(l) + s;
    //assert s == f(l) + sum(lo,l);
    l := l + 1;
    //assert s == f(l-1) + sum(lo,l-1);
    sum_add(lo,l-1);
    assert sum(lo,l) == sum(lo,l-1) + f(l-1);
  }
}









lemma sum_add(lo: int, hi: int)
  requires lo <= hi
  ensures sum(lo, hi+1) == sum(lo, hi) + f(hi)
  decreases hi - lo
{
  if (lo < hi) { sum_add(lo+1, hi); }
}

