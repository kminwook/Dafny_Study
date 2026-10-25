/* Lecture 22: the same shape, with no array in sight.
   Ported from COMP1600 2025, week10-code.dfy (inc_search). */

/* weak sauce spec.: should return more than just bool, right? */
method inc_search_incomplete(f: int -> int, lo: int, hi: int, k: int)
    returns (b: bool)
  requires forall i, j : int :: i < j ==> f(i) < f(j)
  ensures b <==> exists i : int :: lo <= i < hi && f(i) == k
{
  var l := lo;
  var h := hi;
  if (k < f(l) || k > f(h-1)) { return false; }
  while (h - l > 0)
    // l and h are the window.  the invariant has to say that if the
    // answer exists at all, it is still inside the window --
    // which, since f is increasing, is two facts about f at the edges.
  {
    var mid : int := (l + h) / 2;
    if f(mid) < k           { l := mid + 1; }
    else if k < f(mid)      { h := mid; }
    else /* k == f(mid) */  { return true; }
  }
  return false;
}









method inc_search(f: int -> int, lo: int, hi: int, k: int) returns (b: bool)
  requires forall i, j : int :: i < j ==> f(i) < f(j)
  ensures b <==> exists i : int :: lo <= i < hi && f(i) == k
{
  var l := lo;
  var h := hi;
  if (k < f(l) || f(h-1) < k) { return false; }

  assert f(l) <= k && k <= f(h-1);
  while (h - l > 0)
    decreases h - l
    invariant f(l-1) < k
    invariant k < f(h)
  {
    var mid : int := (l + h) / 2;
    if f(mid) < k           { l := mid + 1; }
    else if k < f(mid)      { h := mid; }
    else /* k == f(mid) */  { return true; }
  }
  return false;
}
