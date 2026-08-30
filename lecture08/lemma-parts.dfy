// let's mess with the component parts of the following
//   - add a return type?
//   - add requires; add ensures
//   - remove requires ; remove ensures
//   - remove/add parameters
lemma simple(m:nat, n:nat)
  requires m <= n requires n < m
  ensures m+1 < m
{}

