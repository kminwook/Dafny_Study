include "core-list.dfy"



predicate all_distinct(A : lset) {
  match A case Nil => true
  case Cons(x,xs) => !member(x,xs) && all_distinct(xs) }

function nub(A : lset) : lset {
  match A case Nil => Nil
  case Cons(x,xs) => if member(x,xs) then nub(xs)
                     else Cons(x,nub(xs))
} // the "nub" of an issue is its essence
