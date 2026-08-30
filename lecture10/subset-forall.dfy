include "../core-list.dfy"

/* preliminaries: definitions of member, subset and reverse, 
   and a useful result about being a member of append (see 
   before when we were showing properties of union) */
predicate member(x:int, A:lset)
{
    match A 
    case Nil => false
    case Cons(y,ys) => x == y || member(x,ys)
}

predicate subset(A: lset, B : lset)
{
    match A 
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}

lemma member_append(x:int, A:lset, B : lset)
  ensures member(x,append(A,B)) <==> member(x,A) || member(x,B)
{}

function reverse<T>(l : list<T>) : list<T>
{
    match l
    case Nil => Nil
    case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
    // in nicer Haskell would be 
    // case l of 
    //   [] -> []
    //   x:xs -> reverse xs ++ [x]
}

lemma subset_forall(A : lset, B : lset)
  ensures subset(A,B) <==> forall x | member(x,A) :: member(x,B)
{
  if subset(A,B) { 
    // dafny automatically reproves our existing member_subset
  } else {
    /* A not a subset of B */
    match A case Nil => /* impossible */
    case Cons(x,xs) => {
      if member(x,B) {
        assert !subset(xs,B);
        var x0 :| member(x0,xs) && !member(x0,B);
        assert exists x0 :: member(x0,A) && !member(x0,B);
      }
      else {
        assert member(x,A);
        assert !member(x,B);
      }
    }
  }
  // surprising which is the tricky direction 
}

// this should now be easier
lemma subset_refl(A:lset) ensures subset(A,A) 
{
  subset_forall(A,A);
}

lemma mem_reverse(x:int, A:lset)
  ensures member(x, reverse(A)) <==> member(x,A) 
{
  match A case Nil=> {}
  case Cons(y,ys) => 
  member_append(x,reverse(ys),Cons(y,Nil));
}

lemma reverse_subset(A:lset)
  ensures subset(reverse(A), A) 
  ensures subset(A, reverse(A))
{
}