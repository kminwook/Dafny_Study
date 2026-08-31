include "../core-list.dfy"

/* preliminaries: definitions of member, subset and reverse, 
   and a useful result about being a member of append (see 
   before when we were showing properties of union) */

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
    // exists x | member(x,A) && !member(x,B)
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
  //member(x,(reverse(ys),Cons(y,Nil)))
  match A case Nil=> {}
  case Cons(y,ys) => 
    member_append(x,reverse(ys),Cons(y,Nil));

}

lemma reverse_subset(A:lset)
ensures subset(reverse(A),A)
ensures subset(A,reverse(A))
{
  assert subset(reverse(A),A) by{
    subset_forall(reverse(A),A);
    // subset(reverse(A),A) <==> forall x :: memeber(x,reverse(A)) ==> member(x,A)
    forall x | member(x,reverse(A)) ensures member(x,A){
      mem_reverse(x,A);
    }
  }
  assert subset(A,reverse(A)) by {
    subset_forall(A,reverse(A));
    forall x ensures member(x,A) ==> member(x,reverse(A)){
      mem_reverse(x,A);
    }
  }
}