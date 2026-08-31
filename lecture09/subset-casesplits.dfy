include "../core-list.dfy"


predicate subset(A : lset, B : lset) 
{
    match A 
    case Nil => true
    case Cons(x,xs) => member(x,B) && subset(xs,B)
}

lemma subset_member(x:int, A:lset, B:lset)
  requires member(x,A) 
  requires subset(A,B)
  ensures member(x,B) {}

/* A ⊆ B ∧ B ⊆ C ⇒ A ⊆ C */
/* build  what-do-we-have   vs   what-do-want  table */
lemma subset_trans(A : lset, B : lset, C : lset)
  requires subset(A,B)
  requires subset(B,C)
  ensures subset(A,C) 
  {
    match A
    case Nil => 
    case Cons(h,t) =>{
      //assert member(h,B);
      //assert subset(t,B);
      // assert member(h,C) by 
      subset_member(h,B,C);
      //assert subset(t,C);
      
    }
  }
lemma append_assoc(X: lset, Y: lset, Z: lset)
  ensures append(append(X, Y), Z) == append(X, append(Y, Z))
{}


lemma subset_append(A:lset,B:lset)
ensures subset(A,append(B,A))
{
  match A case Nil =>{}
  case Cons(x,xs) =>{
    //assert member(x,append(B,A));
    //assert subset(xs,append(B,A));
   // assert subset(xs,append(append(B,Cons(x,Nil)),xs));
    //assert append(B,Cons(x,xs)) == append(append(B,Cons(x,Nil)),xs)
      append_assoc(B,Cons(x,Nil),xs);
    //assert subset(xs,append(B,Cons(x,xs)));

  }
}

/* A ⊆ A */
lemma subset_refl(A : lset)
  ensures subset(A,A)
  {
    match A
    case Nil => {}
    case Cons(x,xs) =>{
     subset_append(xs,Cons(x,Nil));
     assert append(Cons(x,Nil),xs) == Cons(x,xs);
    }
  }

 