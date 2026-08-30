include "core-list.dfy"

predicate member(x : int, A : lset)
{
    match A 
    case Nil => false
    case Cons(y,ys) => x == y || member(x,ys)
}

predicate wfSet( A : lset)
{
    match A
    case Nil => true
    case Cons(x,xs) => !member(x,xs) && wfSet(xs)
}

/* functions to define
insert
delete
inter
union
card
subset
*/

function insert (x :int, A : lset) : lset{
    if member(x,A) then A else Cons(x,A)
}

lemma insert_preserves_wfSet(x:int, A:lset)
requires wfSet(A)
ensures wfSet(insert(x,A)) {}

lemma member_insert(x:int, y:int, A:lset)
ensures member(x,insert(y,A)) <==> x == y || member(x,A){}
/* lemmas to prove
member(x,insert(y,A)) <==> x == y || member(x,A)
member(x,delete(y,A)) <==> x != y && member(x,A)
member(x,union(A,B)) <==> member(x,A) || member(x,B)
member(x,inter(A,B)) <==> member(x,A) && member(x,B)
member(x,A) && subset(A,B) ==> member(x,B)

+ whatever well-formedness results we need and can manage
*/

function insert(x:int, A:lset) : lset
lemma member_insert(x:int, y:int, A:lset)
/* ? */ lemma wfSet_insert(x:int, A:lset) 


function delete(x:int, A : lset) : lset{
    match A
    case Nil => Nil
    case Cons(h,t) => if x == h then t else Cons(h,delete(x,t))
}
lemma member_delete(x:int, y:int, A : lset) 
requires wfSet(A)
ensures member(x,delete(y,A)) <==> x != y && member(x,A){}

lemma wfSet_delete(x:int, A:lset)
requires wfSet(A)
ensures wfSet(delete(x,A)) {}


function inter(A:lset, B:lset) : lset{
    match A
    case Nil => Nil
    case Cons(h,t) => var r0 := inter(t,B);
    if member(h,B) then Cons(h,r0) else r0
}

lemma member_inter(x:int, A : lset, B : lset)
ensures member(x,inter(A,B)) <==> member(x,A) && member(x,B){}

lemma wfSet_inter(A:lset, B:lset)
requires wfSet(A)
requires wfSet(B)
ensures wfSet(inter(A,B)) {}


predicate subset(A: lset, B : lset){
    match A case Nil => true
    case Cons(h,t) => member(h,b) && subset(t,B)
}

lemma member_subset(x:int, A : lset, B : lset)
requires member(x,A)
requires subset(A,B)
ensures member(x,B) {}


function union(A:lset, B:lset): lset{
    match A case Nil => B
    case Cons(h,t) => if !member(h,B) then Cons(h,union(t,B))
                      else union(t,B)
}
lemma member_union(x:int, A:lset, B:lset)
ensures member(x,union(A,B)) <==> member(x,A) &&member(x,B){}

/* ? */ lemma wfSet_union(A:lset, B:lset)
    requires wfSet(A) requires wfSet(B)
    ensures wfSet(union(A,B)) {}
    
