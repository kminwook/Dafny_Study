include "../core-list.dfy"

// OK
predicate member(i:int, s:lset) 
{
    match s
    case Nil => false
    case Cons(h,t) => if i == h then true else member(i,t)
}
function insert(i:int, s:lset) : lset
{
    Cons(i,s)
}
function union (A : lset, B : lset) : lset 
{
    append(A,B)
}
function delete(i:int, A : lset) : lset
{
    match A 
    case Nil => Nil
    case Cons(h,t) => 
        var t' := delete(i,t);
        if i == h then t' else Cons(h,t')
}
function intersect(A : lset, B : lset) : lset
{
    match A 
    case Nil => Nil
    case Cons(h,t) =>
        var i0 := intersect(t,B);
        if member(h,B) then Cons(h,i0) else i0

}
predicate subset(A : lset, B : lset)
{
     match A 
    case Nil => true
    case Cons(h,t) => member(h,B) && subset(t,B)
}

function card(A : lset) : nat
{
     match A 
    case Nil => 0
    case Cons(h,t) => if member(h,t) then card(t) else 1 + card(t)
}

lemma cardtest()
ensures card(union(Cons(1,Cons(2,Cons(3,Nil))),Cons(3,Cons(4,Cons(5,Nil))))) == 5 {}
// work
lemma member_insert(x : int, y:int, A : lset) 
ensures member(x,insert(y,A)) <==> member(x,A) || y == x{}

lemma member_delete(i:int, j:int, A:lset)
ensures member(i,delete(j,A)) <==> i != j && member(i,A) {}

lemma member_inter(x:int, A:lset, B:lset)
ensures member(x,intersect(A,B)) <==> member(x,A) && member(x,B){}

lemma member_subset(x:int, A:lset, B:lset)
requires subset(A,B)
requires member(x,A)
ensures member(x,B){}

// feels like it should work
lemma member_union(x : int, A : lset, B : lset)
    ensures member(x,union(A,B))

lemma subset_union(A : lset, B : lset, C : lset) 
lemma subset_refl(A : lset)
lemma subset_trans(A : lset, B : lset, C : lset)
