include "../core-list.dfy"

function reverse<T>(l:list<T>) : list<T>
{
    match l case Nil => Nil
    case Cons(h,t) => append(reverse(t), Cons(h,Nil))
}

lemma length_append<T>(l1 : list<T>, l2:list<T>) 
  ensures length(append(l1,l2)) == length(l1) + length(l2) {}


lemma append_nil_right<T>(l: list<T>)
  ensures append(l, Nil) == l
{
  match l
  case Nil => {}
  case Cons(x, xs) => append_nil_right(xs);
}

lemma append_assoc<T>(l1: list<T>, l2: list<T>, l3: list<T>)
  ensures append(append(l1,l2), l3) == append(l1, append(l2, l3))
{
  match l1
  case Nil => {}
  case Cons(x, xs) => append_assoc(xs, l2, l3);
}

lemma reverse_append<T>(l1: list<T>, l2: list<T>)
  ensures reverse(append(l1,l2)) == append(reverse(l2),reverse(l1))
{
  match l1
  case Nil =>
    append_nil_right(reverse(l2));
  case Cons(x, xs) =>
    reverse_append(xs, l2);
    append_assoc(reverse(l2), reverse(xs), Cons(x, Nil));
}


datatype tree<V> = Lf | Node (k:int, v:V, tree<V>, tree<V>)

function size<V>(t : tree<V>) : nat
{
    match t case Lf => 0
    case Node(_, _, lt, rt) => size(lt) + size(rt) + 1
}

function mirror<V>(t:tree<V>) : tree<V>
{
    match t case Lf => Lf
    case Node(k,v,lt,rt) => Node(k,v,mirror(rt), mirror(lt))
}

function keys<V>(t:tree<V>) : list<int>
{
    match t case Lf => Nil
    case Node(k,_, lt, rt) => append(keys(lt), Cons(k, keys(rt)))
}

lemma {:induction false} size_mirror<V>(t:tree<V>) 
  ensures size(mirror(t)) == size(t) 
  {
    match t case Lf =>{}
    case Node(k,v,lt,rt) => {
        size_mirror(lt);
        size_mirror(rt);
    }
  }

lemma {:induction false} length_keys<V>(t:tree<V>)
  ensures length(keys(t)) == size(t) 
{
    match t case Lf => {}
    case Node(k,v,lt,rt) => {
        //assert keys(t) == append(keys(lt),Cons(k,keys(rt)));
        length_append(keys(lt),Cons(k,keys(rt)));
        //assert length(keys(t)) == length(keys(lt)) + length(Cons(k,keys(rt)));
        //assert length(keys(t)) == length(keys(lt)) + 1 + length(keys(rt));
        length_keys(lt);
        length_keys(rt);
    }
}

lemma {:induction false}keys_mirror<T>(t:tree<T>)
ensures keys(mirror(t)) == reverse(keys(t))
{
    match t case Lf => {}
    case Node(k,v,lt,rt) => {
        keys_mirror(lt); keys_mirror(rt);
        var k_l := keys(lt);
        var k_r := keys(rt);
        assert reverse(keys(t)) == append(reverse(Cons(k,k_r)),reverse(k_l))
        by {
            reverse_append(k_l,Cons(k, k_r));
        }
        append_assoc(reverse(k_r),Cons(k,Nil),reverse(k_l));
    }
}

/*
lemma keys_mirror<T>(t:tree<T>)
ensures keys(mirror(t)) == reverse(keys(t))
{
    match t case Lf => {}
    case Node(k,v,lt,rt) => {

        var k_l := keys(lt);
        var k_r := keys(rt);

        reverse_append(k_l,Cons(k, k_r));
        append_assoc(reverse(k_r),Cons(k,Nil),reverse(k_l));
    }
}
*/