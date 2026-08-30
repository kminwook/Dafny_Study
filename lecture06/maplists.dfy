include "../core-list.dfy"
type intmap<V> = list<(int,V)>

ghost predicate member<T>(i :T, l : list<T>)
{
    match l case Nil => false
    case Cons(j,js) => i == j || member(i,js)
}

function keys<V>(m:intmap<V>) : list<int>
{
    match m case Nil => Nil
    case Cons((k,_), kvs) => Cons(k,keys(kvs))
}

function insert<V>(m : intmap<V>, k:int, v:V) : intmap<V>
{
    Cons((k,v), m)
}

function lookup<V>(m : intmap<V>, k:int) : option<V>
{
    match m 
    case Nil => None
    case Cons((j,v), jvs) => if k == j then Some(v) else lookup(jvs, k)
}

lemma member_lookup<V>(m : intmap<V>, k : int, v : V)
  requires member((k,v), m)
  ensures exists u :: lookup(m,k) == Some(u)
{}

lemma lookup_some<V>(m : intmap<V>, k : int, v : V)
  ensures lookup(m,k) == Some(v) ==> member(k,keys(m))
  {}
