include "../core-list.dfy"

// "dictionaries" are lists of integers (the keys), coupled 
// with the values, which can be anything (generic/polymorphic)
type dict<V> = list<(int,V)>

function lookup<V>(key:int, dict:dict<V>) : option<V>
{
    match dict 
    case Nil => None
    case Cons((j,v), rest) => if j == key then Some(v) 
                            else lookup(key,rest)
}

function insert<V>(key : int, value : V, dict : dict<V>) : dict<V>
{
  match dict case Nil => Cons((key,value),Nil)
  case Cons((j,u),t) => if key == j then Cons((key,value),t)
                        else Cons((j,u),insert(key,value,t))
}

lemma lookup_insert<V>(d:dict<V>, k:int, v:V)
  ensures lookup(k,insert(k,v,d)) == Some(v) {}

  lemma lookup_insert_different<V>(d : dict<V>, k1 : int, k2:int, v : V)
  requires k1 != k2
  ensures lookup(k2,insert(k1,v,d)) == lookup(k2,d) {}
