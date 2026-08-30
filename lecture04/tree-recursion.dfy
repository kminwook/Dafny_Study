datatype option<V> = None | Some(V)
datatype tree<V> = Lf
  | Node(k : string, v : V, left : tree<V>, right : tree<V>)

function lookup<V>(t : tree<V>, key : string) : option<V> 
{
  match t
  case Lf => None
  case Node(j,v,lt,rt) => 
    if j == key then Some(v)
    else if j < key then lookup(rt,key)
    else lookup(lt,key)
}

/**/
function insert_and_maybe_replace<V>(t : tree<V>, key : string, value : V) : tree<V> {
  match t 
  case Lf => Node(key,value,Lf,Lf)
  case Node(j,v,lt,rt) => 
    if j == key then Node(key,value,lt,rt)
    else if key < j then Node(j,v,insert_and_maybe_replace(lt,key,value),rt)
    else Node(j, v ,lt,insert_and_maybe_replace(rt,key,value))
}

function sz<T>(t:tree<T>) : nat 
{
  match t
  case Lf => 0
  case Node(_,_,lt,rt) => 1 + sz(lt) + sz(rt)
}

// lemmas?