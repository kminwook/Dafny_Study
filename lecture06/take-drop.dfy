include "../core-list.dfy"

function take<T> (n:nat, l : list<T>) : list<T>
{
    if n == 0 then Nil
    else 
      match l 
      case Nil => Nil
      case Cons(h,t) => Cons(h, take(n-1, t))
}

function drop<T>(n:nat, l : list<T>) : list<T> 
{
  match l case Nil => Nil
  case Cons(h,t) => if n == 0 then l
                    else drop(n-1,t)
}

function max(i:int, j:int):int{if i < j then j else i}

lemma length_drop<T>(n:nat, l:list<T>)
ensures length(drop(n,l)) == max(length(l)-n , 0){}

lemma take_drop<T>(n:nat, l:list<T>)
ensures append(take(n,l),drop(n,l)) == l{}


