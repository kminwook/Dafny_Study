include "../core-list.dfy"

function member(i : int, l : list<int>) : bool
{
    match l case Nil => false case Cons(h,t) => h == i || member(i,t)
}

function nth<T>(l : list<T>, n : nat) : T
  requires n < length(l)
{
    match l 
    case Cons(h,t) => if n == 0 then h else nth(t, n - 1)
}

lemma mem_nth(i : int, l : list<int>)
  ensures member(i, l) <==> exists idx : nat | idx < length(l) :: nth(l,idx) == i
  {
    match l case Nil =>{}
    case Cons(j,js) =>{
      if member(i,l){
        if i == j {
          assert nth(l,0) == i;
        } else {
          assert member(i,js);
          var idx : nat :| idx < length(js) && nth(js,idx)==i;
          assert nth(l,idx+1) == i;
          assert idx+1 < length(l);
          assert exists IDX : nat | IDX < length(l) :: nth(l,IDX) == i;
        }
      } else {

      }
    }
  }
