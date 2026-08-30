datatype intlist = Empty 
  | Cons(hd:int, tl:intlist)

// write some variations on this with selectors ".fldname" and 
// pattern-matching to get particular output numbers
function dumb() : int
  ensures dumb() == 0
{
    var l := Cons(0,Cons(1,Cons(2,Empty)));
    l.hd
}

function dumb2() : int
  ensures dumb2() == 3
  {
    var l:= Cons(0,Cons(3,Empty));
    l.tl.hd
  }

function head(x:intlist) : int
  requires x.Cons?
  ensures head(x) == x.hd{
    match x case Cons(h,t) => h
  }
