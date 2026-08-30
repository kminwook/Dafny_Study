datatype intlist = Empty | Cons(hd: int, tl : intlist)

function singleton(i:int) : intlist

  // what ensures line might we write here?
{
  Cons(i, Empty)
}
lemma singleton_properties(i:int)
  ensures !singleton(i).Empty?
  ensures singleton(i).Cons? 
  ensures singleton(i).hd == i
  ensures singleton(i).tl == Empty {}
  
// what more interesting functions might we write to build lists?
// - of different lengths
// - with successive elements
// - ?

function three_successive(i:int) :intlist{
  Cons(i,Cons(i+1,Cons(i+2,Empty)))
}

lemma TS4()
  ensures three_successive(4) == Cons(4,Cons(5,Cons(6,Empty))){}
