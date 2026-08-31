include "../core-list.dfy"

predicate exceeds(i:int, l:list<int>) {
  match l case Nil => true
  case Cons(h,t) => i > h && exceeds(i,t)
}

// will probably need an intermediate lemma
function max(i:int, j:int) : int {if i < j then j else i}

function maxList(l : list<int>) : int
requires 0 < length(l)
{
  match l
  case Cons(j,Nil) => j
  case Cons(j,js) => max(j,maxList(js))
}

lemma exceeds_ge(i:int, j :int, l : list<int>)
requires i >= j requires exceeds(j,l) // j >> l
ensures exceeds(i,l) // i >> l
{}

lemma maxList_exceeds(l : list<int>)
requires 0 < length(l)
ensures exceeds(maxList(l) + 1,l)
{ 
 match l
 case Nil => {}
 case Cons(j,Nil) => {}
 case Cons(j,js) => {
  //maxList(l) + 1 >j && exceeds(maxList(js)+1,js);
  //max(j,maxList(js))+1 > j
  assert maxList(l) == max(j,maxList(js));
  assert maxList(l) + 1 > j;
  assert exceeds(maxList(js)+1,js);
  exceeds_ge(maxList(l)+1,maxList(js)+1,js);
  assert exceeds(maxList(l)+1,js);
 }
}

// i >= j && j >= k ==> i>= k
 


lemma boundExists(l : list<int>)
  ensures exists m :: exceeds(m,l)
  {
    match l
    case Nil => {assert exceeds(-7,l);}
    case Cons(j,Nil) => {assert exceeds(j+1,l);}
    case Cons(j,js) => {
      boundExists(js);
      var n :| exceeds(n,js);
      assert max(n,j)+1 > n;
      assert max(n,j)+1 > j;
      exceeds_ge(max(n,j)+1,n,js);
      assert exceeds(max(n,j)+1,l);
    }
  } 


// flip quantifiers, prove something else
