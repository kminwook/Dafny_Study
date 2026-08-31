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



lemma maxList_exceeds(l : list<int>)
requires 0 < length(l)
ensures exceeds(maxList(l) + 1,l)
{
  match l case Nil => {}
  case Cons(j,Nil) => {}
  case Cons(j,js) => {
    assert(maxList(l) == max(j,maxList(js)));
    assert exceeds(maxList(js)+1, js);
    assert maxList(l) +1 > j;
    /* maxList(js) + 1 >> js
       maxList(l) == max(j,maxList(js))
       maxList(l) + 1 > j && maxList(l) + 1 > maxList(js)
       */
    assert maxList(l) + 1>= maxList(js) +1;
    // and also maxList(js) + 1 >> js
    exceeds_ge(maxList(l) + 1, maxList(js) + 1, js);
    assert exceeds(maxList(l) + 1 , js);
    // maxList(l) + 1 >> js
  }
}

// i >= j && j >= k ==> i>= k

lemma exceeds_ge(i:int, j :int, l : list<int>)
requires i >= j requires exceeds(j,l) // j >> l
ensures exceeds(i,l) // i >> l
{}

lemma boundExists(l : list<int>)
  ensures exists m :: exceeds(m,l)
  {
    match l
    case Nil => {assert exceeds(-3,l);}
    case Cons(j,Nil) => {assert exceeds(j+1,l);}
    case Cons(j,js) => {
      boundExists(js);
      var m0 :| exceeds(m0,js);
      assert max(m0,j) +1 >j;
      assert max(m0,j) + 1 > m0;
      exceeds_ge(max(m0,j)+1,m0,js);
      assert exceeds(max(m0,j)+1,l);
    }
  }

// flip quantifiers, prove something else
