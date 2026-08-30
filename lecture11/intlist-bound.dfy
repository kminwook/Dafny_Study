include "../core-list.dfy"

predicate exceeds(i:int, l:list<int>) {
  match l case Nil => true
  case Cons(h,t) => i > h && exceeds(i,t)
}

// will probably need an intermediate lemma

lemma boundExists(l : list<int>)
  ensures exists m :: exceeds(m,l)

// flip quantifiers, prove something else
