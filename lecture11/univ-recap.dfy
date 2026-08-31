predicate q(x:int)
predicate r(x:int){ true}

lemma somename_arbitrary()
  ensures forall x | 0 < x :: q(x)
  {
    forall x ensures 0 < x ==> q(x){
      if 0 < x{}
    }
  }


lemma somename_instantiate(y:nat)
  requires forall x | 0 < x :: q(x)
  ensures r(y / 103)
  {
    if ( 0 < y) {
      assert q(y);
      assert r(y/103) by {}
    }
  }
