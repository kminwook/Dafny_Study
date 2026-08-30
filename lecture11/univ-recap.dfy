predicate q(x:int)
predicate r(x:int)

lemma somename_arbitrary()
  ensures forall x | 0 < x :: q(x)


lemma somename_instantiate(y:nat)
  requires forall x | 0 < x :: q(x)
  ensures r(y / 103)
