// 1. Write functions to implement the following; 
// 2. Use parentheses to make them unambiguous
// 3. Make sure we know what values they'll have

// p ∧ q ∨ r
// p ⇒ q ∨ r ⇔ s

function f(x:int, y:int) :int
{
    (x+y) * 2
}

lemma ftest() ensures f(2,3) == 10 {}

function ex1(p:bool,q:bool,r:bool) : bool{
    (p && q) || r
}