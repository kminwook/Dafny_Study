/* Lecture 20: arrays, by demonstration. */

method basics(n:nat)
  requires 12 <= n < 20
{
  var a : array<int> := new int[20];
  a[0] := 12;
  var a0 : int := 12;
  a[12] := 12;
  assert a.Length == 20;
  assert a[0] == 12 && a0 == 12;

  /* in place: no new array is made */
  a[0] := 17;
  assert a[0] == 17 && a0 == 12;
  a0 := 17;

  /* a is a collection of 20 new variables, 
     each a[i] behaves just like a variable you 
     might declare with something like
        var a12 : int := 12
  */
}

/* can return arrays from methods and describe their
   properties */
method make() returns (a: array<int>)
  ensures a.Length == 20
  ensures a[12] == 12
  ensures forall i | 0 <= i < 20 && i != 12 :: a[i] == 0
{
  a := new int[20];
  var i := 0;
  while i < 20
    //invariant i <= a.Length
    invariant forall j:nat | j < i :: a[j] == 0
  { 
    a[i] := 0; 
    i := i + 1; 
  }
  assert forall j : nat | j < a.Length :: a[j] == 0;
  a[12] := 12;
}

/* functions can't create fresh arrays, and can't
   assign to array indices 

   They also find it hard to even look inside them...   
*/
function array_fn(a:array<int>, b:array<int>) : array<int>
  requires a.Length > 0
  reads a
{
  if a[0] % 2 == 0 then a else b
}

predicate arrays_eq(a : array<int>, b:array<int>)
{
  if a == b then true else false
}

predicate sorted(a:array<int>)
  reads a
{
  forall i : nat, j : nat | j < i < a.Length :: a[j] <= a[i]
}

predicate ssorted(a:seq<int>)
{
  forall i : nat, j : nat | j < i < |a| :: a[j] <= a[i]
}

method foo(a:array<int>) returns (i:int)
{
  if ssorted(a[..]) { return 3; }
  else {return 4;}
}