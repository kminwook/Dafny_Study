 ghost predicate Ordered(s: seq<int>, left: nat, right: nat)
    requires left <= right <= |s|
  {
    forall i: nat :: 0 < left <= i < right ==> s[i-1] <= s[i]
  }

  method BogoSort(a: array<int>)
    modifies a
    ensures Ordered(a[..],0,a.Length) 
    ensures multiset(a[..]) == multiset(old(a[..]))
  {
    var i :nat := 0;
    while i < a.Length
      invariant i <= a.Length
      invariant Ordered(a[..],0,i)
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var minValue := a[i];
      var minPos := i;
      var j : nat := i + 1;
      while j < a.Length
        invariant j <= a.Length
        invariant minPos < a.Length
        invariant a[minPos] == minValue
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
        j := j + 1;
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
      }
      i := i + 1;
    }
  }