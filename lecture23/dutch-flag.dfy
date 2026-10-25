/* Lecture 23: Dijkstra's Dutch national flag.
   Ported from COMP1600 2025, tutorial 12 exercise 2. */

datatype Color = Red | White | Blue

/* the colour order on the flag */
predicate dnf_cseq(x: Color, y: Color)
{ (x == Red) || (y == Blue) || x == y == White }

method dutch_national_flag_incomplete(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> dnf_cseq(a[i], a[j])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var r, w, b := 0, 0, a.Length;
  while w != b
    // three pointers cut the array into four regions.
    // name what is true of each one -- and think about how many of
    // the four you can actually say anything about.
    // (also: why does this loop stop?)
  {
    match a[w]
    case Red =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case White =>
      w := w + 1;
    case Blue =>
      b := b - 1;
      a[w], a[b] := a[b], a[w];
  }
}









/* Three of the four regions get an invariant.  The fourth, w .. b, is
   the part we know nothing about, and saying nothing about it is
   exactly what makes the other three maintainable.

   The Blue case does not advance w: the element swapped in from the
   top has not been looked at yet. */
method dutch_national_flag(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> dnf_cseq(a[i], a[j])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var r:nat, w, b := 0, 0, a.Length;
  while w != b
    decreases b - w
    invariant r <= w <= b <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] == Red
    invariant forall i :: r <= i < w ==> a[i] == White
    invariant forall i :: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    match a[w]
    case Red =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case White =>
      w := w + 1;
    case Blue =>
      b := b - 1;
      a[w], a[b] := a[b], a[w];
  }
}
