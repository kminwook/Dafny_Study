datatype list<T> = Nil | Cons(hd : T, tl : list<T>)
datatype tree<T> = Leaf | Node(left : tree<T>, val : T, right : tree<T>)

function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, xs) => 1 + length(xs)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T>
{
  match l1
  case Nil => l2
  case Cons(x, xs) => Cons(x, append(xs, l2))
}
function min(a : nat, b : nat) : nat
{
  if a < b then a else b
}
/* ------------------------------------------------------------
   PART A -- More recursion over lists
   ------------------------------------------------------------ */

// Exercise 1. take
function take<T>(n : nat, l : list<T>) : list<T>
{
  if n == 0 then
    Nil
  else
    match l
    case Nil => Nil
    case Cons(x, xs) => Cons(x, take(n - 1, xs))
}

// Exercise 2. drop
function drop<T>(n : nat, l : list<T>) : list<T>
{
  if n == 0 then
    l
  else
    match l
    case Nil => Nil
    case Cons(_, xs) => drop(n - 1, xs)
}

// Exercise 3. reverse
function reverse<T>(l : list<T>) : list<T>
{
  match l
  case Nil => Nil
  case Cons(x, xs) => append(reverse(xs), Cons(x, Nil))
}
function zip<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>{
match (l1, l2)
  case (Cons(x, xs), Cons(y, ys)) => Cons((x, y), zip(xs, ys))
  case _ => Nil
}
function unzip<A, B>(l : list<(A, B)>) : (list<A>, list<B>){
  match l
  case Nil => (Nil,Nil)
  case Cons((x,y),rest) => 
    var (xs,ys) := unzip(rest);
    (Cons(x,xs),Cons(y,ys))
}
function zipPartial<A, B>(l1 : list<A>, l2 : list<B>) : list<(A, B)>
  requires length(l1) == length(l2)
{
  if l1.Nil? then 
    Nil
  else 
    Cons((l1.hd, l2.hd), zipPartial(l1.tl, l2.tl))
}
function sumUpTo(n : nat) : nat
{
  if n == 0 then 0 else n + sumUpTo(n - 1)
}

lemma triangle(n : nat)
ensures 2 * sumUpTo(n) == n * (n+1)
{}

lemma takeLength<T>(n : nat, l : list<T>)
  ensures length(take(n,l)) == min(n,length(l))
{}

function sub(a:nat, b:nat) :nat{
  if a < b then 0 else a-b
}
lemma dropLength<T>(n : nat, l : list<T>)
ensures length(drop(n,l)) ==  sub(length(l),n)
{}
// Exercise 10.
// take and drop fit back together: appending  take(n, l)  and
//  drop(n, l)  gives back  l .
lemma takeDropAppend<T>(n : nat, l : list<T>)
ensures l == append(take(n,l),drop(n,l))
{}
// Exercise 11.  (unzip lengths)
// Unzipping a list of pairs gives two lists, each the same length as
// the original. The result of unzip is a pair, so refer to its parts
// as  unzip(l).0  and  unzip(l).1, or pattern match with
// ensures var(l1,l2) := unzip(l); ...
lemma unzipLength<A, B>(l : list<(A, B)>)
ensures length(unzip(l).0) == length(l) && length(unzip(l).1) == length(l)
{}
// Exercise 12.  (zipPartial length)
// Because zipPartial pairs up ALL elements, its result has exactly the
// same length as its inputs. Write the ensures for it.
//     length(zipPartial(l1, l2)) == ??
// Note: this lemma mentions zipPartial, so it must satisfy zipPartial's
// precondition -- you will need the same  requires  clause here too.
lemma zipPartialLength<A, B>(l1 : list<A>, l2 : list<B>)
requires length(l1) == length(l2)
ensures length(zipPartial(l1,l2)) == length(l1)
{}

// Exercise 13.
// treeSize counts the internal (Node) nodes: a Leaf has size 0; a Node
// has size 1 plus the sizes of its two subtrees.
function treeSize<T>(t : tree<T>) : nat{
  match t
  case Leaf => 0
  case Node(left,_,right) => 1 + treeSize(left) + treeSize(right)
}

// Exercise 14.
// mirror reflects a tree left-to-right: at each Node, swap the two
// subtrees (recursively) and keep the value.
function mirror<T>(t : tree<T>) : tree<T>
{
  match t
  case Leaf => Leaf
  case Node(left,val,right) => Node(mirror(right),val,mirror(left))
}
// Exercise 15.
// Mirroring does not change the number of nodes. Write the ensures for
//     treeSize(mirror(t)) == ??
lemma mirrorSize<T>(t : tree<T>)
ensures treeSize(t) == treeSize(mirror(t))
{}
// Exercise 16.
// Mirroring twice gets you back where you started. Write the ensures
// clause capturing this.
lemma mirrorMirror<T>(t : tree<T>)
ensures t == mirror(mirror(t))
{}

// Exercise 17.
// maxDepth(t) is the length of the longest path from the root down to a
// leaf: a Leaf has depth 0; a Node is 1 plus the LARGER of its two
// subtree depths. You will need a  max  function on ints first -- you
// have seen how to write one in lectures; add it above this exercise.
function max(a:nat, b:nat): nat{
  if a>=b then a else b
}
function maxDepth<T>(t : tree<T>) : nat{
  match t
  case Leaf => 0
  case Node(left,_,right) => 1 + max(maxDepth(left),maxDepth(right))
}
// Exercise 18.
// maxDepth and treeSize are not independent: for EVERY tree, one of
// them stands in a fixed relation to the other (there are multple
// solutions here).

// Work out one such relation, and write it as the ensures, using
// maxDepth(t) and treeSize(t). Leave the body empty.
// If Dafny rejects your claim, it is not true of every tree --
// try a different relation until it holds.
lemma depthAndSize<T>(t : tree<T>)
ensures treeSize(t) >= maxDepth(t)
{}
/* ------------------------------------------------------------
   Main Method for Testing
   ------------------------------------------------------------ */

method Main()
{
  // 테스트용 리스트 l = [10, 20, 30] 생성 (Cons(10, Cons(20, Cons(30, Nil))))
  var l := Cons(10, Cons(20, Cons(30, Nil)));

  // 1. take 테스트
  var t1 := take(2, l); // Cons(10, Cons(20, Nil))
  assert t1 == Cons(10, Cons(20, Nil));
  
  var t2 := take(5, l); // 원래 리스트 길이보다 긴 경우
  assert t2 == l;

  // 2. drop 테스트
  var d1 := drop(1, l); // Cons(20, Cons(30, Nil))
  assert d1 == Cons(20, Cons(30, Nil));
  
  var d2 := drop(3, l); // 전체를 버린 경우
  assert d2 == Nil;

  // 3. reverse 테스트
  var r := reverse(l); // Cons(30, Cons(20, Cons(10, Nil)))
  assert r == Cons(30, Cons(20, Cons(10, Nil)));

// 4. zip 테스트 [새로 추가된 검증 및 출력]
  var l_str := Cons("A", Cons("B", Nil)); // ["A", "B"]
  var z := zip(l, l_str); // [(10, "A"), (20, "B")]
  assert z == Cons((10, "A"), Cons((20, "B"), Nil));
  // 5. unzip 테스트
  var unzipped := unzip(z);
  assert unzipped == (Cons(10, Cons(20, Nil)), Cons("A", Cons("B", Nil)));
// 6. zipPartial 테스트
  var l_a := Cons(1, Cons(2, Nil));
  var l_b := Cons("X", Cons("Y", Nil));
  
  // 길이가 같을 때 정상 동작
  var zp := zipPartial(l_a, l_b);
  assert zp == Cons((1, "X"), Cons((2, "Y"), Nil));

var sampleTree := Node(Node(Leaf, 10, Leaf), 20, Node(Leaf, 30, Leaf));
  
  var size := treeSize(sampleTree);
  assert size == 3; // 노드가 총 3개(10, 20, 30)
var mirroredTree := mirror(sampleTree);
  assert mirroredTree == Node(Node(Leaf, 30, Leaf), 20, Node(Leaf, 10, Leaf));

// 17. maxDepth 테스트

  var depth := maxDepth(sampleTree);
  assert depth == 2;

  // 비대칭 트리 테스트:

  var deepTree := Node(Node(Node(Leaf, 5, Leaf), 10, Leaf), 20, Node(Leaf, 30, Leaf));
  assert maxDepth(deepTree) == 3;


  print "Original list: ", l, "\n";
  print "Reversed list: ", r, "\n";
  print "Zipped list:   ", z, "\n";
  print "Unzipped lists: ", unzipped, "\n";
    print "zipPartial list: ", zp, "\n";
  print "treeSize: ", size, "\n";
  print "mirroredTree: ", mirroredTree, "\n";
  print "maxDepth of sampleTree: ", depth, "\n";
  print "maxDepth of deepTree: ", maxDepth(deepTree), "\n";

}