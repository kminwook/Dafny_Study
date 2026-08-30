datatype list<T> = Nil | Cons(hd: T, tl: list<T>)

// 1. length 함수 (Nile -> Nil 오타 수정)
function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + length(t)
}

// 2. 두 정수 중 큰 값을 반환하는 max 함수 (i > j 일 때 i 반환하도록 수정)
function max(i: int, j: int) : int {
  if i > j then i else j
}

// 3. 일반적인 재귀 방식의 maxList
function maxList(l : list<int>) : int
  requires length(l) > 0
{
  match l
  case Cons(hd, Nil) => hd
  case Cons(hd, tl) => max(hd, maxList(tl))
}

// 4. Accumulator(누적기) 방식의 maxListA
function maxListA(l : list<int>, acc : int) : int
{
  match l
  case Nil => acc
  case Cons(hd, tl) => maxListA(tl, max(hd, acc))
}

method Main() {
  var testList := Cons(12, Cons(3, Cons(4, Cons(3, Nil))));

  // maxList 테스트
  print "maxList  = ", maxList(Cons(12, Cons(3, Cons(4, Cons(3, Nil))))), "\n"; // 출력: 12

  // maxListA 테스트 (초기 acc 값으로 리스트의 첫 원소나 가장 작은 정수 전달)
  print "maxListA = ", maxListA(testList.tl, testList.hd), "\n"; // 출력: 12
}