/* ## Part I. 함수/프레디케이트 기본기 (Lecture 2~3, Lab1)

**Q1.** 다음 datatype이 주어졌을 때,
```dafny
datatype shape = Circle(radius: nat) | Rect(w: nat, h: nat)
```
- `area(s: shape): nat` 함수를 작성하시오. (원의 넓이는 `radius*radius*3`으로 근사해서 계산해도 됨 — 정수 연산만 사용)
- `perimeter(s: shape): nat` 함수도 작성하시오.
*/
datatype shape = Circle(radius: nat) | Rect(w: nat, h: nat)
function area(s:shape) : nat{
    match s
    case Circle(r) => r*r*3
    case Rect(w,h) => w*h 
}
function perimeter(s:shape) : nat{
    match s
    case Circle(r) => 2 * r*3
    case Rect(w,h) => 2*(w+h)
}
/*
**Q2.** `nat` 두 개를 받아 더 큰 값을 리턴하는 `max(a: nat, b: nat): nat` 함수를 쓰고, 다음을 만족하는 lemma를 작성하시오 (빈 body `{}` 로 증명되어야 함):
- `max(a,b) >= a && max(a,b) >= b`
- `max(a,b) == a || max(a,b) == b`
*/
function max(a : nat, b:nat) :nat{
    if a > b then a else b
}
lemma max_e(a: nat, b: nat)
ensures max(a,b) >= a && max(a,b) >= b
ensures max(a,b) == a || max(a,b) == b
{}
/*
**Q3.** 아래 함수에 적절한 `requires`를 추가해서 squiggle이 안 뜨게 만드시오.
```dafny
function safeDiv(a: int, b: int): int
{
  a / b
}
*/
function safeDiv(a :int, b:int) : int
requires b != 0
{
    a/b
}
 /*
 ## Part II. 패턴매칭 & Datatype (Lecture 3, Lab1 Part B)

**Q4.** 다음 datatype을 정의하시오: 신호등 상태를 나타내는 
`signal = Green | Yellow | Red`. `nextSignal(s: signal): signal`을 
`Green -> Yellow -> Red -> Green` 순서로 순환하도록 작성하시오.
*/
datatype signal = Green | Yellow | Red
function nextSignal(s : signal) :signal{
    match s
    case Green => Yellow
    case Yellow => Red
    case Red => Green
}

/*
**Q5.** `month` (Jan..Dec)과 `isLeapYear`가 주어졌다고 가정하고, 아래 요구사항의 함수 `daysInMonth`를 작성하시오:
- 31일: Jan, Mar, May, Jul, Aug, Oct, Dec
- 30일: Apr, Jun, Sep, Nov
- Feb: `isLeapYear`가 참이면 29, 아니면 28

이후 `daysInMonth(m, true) >= 28` 임을 증명하는 lemma를 작성하시오 (`{}`으로 증명 가능해야 함).
*/
datatype month = Jan| Mar| May| Jul| Aug| Oct| Dec | Apr| Jun| Sep| Nov | Feb

function daysInMonth( m : month, isLeapYear : bool) : nat{
    match m
    case Jan| Mar| May| Jul| Aug| Oct| Dec => 31
    case Apr| Jun| Sep| Nov => 30
    case Feb => if isLeapYear then 29 else 28
}
lemma daysInMonth_LeapYear(m : month, isLeapYear : bool)
ensures daysInMonth(m,true) >= 28{}


datatype list<T> = Nil | Cons(hd: T, tl: list<T>)
function length<T>(l: list<T>): nat { 
    match l case Nil => 0 case Cons(_,xs) => 1+length(xs) }
function append<T>(l1: list<T>, l2: list<T>): list<T> { 
    match l1 case Nil => l2 case Cons(x,xs) => Cons(x,append(xs,l2)) }
/*
## Part III. 리스트 재귀 (Lecture 4~5, Lab2)

**Q6.** `last<T>(l: list<T>): T` 함수를 작성하시오 (리스트의 마지막 원소를 리턴).
 빈 리스트에 대해서는 정의되지 않도록 적절한 `requires`를 추가하시오.
*/
function last<T>(l:list<T>) : T
requires l != Nil
{
    if l.tl == Nil then l.hd else last(l.tl)
}
/*
**Q7.** `contains<T(==)>(x: T, l: list<T>): bool`을 작성하고 (제네릭 동등비교 필요), 
다음 lemma를 `{}` body로 증명하시오:
```dafny
*/
function contains<T(==)>(x: T, l: list<T>): bool{
    match l
    case Nil => false
    case Cons(hd,tl) => if hd == x then true else contains(x,tl) 
}
lemma contains_append<T>(x: T, l1: list<T>, l2: list<T>)
  ensures contains(x, append(l1,l2)) <==> contains(x,l1) || contains(x,l2)
  {}
/*
**Q8.** (Lab2 스타일) `take`와 `drop`이 주어졌을 때 다음을 증명하는 lemma를 작성하시오 (`{}`로 증명 가능):
*/
function take<T>(n : nat, l : list<T>) : list<T>{
  if n == 0 then Nil
  else
  match l
  case Nil => Nil
  case Cons(x,xs) => Cons(x,take(n-1,xs))
}
function drop<T>(n : nat, l : list<T>) : list<T>{
  if n == 0 then l
  else
  match l
  case Nil => Nil
  case Cons(x,xs) => drop(n-1,xs)
}
function min(a : int, b : int) : int{
    if a>b then b else a
}
lemma Q8<T>(n:nat,l:list<T>)
ensures length(take(n,l)) == min(n, length(l)){}
 
/*
**Q9. (실전 난이도)** `reverse`가 다음처럼 정의되어 있다:
`length(reverse(l)) == length(l)`을 증명하는 lemma를 작성하시오. 
필요하다면 `lengthAppend` 보조 lemma(주어진 것으로 가정)를 호출해서 증명하시오. 
(`{}`만으로는 증명이 안 될 수도 있음 — 왜 안 되는지, 그리고 어떻게 고치는지 설명하시오.)
*/
function reverse<T>(l: list<T>): list<T> {
  match l case Nil => Nil case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
}
lemma length_append<T>(l1 : list<T>, l2 : list<T>)
ensures length(append(l1,l2)) == length(l1) + length(l2){}

lemma length_reverse<T>(l : list<T>)
ensures length(reverse(l)) == length(l) 
// length(append(reverse(xs),Cons(x,Nil)))
{
    match l
    case Nil => 
    case Cons(x,xs) => {
        length_reverse(xs);
        length_append(reverse(xs),Cons(x,Nil));
    }
}

/*
## Part IV. 이진트리 / BST (Lab3 Part B)

**Q10.** `sumKeys(t: btree<int>): int` 함수를 작성하시오 (모든 노드의 key를 합산).
*/
datatype option<V> = None | Some(v : V)
datatype btree<V> = Lf | Node(k: int, value: V, left: btree, right: btree)
function size<V>(t: btree<V>): nat { 
    match t case Lf => 0 case Node(_,_,lt,rt) => 1+size(lt)+size(rt) }
function lookup<T>(key : int, t:btree<T>): option<T>{
  match t
  case Lf => None
  case Node(k,v,lt,rt) =>
    if k == key 
    then Some(v)
    else if key < k
    then lookup(key,lt)
    else lookup(key,rt)
}
function insert_tree<V>(key : int, value : V, t : btree<V>) : btree<V>{
  match t
  case Lf => Node(key, value, Lf, Lf)
  case Node(k, v, lt, rt) =>
    if k == key then Node(key, value, lt, rt)
    else if key < k then Node(k, v, insert_tree(key, value, lt), rt) 
    else Node(k, v, lt, insert_tree(key, value, rt))               
}

function sumKeys(t:btree<int>) : int {
    match t
    case Lf => 0
    case Node(k,v,lt,rt) => k + sumKeys(lt) + sumKeys(rt)
}
/*
**Q11.** `contains_key(key: int, t: btree<V>): bool`을 (순서를 이용하지 않고 그냥 순회로) 작성하고, 
`insert_tree`가 주어졌다고 가정할 때 다음을 증명하시오:

(이건 Lab3에 있던 것과 동일 — 왜 `{}`만으로 증명되는지 설명하시오.)
*/
//function contains_key(key : int, t: btree<V>):bool{}
lemma lookup_insert<V>(k: int, value: V, t: btree<V>)
  ensures lookup(k, insert_tree(k, value, t)) == Some(value){}


  
/*
**Q12. (스트레치)** `insert_only_one` 
lemma (Lab3 Ex13)가 왜 빈 body로는 증명이 안 되는지 설명하고, 
증명에 필요한 핵심 보조 정리(`member_append`)를 어디서/왜 호출해야 하는지 서술하시오.
*/

/*
## Part V. Termination / decreases (Lecture 7, Lab3 Part C)

**Q13.** 다음 함수가 termination 체크를 통과하도록 `decreases` 절을 추가하시오:
*/
function countDown(n: nat): list<nat>
decreases n
{
  if n == 0 then Cons(0, Nil) else Cons(n, countDown(n-1))
}
/*
**Q14.** 아래 `collatzSteps` 함수는 Dafny가 termination을 증명 못 한다 
(실제로 정지성이 알려지지 않은 문제이기 때문). 왜 `decreases` 절을 붙일 수 없는지 한두 문장으로 설명하시오.
```dafny
function collatzSteps(n: nat): nat
  requires n > 0
{
  if n == 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps(n / 2)
  else 1 + collatzSteps(3*n + 1)
}
*/

/*
## Part VI. Quantifiers — forall/exists (Lecture 10~11) ⭐ 시험 자주 나오는 부분

**Q15.** 다음 lemma의 `ensures`를 완성하시오 — "임의의 자연수 x에 대해, x보다 항상 더 큰 자연수가 존재한다":
*/
lemma noMaxNat()
  ensures forall x: nat :: exists y: nat :: y > x

/*

**Q16.** 아래는 Lecture10 `subset_forall`의 핵심 증명 스케치다. 
`subset(A,B) <==> forall x | member(x,A) :: member(x,B)`
 를 증명할 때 두 방향 중 **어느 쪽이 더 어려운지**, 그리고 어려운 방향에서 왜 
 `var x0 :| ...` (witness 추출)이 필요한지 설명하시오.

*/
/*
**Q17.** 다음 프레디케이트가 주어졌을 때:
다음을 증명하는 lemma를 작성하시오 (Lecture10의 `subset_forall`과 같은 스타일):



(단, `member`는 위에서 정의한 것과 동일)
*/
function member(x : int, l : list<int>) : bool {
  match l
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}

predicate allPositive(l: list<int>) {
  match l case Nil => true case Cons(x,xs) => x > 0 && allPositive(xs)
}

lemma allPositive_forall(l: list<int>)
  ensures allPositive(l) <==> forall x | member(x,l) :: x > 0
  

/*
**Q18.** `exists`가 있는 명제를 증명할 때, Dafny에게 **witness(증거)를 어떻게 알려주는지** 두 가지 방법(직접 값 주기 / `:|` 로 뽑아내기)을 예시와 함께 설명하시오.

**Q19. (Lecture11 스타일)** 아래 lemma 두 개가 있다. 첫 번째가 참이라고 가정할 때 두 번째를 증명하시오 (forall instantiation 연습):
```dafny
predicate q(x: int)
predicate r(x: int)

lemma given()
  ensures forall x | 0 < x :: q(x)

lemma useIt(y: nat)
  requires forall x | 0 < x :: q(x)
  ensures q(y + 1)
{
  // 여기 채우기
}
```
*/