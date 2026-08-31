# COMP1600/COMP6260 모의 중간고사 연습문제
### (Lab1~4, Lecture10~11 내용 기반)

지금까지 본 Dafny 랩(list/append/reverse/zip/tree/BST)과 강의(quantifier, subset-forall) 내용을 종합해서 만든 연습 문제입니다. 시험처럼 시간 재고 풀어보세요. 정답/힌트는 맨 아래 "해설" 섹션에 있습니다.

---

## Part I. 함수/프레디케이트 기본기 (Lecture 2~3, Lab1)

**Q1.** 다음 datatype이 주어졌을 때,
```dafny
datatype shape = Circle(radius: nat) | Rect(w: nat, h: nat)
```
- `area(s: shape): nat` 함수를 작성하시오. (원의 넓이는 `radius*radius*3`으로 근사해서 계산해도 됨 — 정수 연산만 사용)
- `perimeter(s: shape): nat` 함수도 작성하시오.

**Q2.** `nat` 두 개를 받아 더 큰 값을 리턴하는 `max(a: nat, b: nat): nat` 함수를 쓰고, 다음을 만족하는 lemma를 작성하시오 (빈 body `{}` 로 증명되어야 함):
- `max(a,b) >= a && max(a,b) >= b`
- `max(a,b) == a || max(a,b) == b`

**Q3.** 아래 함수에 적절한 `requires`를 추가해서 squiggle이 안 뜨게 만드시오.
```dafny
function safeDiv(a: int, b: int): int
{
  a / b
}
```

---

## Part II. 패턴매칭 & Datatype (Lecture 3, Lab1 Part B)

**Q4.** 다음 datatype을 정의하시오: 신호등 상태를 나타내는 `signal = Green | Yellow | Red`. `nextSignal(s: signal): signal`을 `Green -> Yellow -> Red -> Green` 순서로 순환하도록 작성하시오.

**Q5.** `month` (Jan..Dec)과 `isLeapYear`가 주어졌다고 가정하고, 아래 요구사항의 함수 `daysInMonth`를 작성하시오:
- 31일: Jan, Mar, May, Jul, Aug, Oct, Dec
- 30일: Apr, Jun, Sep, Nov
- Feb: `isLeapYear`가 참이면 29, 아니면 28

이후 `daysInMonth(m, true) >= 28` 임을 증명하는 lemma를 작성하시오 (`{}`으로 증명 가능해야 함).

---

## Part III. 리스트 재귀 (Lecture 4~5, Lab2)

주어진 정의:
```dafny
datatype list<T> = Nil | Cons(hd: T, tl: list<T>)
function length<T>(l: list<T>): nat { match l case Nil => 0 case Cons(_,xs) => 1+length(xs) }
function append<T>(l1: list<T>, l2: list<T>): list<T> { match l1 case Nil => l2 case Cons(x,xs) => Cons(x,append(xs,l2)) }
```

**Q6.** `last<T>(l: list<T>): T` 함수를 작성하시오 (리스트의 마지막 원소를 리턴). 빈 리스트에 대해서는 정의되지 않도록 적절한 `requires`를 추가하시오.

**Q7.** `contains<T(==)>(x: T, l: list<T>): bool`을 작성하고 (제네릭 동등비교 필요), 다음 lemma를 `{}` body로 증명하시오:
```dafny
lemma contains_append<T(==)>(x: T, l1: list<T>, l2: list<T>)
  ensures contains(x, append(l1,l2)) <==> contains(x,l1) || contains(x,l2)
```

**Q8.** (Lab2 스타일) `take`와 `drop`이 주어졌을 때 다음을 증명하는 lemma를 작성하시오 (`{}`로 증명 가능):
```
length(take(n,l)) == min(n, length(l))
```

**Q9. (실전 난이도)** `reverse`가 다음처럼 정의되어 있다:
```dafny
function reverse<T>(l: list<T>): list<T> {
  match l case Nil => Nil case Cons(x,xs) => append(reverse(xs), Cons(x,Nil))
}
```
`length(reverse(l)) == length(l)`을 증명하는 lemma를 작성하시오. 필요하다면 `lengthAppend` 보조 lemma(주어진 것으로 가정)를 호출해서 증명하시오. (`{}`만으로는 증명이 안 될 수도 있음 — 왜 안 되는지, 그리고 어떻게 고치는지 설명하시오.)

---

## Part IV. 이진트리 / BST (Lab3 Part B)

주어진 정의:
```dafny
datatype btree<V> = Lf | Node(k: int, value: V, left: btree, right: btree)
function size<V>(t: btree<V>): nat { match t case Lf => 0 case Node(_,_,lt,rt) => 1+size(lt)+size(rt) }
```

**Q10.** `sumKeys(t: btree<int>): int` 함수를 작성하시오 (모든 노드의 key를 합산).

**Q11.** `contains_key(key: int, t: btree<V>): bool`을 (순서를 이용하지 않고 그냥 순회로) 작성하고, `insert_tree`가 주어졌다고 가정할 때 다음을 증명하시오:
```dafny
lemma lookup_insert<V>(k: int, value: V, t: btree<V>)
  ensures lookup(k, insert_tree(k, value, t)) == Some(value)
```
(이건 Lab3에 있던 것과 동일 — 왜 `{}`만으로 증명되는지 설명하시오.)

**Q12. (스트레치)** `insert_only_one` lemma (Lab3 Ex13)가 왜 빈 body로는 증명이 안 되는지 설명하고, 증명에 필요한 핵심 보조 정리(`member_append`)를 어디서/왜 호출해야 하는지 서술하시오.

---

## Part V. Termination / decreases (Lecture 7, Lab3 Part C)

**Q13.** 다음 함수가 termination 체크를 통과하도록 `decreases` 절을 추가하시오:
```dafny
function countDown(n: nat): list<nat>
{
  if n == 0 then Cons(0, Nil) else Cons(n, countDown(n-1))
}
```

**Q14.** 아래 `collatzSteps` 함수는 Dafny가 termination을 증명 못 한다 (실제로 정지성이 알려지지 않은 문제이기 때문). 왜 `decreases` 절을 붙일 수 없는지 한두 문장으로 설명하시오.
```dafny
function collatzSteps(n: nat): nat
  requires n > 0
{
  if n == 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps(n / 2)
  else 1 + collatzSteps(3*n + 1)
}
```

---

## Part VI. Quantifiers — forall/exists (Lecture 10~11) ⭐ 시험 자주 나오는 부분

**Q15.** 다음 lemma의 `ensures`를 완성하시오 — "임의의 자연수 x에 대해, x보다 항상 더 큰 자연수가 존재한다":
```dafny
lemma noMaxNat()
  ensures ______________________
{}
```

**Q16.** 아래는 Lecture10 `subset_forall`의 핵심 증명 스케치다. `subset(A,B) <==> forall x | member(x,A) :: member(x,B)` 를 증명할 때 두 방향 중 **어느 쪽이 더 어려운지**, 그리고 어려운 방향에서 왜 `var x0 :| ...` (witness 추출)이 필요한지 설명하시오.

**Q17.** 다음 프레디케이트가 주어졌을 때:
```dafny
predicate allPositive(l: list<int>) {
  match l case Nil => true case Cons(x,xs) => x > 0 && allPositive(xs)
}
```
다음을 증명하는 lemma를 작성하시오 (Lecture10의 `subset_forall`과 같은 스타일):
```dafny
lemma allPositive_forall(l: list<int>)
  ensures allPositive(l) <==> forall x | member(x,l) :: x > 0
```
(단, `member`는 위에서 정의한 것과 동일)

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

---

## Part VII. 종합 / 응용 문제

**Q20. (종합)** `zip`, `unzip`이 Lab2처럼 정의되어 있다고 가정할 때, 다음을 증명하시오:
```dafny
lemma unzip_zip<A,B>(l1: list<A>, l2: list<B>)
  requires length(l1) == length(l2)
  ensures unzip(zip(l1,l2)) == (l1, l2)
```
(힌트: `zip`이 짧은 쪽에 맞춰 자르므로 `length` 같다는 전제가 필요함. 귀납 구조로 접근.)

**Q21. (subset 관련 종합, Lecture10 lset 스타일)** `union(A,B)` (두 lset의 합집합, 그냥 append 후 중복 허용) 이 주어졌을 때:
```dafny
function union(A: lset, B: lset): lset { append(A,B) }
```
다음을 증명하시오:
```dafny
lemma union_subset(A: lset, B: lset, C: lset)
  requires subset(A,C) requires subset(B,C)
  ensures subset(union(A,B), C)
```

---

## 해설 / 힌트 (정답 스포일러 주의)

<details>
<summary>Q1~Q5 힌트</summary>

- Q1: `match s case Circle(r) => r*r*3 case Rect(w,h) => w*h` 식으로 하면 됨. 둘레는 `Circle(r) => 2*r*3` 근사, `Rect(w,h) => 2*(w+h)`.
- Q2: `if a >= b then a else b`. `ensures`는 두 줄 다 필요 (하나만 있으면 Dafny가 자동으로 못 미는 경우가 있음 — 직접 확인해볼 것).
- Q3: `requires b != 0`
- Q4: `match s case Green => Yellow case Yellow => Red case Red => Green`
- Q5: `daysUpToStartOf` 스타일로 Lab4 Q1과 거의 동일. `{}`으로 안 되면 `if`/`match` 분기를 다 커버했는지 확인.
</details>

<details>
<summary>Q6~Q9 힌트</summary>

- Q6: `requires l != Nil` (또는 `l.Cons?`), body는 `match l case Cons(x, Nil) => x case Cons(_, xs) => last(xs)`.
- Q7: `contains` 정의는 `member`와 동일한 패턴. lemma는 `{}`로 Dafny가 귀납으로 증명해줌 (Lab2/3에서 `member_append`가 이미 `{}`로 증명됐던 것과 같은 이유 — append의 정의를 그대로 따라가는 구조적 귀납).
- Q8: Lab2 Ex8 `takeLength`와 동일 — `{}`로 증명됨.
- Q9: `{}`만으로는 실패한다. 이유: `length(reverse(Cons(x,xs))) = length(append(reverse(xs), Cons(x,Nil)))`인데, Dafny가 `length(append(...))`를 `length`+`length`로 자동으로 안 풀어줌 (별개의 재귀 함수라서). `lengthAppend(reverse(xs), Cons(x,Nil))`를 **명시적으로 호출**해서 그 사실을 alert 해줘야 함. 즉 body를:
```dafny
lemma length_reverse<T>(l: list<T>)
  ensures length(reverse(l)) == length(l)
{
  match l
  case Nil =>
  case Cons(x, xs) => {
    length_reverse(xs);
    lengthAppend(reverse(xs), Cons(x, Nil));
  }
}
```
</details>

<details>
<summary>Q10~Q12 힌트</summary>

- Q10: `match t case Lf => 0 case Node(k,_,lt,rt) => k + sumKeys(lt) + sumKeys(rt)`
- Q11: `lookup_insert`가 `{}`로 증명되는 이유 — `insert_tree(key,value,t)`의 정의를 풀면 항상 `k==key`인 노드가 생기도록 구성되어 있고, `lookup`도 마찬가지로 그 노드를 바로 찾는 구조라 Dafny의 자동 unfolding(함수 정의 펼치기) + SMT 솔버로 바로 풀림. 즉 두 함수가 "같은 재귀 구조"를 따라가기 때문.
- Q12: `insert_only_one`이 실패하는 이유 — `size(insert_tree(...))`와 `keys(t)`의 관계는 `keys`가 `append(keys(lt), Cons(k,keys(rt)))`로 정의되어 있어서, `member(key, keys(t))`가 `append`를 뚫고 `lt`/`rt`/`k` 각각에 대해 뭘 의미하는지 Dafny가 자동으로 못 짚어냄. `member_append(key, keys(lt), Cons(k,keys(rt)))`를 명시적으로 호출해서 "append 안에서 멤버십이 어떻게 분해되는지"를 알려줘야 재귀 호출(`insert_only_one(key,v,lt)` 등)의 전제조건을 만족시킬 수 있음.
</details>

<details>
<summary>Q13~Q14 힌트</summary>

- Q13: `decreases n`
- Q14: Collatz 추측(3n+1 문제)은 모든 자연수에 대해 유한 스텝 안에 1로 수렴하는지가 **아직 수학적으로 증명되지 않은 미해결 문제**이기 때문에, 어떤 값이 매 호출마다 "단조 감소"하는지 알 수 있는 decreases metric을 우리가 제시할 수 없음. 즉 Dafny가 termination을 거부하는 게 아니라, 애초에 우리가 종료성을 증명할 수학적 근거가 없음.
</details>

<details>
<summary>Q15~Q19 힌트</summary>

- Q15: `ensures forall x: nat :: exists y: nat :: y > x` (smallestExists류와 반대 형태)
- Q16: subset(A,B) => forall 방향은 쉬움 (member_subset 재귀로 바로 됨). 반대 방향(forall => subset)이 어려운 이유는 `subset`이 구조적 귀납(리스트를 따라 내려가며 검사)인데 `forall`은 그런 구조 정보가 없기 때문. `A`가 subset이 아니라고 가정하고(반증법), `A = Cons(x,xs)`로 분해한 뒤 `xs`가 subset이 아니라는 사실로부터 `var x0 :| member(x0,xs) && !member(x0,B)`로 **반례 x0을 명시적으로 꺼내야** `exists x0 :: member(x0,A) && !member(x0,B)`, 즉 forall의 부정을 만들 수 있음. Dafny는 존재성 증거를 스스로 못 찾으므로 `:|`로 직접 뽑아줘야 함.
- Q17: `subset_forall`과 완전히 동일한 스켈레톤 — `member`, `allPositive`, `x>0`으로 이름만 바꾸면 됨.
- Q18: (1) 직접 값: `assert exists x :: P(x)` 대신 `assert P(5)` 후 자동으로 존재성 도출되도록 유도하거나 `exists x :: P(x)`를 증명할 constructive proof에서는 그냥 그 값을 쓰면 Dafny가 인식. (2) `var w :| P(w);` — 이미 `exists x :: P(x)`가 참임이 알려진 상태(가정 또는 이전 assert)에서 Hilbert-choice 스타일로 증거값을 이름 붙여 꺼내는 것.
- Q19: `useIt`의 body:
```dafny
{
  given();
}
```
`given()`을 호출하면 `forall x | 0<x :: q(x)`가 컨텍스트에 들어오고, Dafny가 `y+1 > 0` (y:nat이므로 자명)이라는 걸 확인 후 자동으로 `q(y+1)`을 이 forall에서 instantiate해서 증명해줌. (참고: `requires`에 이미 그 forall이 있으므로 `given()` 호출조차 필요 없을 수도 있음 — `{}` 로 될지 직접 확인해볼 것)
</details>

<details>
<summary>Q20~Q21 힌트</summary>

- Q20: `l1`, `l2` 둘 다 Nil이거나 둘 다 Cons인 경우로 나눠서 귀납. `length` 같다는 requires 덕분에 `l1=Nil <=> l2=Nil`이 보장됨. body는 대략:
```dafny
{
  if l1.Cons? {
    unzip_zip(l1.tl, l2.tl);
  }
}
```
- Q21: `union_subset`은 `subset_forall` (또는 `member_append`)을 이용해서 증명. `subset(append(A,B),C)`를 풀면 `member(x,append(A,B)) ==> member(x,C)`인데, `member_append`로 `member(x,append(A,B)) <==> member(x,A)||member(x,B)`를 얻고, 각각 `subset(A,C)`, `subset(B,C)`의 정의(`subset_forall` 경유)로 마무리. `{}`만으로는 안 될 가능성 높음 — `member_append`와 `subset_forall`을 명시 호출해볼 것.
</details>

---

### 시험 팁 요약
1. **`{}` 빈 body로 증명이 안 될 때 체크리스트**: (a) `append`/다른 재귀함수를 관통하는 사실인가? → 관련 보조 lemma를 explicit하게 호출. (b) `match`/`if`로 케이스를 다 나눴는가? (c) 재귀 호출(귀납가정)을 실제로 사용했는가?
2. **forall ⟺ predicate 증명 패턴**: 쉬운 방향(구조적 귀납 그대로) vs 어려운 방향(반증법 + `:|` witness 추출)을 항상 구분해서 접근.
3. **decreases**: "무엇이 매 재귀 호출마다 엄밀히 작아지는가"를 항상 먼저 찾고 시작.
4. **BST 계열**: `insert_tree`/`lookup`처럼 서로 "같은 구조"를 따라가는 함수 쌍은 `{}`로 잘 풀리고, `keys`/`size`처럼 `append`를 매개로 연결된 함수는 거의 항상 `member_append`/`lengthAppend` 류의 명시적 호출이 필요.
</details>