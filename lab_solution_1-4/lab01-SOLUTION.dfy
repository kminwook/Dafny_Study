/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 1  (Week 2) -- SOLUTIONS

   Reference version of lab01.dfy. Every function is defined and
   every lemma verifies; the whole file should be "all green" in
   VS Code.
   ============================================================ */


/* ---- PART A -- Expressions, functions and types ---- */

function distSquared(v : (int,int)) : int
{
  v.0 * v.0 + v.1 * v.1
}

function dotProduct(u : (int,int), v : (int,int)) : int
{
  u.0 * v.0 + u.1 * v.1
}

predicate perpendicular(u : (int,int), v : (int,int))
{
  dotProduct(u, v) == 0
}

function divides(m : nat, n : nat) : bool
{
  (m == 0 && n == 0) || (m != 0 && n % m == 0)
}

predicate inRange(lo : int, x : int, hi : int)
{
  lo <= x <= hi
}

function withTax(cents : int) : int
  requires cents >= 0
{
  var tax := cents / 10;
  cents + tax
}


/* ---- PART B -- Datatypes and pattern-matching ---- */

datatype light = Red | Orange | Green

function next(l : light) : light
{
  match l
  case Red    => Green
  case Green  => Orange
  case Orange => Red
}

datatype shape =
    Rectangle(height : nat, width : nat)
  | Square(side : nat)
  | Triangle(base : nat, height : nat)

function area(s : shape) : nat
{
  match s
  case Rectangle(h, w) => h * w
  case Square(sd)      => sd * sd
  case Triangle(b, h)  => b * h / 2
}

datatype month =
  Jan | Feb | Mar | Apr | May | Jun |
  Jul | Aug | Sep | Oct | Nov | Dec

function monthLen(m : month, isLeap : bool) : nat
{
  match m
  case Jan | Mar | May | Jul | Aug | Oct | Dec => 31
  case Apr | Jun | Sep | Nov => 30
  case Feb => if isLeap then 29 else 28
}

predicate isLeapYear (year: nat)
{
  year % 4 == 0 && (year % 100 == 0 ==> year % 400 == 0)
}

lemma isLY2024() ensures isLeapYear(2024) {}
lemma isLY1900() ensures !isLeapYear(1900) {}
lemma isLY2000() ensures isLeapYear(2000) {}


/* ---- PART C -- Recursion, and simple specifications ---- */

function exp(m : nat, p : nat) : nat
{
  if p == 0 then 1 else m * exp(m, p - 1)
}

function gradient(p1 : (int,int), p2 : (int,int)) : int
  requires p2.0 != p1.0
{
  (p2.1 - p1.1) / (p2.0 - p1.0)
}

function makeItBigger(i : int) : int
  ensures makeItBigger(i) > i
{
  i + 1
}

function fact(n : nat) : nat
{
  if n < 2 then 1 else n * fact(n - 1)
}

lemma factTest1()
  ensures fact(4) == 24
{}

lemma factTest2()
  ensures fact(6) > 100
{}


/* ---- PART D -- A gentle first look at recursive types ---- */

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)

// worked example (given to students)
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

function member(x : int, A : list<int>) : bool
{
  match A
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}

datatype tree<V> = Lf | Node(key : string, val : V, left : tree<V>, right : tree<V>)

function size<V>(t : tree<V>) : nat
{
  match t
  case Lf => 0
  case Node(_, _, l, r) => 1 + size(l) + size(r)
}
