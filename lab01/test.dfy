datatype light = Red | Orange | Green
datatype shape =
    Rectangle(height : nat, width : nat)
  | Square(side : nat)
  | Triangle(base : nat, height : nat)
datatype month =
  Jan | Feb | Mar | Apr | May | Jun |
  Jul | Aug | Sep | Oct | Nov | Dec
datatype list<T> = Nil | Cons(hd : T, tl : list<T>)

function distSquared(v : (int,int)) : int
{
  v.0*v.0 + v.1*v.1
}
function dotProduct(u : (int,int), v : (int,int)) : int
{
  u.0 * v.0 + u.1 * v.1
}
predicate perpendicular(u : (int,int), v : (int,int))
{
  if dotProduct(u,v) == 0 
    then true
    else false
}
function divides(m : nat, n : nat) : bool
{
  if (m==0 && n==0) || (m != 0 && n%m==0)
    then true
    else false
}
predicate inRange(lo : int, x : int, hi : int)
{
  if lo <= x <= hi
    then true
    else false
}
function withTax(cents : int) : int
  requires cents >= 0
  {
    var tax := cents/10 ;
    cents + tax
  }
function next(l : light) : light
{
  match l {
    case Red => Orange
    case Orange => Green
    case Green => Red
  }
}
function area(s : shape) : nat
{
  match s
  case Rectangle(h,w) => h*w
  case Square(l) => l*l
  case Triangle(base, height) => base*height/2
}
function monthLen(m : month, isLeap : bool) : nat
{
  match m
  case Jan | Mar | May | Jul | Aug | Oct | Dec => 31
  case Apr | Jun | Sep | Nov => 30
  case Feb => if isLeap then 29 else 28
}
predicate isLeapYear (y:nat)
{
  if y % 400 == 0 then true
  else if y % 100 == 0 then false
  else y % 4 == 0
} /* write stuff here! */

// write testing lemmas for the test cases in the comment above
lemma isLY2024()
  ensures isLeapYear(2024){}
lemma isLY1900()
  ensures isLeapYear(2000){}
lemma isLY2000()
  ensures isLeapYear(2000){}
function exp(m : nat, p : nat) : nat
{
  if p == 0 then 1 else m * exp(m,p-1)
}
function gradient(p1 : (int,int), p2 : (int,int)) : int
  requires p2.0 != p1.0
{
  (p2.1 - p1.1) / (p2.0 - p1.0)
}
function makeItBigger(i : int) : int
  ensures makeItBigger(i) > i
{
  i+1
}
function fact(n : nat) : nat
{
  if n < 2 then 1 else n * fact(n - 1)
}

lemma factTest1()
  ensures fact(4) == 24
  // TODO: write the ensures for "fact(4)"
{}
lemma factTest2()
  ensures fact(6) == 720{}

function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, xs) => 1 + length(xs)
}
function append<T>(l1 : list<T>, l2 : list<T>) : list<T>{
  match l1
    case Nil => l2
    case Cons(x,xs) => Cons(x,append(xs,l2))
}
method Main()
{
  var intList := Cons(10, Cons(20, Cons(30, Nil))); 
  print "dotProduct((2,3),(5,6)) = ", dotProduct((2,3),(5,6)), "\n";
  print "prependicular = ", perpendicular((0,2),(2,3)), "\n";
  print "divides (2,4) =", divides(2,4),"\n";
  print "inRange (10,40,30) =", inRange(10,40,30), "\n";
  print "withTax(10) = ", withTax(10), "\n";
  print "next(Red) =", next(Red), "\n";
  print "area(Square(10)) = ", area(Square(10)), "\n";
  print "monthLen(Feb,true) = ", monthLen(Feb,false), "\n";
  print "isLeapYear(2000) = ", isLeapYear(2000) , "\n";
  print "exp(3,4) = ", exp(3,4) , "\n";
  print "gradient((70,23),(52,2)) = ", gradient((70,23),(52,2)), "\n";
  print "makeItbigger(10) =", makeItBigger(10), "\n";
  print "length([1,2,3] = ", length(intList),"\n";
}