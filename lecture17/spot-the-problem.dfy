/* Lecture 17: which of the three questions fails?
   Snippets from COMP1600 2025, tutorial 9, exercises 1 and 6. */

/* --- pair one ------------------------------------------------- */

/* fine: the guard failing IS what we want */
method problem1()
{
  var x := 20;
  while (x < 20)
    invariant x % 2 == 0
  // 20 이상 수중에 2짝수는 엄청 많아서 22일수도있고 24일수도있고 시작할때 20 이라해도 상관이 없다
  // 근데 int에다가 +1 씩 해주는 함수 표현하면 무조건 20이니까
  { x := x + 1;}
  assert x == 20;
  //assert !(x<20);
  assert x % 2 == 0;
}


method broken3()
{
  var i := 0;
  while (i < 97)
    invariant 0 <= i <= 99
   { i := i + 1; } 
  // 97,98,99 다 가능하니까 근데 i := i + 1 넣으면 무조건 97 이니까 성립된다
  assert i == 97;          // complaint 3
}
