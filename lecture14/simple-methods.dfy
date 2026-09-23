/* What *must* we assign to?  What *mustn't* we assign to? */
method maxMethod(i : int, j : int) returns (mx : int, mn :int)
{
    if i < j { return j,i; }
    return i,j;
    // i := 3;
}
function max(i :int, j : int) : int
{
    if i< j then j
    else i
}
method Main()
{
    // dafny is fussy here; can't put parens around x,n
    var max1, min := maxMethod(10,10);
    print "max is ", max, "min = ",min,"\n";
}