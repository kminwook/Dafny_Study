// write a function f to combine three booleans
function f(a : bool, b : bool, c : bool) : bool
{
    (a== b) || !c
}

method Main()
{
    print true || false, "\n";
    print true ==> false, "\n";
    print "f(true,false,true) = ", f(true,false,true), "\n";
}