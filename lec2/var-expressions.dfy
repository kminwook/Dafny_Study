// "let" expressions in Dafny

function expanded(x:int) : int
{
    var y := x*10;
    if y > 63 then y + 7 else y + 1
}

// if only we didn't have to keep writing x * 10 again and again and again and again

method Main()
{
    print" expanded(100) = ", expanded(100), "\n";
    print "expanded(1) =", expanded(1),"\n";

}
