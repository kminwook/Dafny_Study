function swap_ish(x:int,y:int) : (int,int) {
    (y,x)
}

function swap(xy:(int,int)) : (int,int) {
    (xy.0,xy.1)
}

// implement f(x,y) = x^2 + x * y 
// in two different styles

function f1(x:int, y:int) :int
{
    x*x+x*y
}

function f2(xy:(int,int)) :int
{
    xy.0*xy.0+xy.0*xy.1
}

function f3(xy:(int,int)) :int
{
    var(x,y) := xy;
    x*x+x*y

}

method Main()
{
    print "A tuple: ", (3,true), "\n";
    print "f1(2,3) = ",f1(2,3), "\n";
    print "f2(2,3) = ",f2((2,3)), "\n";
}

// 3D vectors would be fun