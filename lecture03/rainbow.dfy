datatype colour = Red | Orange | Yellow | Green | Blue | Indigo
  | Violet

function isRedWithEquality(c : colour) : bool {
    c == Red
}

// write is-yellow with built-in discriminator
predicate isyellowwithdiscriminatior(c : colour) { c.Green? }

method Main()
{
  print "red=", isyellowwithdiscriminatior(Red), "\n";
  print "green=",isyellowwithdiscriminatior(Green), "\n";


}

