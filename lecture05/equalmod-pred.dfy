function equalMod(x:int, y:int, z:int):bool
requires z != 0
{
    x % z == y % z
}

// is this really an equivalence relation?

lemma equalMod_reflexive(x:int,z:int)
requires z!=0
ensures equalMod(x,x,z){}

lemma equalMod_symmentic(x:int, y:int, z:int)
requires z != 0
requires equalMod(x,y,z)
ensures equalMod(y,x,z){}

lemma trnas(w:int, x:int, y:int,z:int)
requires z !=0
requires equalMod(w,x,z){}