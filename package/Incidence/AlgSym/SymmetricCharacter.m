freeze;
 
intrinsic SymmetricCharacter(s::AlgSymElt) -> AlgChtrElt
{computes the character of the symmetric group corresponding to the symmetric function}
require IsHomogeneous(s): "only for homogenous symmetric functions";
require Degree(s) gt 0: "only for symmetric function of degree gt 0";
if not HasSchurBasis(Parent(s)) then
   sf := SFA(BaseRing(Parent(s)))!s;
else
   sf := s;
end if;

C:=Coefficients(sf);
P:=Partitions(sf);

w := Weight(P[1]);
l := #C;
res := Zero(CharacterRing(Sym(w)));
for i in [1..l] do
    res +:= SymmetricCharacter(P[i]) * C[i];
end for;
return res;
end intrinsic;

//intrinsic AlternatingCharacter(p::SeqEnum,I::RngIntElt) -> RngElt
//{ computes the irreducible charcter of the alternating group labelled by the partition p,
  //in the case of a self conjugate partition i (0 or 1) decides which of the two possible
  //irreducible is choosen  }
//i := Weight(p);
//cl := Classes(Alt(i));
//d := [CyclotomicField(1)|];k:=1;
//for j in cl do
    //d := d cat [AlternatingCharacterValue(p,I,j[3])];
    //k +:= 1;
//end for;
//R:=CharacterRing(Alt(i));
//res := R!d;
//AssertAttribute(res, "IsIrreducible", true);
//return res;
//end intrinsic;
//
//intrinsic AlternatingCharacter(p::SeqEnum) -> RngElt
//{ computes the irreducible charcter of the alternating group labelled by the partition p,
  //in the case of a self conjugate partition i (0 or 1) decides which of the two possible
  //irreducible is choosen  }
//res := AlternatingCharacter(p,0);
//return res;
//end intrinsic;

//intrinsic AlternatingCharacterTable(n::RngIntElt) -> SeqEnum
//{ computes the charactertable of the alternating group
//}
//require n ge 3: "degree of the alternating group should be >= 3";
//if n eq 3 then return CharacterTable(Alt(3)); end if;
//G := Alt(n);
//cl := Classes(G);
//P := Partitions(n);
//R:= CharacterRing(G);
//for p in P do
    //cp := ConjugatePartition(p);

    //if p le cp then
    //d := [CyclotomicField(1)|];k:=1;
    //for j in cl do
        //d cat:=  [AlternatingCharacterValue(p,0,j[3])];
        //k +:= 1;
    //end for;
    //AssertAttribute(R!d, "IsIrreducible", true);
    //end if;
//
    //if p eq cp then
    //d := [CyclotomicField(1)|];k:=1;
    //for j in cl do
        //d cat:=  [AlternatingCharacterValue(p,1,j[3])];
        //k +:= 1;
    //end for;
    //AssertAttribute(R!d, "IsIrreducible", true);
//
    //end if;
//end for;
//return KnownIrreducibles(G);
//end intrinsic;

