function CharacterTrace(c)
  K:=CharacterField(c);
  if Type(K) eq FldRat then return c; end if;
  return Parent(c)![AbsoluteTrace(K!x): x in Eltseq(c)];
end function;


for n in [2..63] do
if n mod 10 eq 0 then n; end if;
if n mod 64 eq 0 then continue; end if;
for G in SmallGroups(n: Warning:=false) do

  GroupName(G),Cputime();
  
  // IsHyperelementary

  ishyp:=exists{Cdata: Cdata in NormalSubgroups(G) | IsCyclic(C) and (((#C eq #G) or 
    ((GCD(#C,#G div #C) eq 1) and IsPrimePower(#G div #C)))) where C is Cdata`subgroup};
  assert ishyp eq IsHyperelementary(G);    
  
  // BurnsideCokernel, IsPermutationCharacter

  C:=CharacterTable(G);
  CT:=[CharacterTrace(c): c in C];
  CTS:=[SchurIndex(C[i])*CT[i]: i in [1..#C]];

  charlist:=Set(C cat CT cat CTS);
  
  L:=Lattice(Matrix([[Rationals()!x: x in Decomposition(C,PermutationCharacter(G,H`subgroup))]: 
    H in Subgroups(G)]));
    
  burn:=true;
  for c in charlist do
    perm:=AbsoluteDegree(CharacterField(c)) eq 1 and
      IsCoercible(L,[Rationals()!x: x in Decomposition(C,c)]);
    if (c in CTS) and not perm then burn:=false; end if;
    assert perm eq IsPermutationCharacter(c);
  end for;
  assert burn eq (#BurnsideCokernel(G) eq 1);

  // IsQGroup

  assert IsQGroup(G) eq (C eq CT);

end for;
end for;


">>> TESTING DONE <<<";
