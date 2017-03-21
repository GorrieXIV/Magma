freeze;

/*

  Implements 
  
  intrinsic IsHyperelementary(G::Grp: p:=0) -> BoolElt,Grp,Grp
  intrinsic IsQGroup(G::Grp) -> BoolElt
  intrinsic IsPermutationCharacter(c::AlgChtrElt) -> BoolElt
  intrinsic BurnsideCokernel(G::Grp) -> GrpAb,UserProgram,SeqEnum[AlgChtrElt] 
  
  v1.0 TD Nov 2014

*/


Z:=Integers();
Q:=Rationals();


function PrimitiveRootsN(N)              // List of generators of (Z/NZ)^*
  if N eq 1 then return []; end if;
  if IsPrime(N) then return [Z|PrimitiveRoot(N)]; end if;
  U,m:=UnitGroup(Integers(N));
  return([Z|m(g): g in Generators(U)]);
end function;


procedure SortBy(~L,f: sign:=1)
  if Type(L) eq SetEnum then
    L:=SetToSequence(L);
  end if;
  Sort(~L,func<a,b|fa lt fb select -sign else (fa eq fb select 0 else sign)
                   where fa is f(a) where fb is f(b)>);
end procedure;                


function InnerProductList(L,M)
  return &+[L[i]*M[i]: i in [1..#L]];
end function;


function CSGPS(G)             // Cyclic subgroups of G up to conjugacy
  P:=PowerMap(G);
  N:=#Codomain(P);
  pows:=[[P(i,g): i in [1..N]]: g in PrimitiveRootsN(#G)];
  perm:=sub<Sym(N)|pows>;
  C:=[sub<G|CC[o[1]][3]>: o in Orbits(perm)] where CC is ConjugacyClasses(G);
  SortBy(~C,'#');
  return C;
end function;


function RationalCharacters(G)
  RC:=RationalCharacterTable(G);
  return [RationalCharacterSchurIndex(G,i)*RC[i]: i in [1..#RC]];
end function;


intrinsic IsHyperelementary(G::Grp: p:=0) -> BoolElt,Grp,Grp
{
  If G is a finite hyperelementary (=quasielementary) group, that is a semi-direct 
  product G=C:P with C cyclic and P a p-group of order coprime to C, returns true, C, P. Otherwise returns false. The prime number p can be forced with an optional parameter p (0 by default).
}
  require Type(G) in [GrpPC,GrpPerm,GrpMat,GrpAb] and IsFinite(G) : 
    "G must be a finite group of type GrpPC,GrpPerm,GrpMat or GrpAb";
  require IsCoercible(Z,p) and ((Z!p eq 0) or IsPrime(Z!p)):
    "p must be 0 or a prime number"; 
  p:=Z!p;
                                            
  if #G eq 1 then return true,G,G; end if;

  P:=PrimeDivisors(#G);
  Sp:=sub<G|>;
  for q in P do
    S:=SylowSubgroup(G,q);
    if q eq p then Sp:=S; end if;
    if IsCyclic(S) and IsNormal(G,S) then continue; end if;
    if p ne 0 
      then if q ne p then return false,_,_; end if;
      else p:=q;     
    end if;
    Sp:=S;
  end for;
  if p eq 0 
    then return true, G, sub<G|>;
    else return true, sub<G|[SylowSubgroup(G,q): q in PrimeDivisors(#G) | 
      q ne p]>, Sp, p;
  end if;
end intrinsic;


SmallCokList:=   // Groups of order <=191 with non-trivial cokernel
  [<24,1>,<24,11>,<40,3>,<40,11>,<48,1>,<48,9>,<48,17>,<48,18>,<48,22>,
  <48,27>,<48,46>,<56,1>,<60,1>,<60,2>,<72,1>,<72,3>,<72,11>,<72,12>,<72,13>,
  <72,25>,<72,26>,<72,38>,<80,3>,<80,18>,<80,22>,<80,27>,<80,29>,<80,32>,
  <80,42>,<80,47>,<84,3>,<88,1>,<88,10>,<96,1>,<96,9>,<96,11>,<96,14>,
  <96,15>,<96,16>,<96,17>,<96,18>,<96,19>,<96,29>,<96,36>,<96,37>,<96,42>,
  <96,43>,<96,45>,<96,51>,<96,53>,<96,55>,<96,56>,<96,57>,<96,58>,<96,63>,
  <96,65>,<96,67>,<96,114>,<96,125>,<96,126>,<96,127>,<96,148>,<96,149>,
  <96,150>,<96,155>,<96,157>,<96,163>,<96,166>,<96,169>,<96,172>,<96,175>,
  <96,181>,<96,184>,<96,199>,<96,201>,<96,214>,<96,222>,<96,225>,<104,3>,
  <104,11>,<112,1>,<112,8>,<112,14>,<112,17>,<112,26>,<120,1>,<120,2>,
  <120,3>,<120,6>,<120,7>,<120,10>,<120,14>,<120,15>,<120,16>,<120,19>,
  <120,21>,<120,24>,<120,33>,<132,2>,<136,1>,<136,3>,<136,11>,<140,1>,
  <140,2>,<144,1>,<144,9>,<144,17>,<144,18>,<144,22>,<144,27>,<144,28>,
  <144,29>,<144,31>,<144,32>,<144,35>,<144,49>,<144,51>,<144,52>,<144,54>,
  <144,56>,<144,58>,<144,60>,<144,61>,<144,62>,<144,73>,<144,74>,<144,77>,
  <144,78>,<144,82>,<144,83>,<144,90>,<144,98>,<144,99>,<144,103>,<144,108>,
  <144,121>,<144,124>,<144,125>,<144,156>,<144,158>,<144,164>,<144,165>,
  <144,180>,<152,1>,<152,10>,<156,4>,<160,3>,<160,14>,<160,17>,<160,36>,
  <160,42>,<160,43>,<160,45>,<160,51>,<160,53>,<160,55>,<160,56>,<160,57>,
  <160,58>,<160,63>,<160,70>,<160,71>,<160,72>,<160,73>,<160,75>,<160,76>,
  <160,77>,<160,78>,<160,85>,<160,87>,<160,111>,<160,113>,<160,114>,<160,115>,
  <160,116>,<160,119>,<160,137>,<160,139>,<160,140>,<160,163>,<160,164>,
  <160,166>,<160,167>,<160,168>,<160,177>,<160,180>,<160,183>,<160,186>,
  <160,189>,<160,195>,<160,198>,<160,201>,<160,206>,<160,208>,<160,210>,
  <160,221>,<160,222>,<160,230>,<160,233>,<168,1>,<168,3>,<168,4>,<168,5>,
  <168,7>,<168,16>,<168,18>,<168,21>,<168,24>,<168,29>,<168,32>,<168,41>,
  <171,1>,<176,1>,<176,8>,<176,16>,<176,17>,<176,21>,<176,26>,<176,39>,
  <180,1>,<180,2>,<180,13>,<180,14>,<180,15>,<180,16>,<184,1>];


function NilpotentHasCokernel(G)                          // Rasmussen's theorem
  error if not IsNilpotent(G), "G should be nilpotent";
  if IsAbelian(G) or (#G eq 1) or IsPrimePower(#G) then return false; end if;
  S:=SylowSubgroup(G,2);
  qorder:=exists{q: q in PrimeDivisors(#G) | IsOdd(q) and IsEven(Order(GF(q)!2))};
  CS:=CharacterTable(S);
  return exists{c: c in CS | (SchurIndex(c) eq 2) and
    (qorder or (AbsoluteDegree(CharacterField(c)) ne 1))};
end function;
 
 
intrinsic BurnsideCokernel(G::Grp) -> GrpAb,UserProgram,SeqEnum[AlgChtrElt] 
{
  For a finite group G computes the Burnside cokernel C(G), the quotient of the rational representation ring R(G) by the subring generated by permutation representations. Thus C(G)=1 if and only if every rational representation of G is a virtual permutation representation. Returns C(G) (finite abelian group), map R(G)->C(G), and a list of irreducible rational representations with non-trivial class in C(G).
}
  
  require Type(G) in [GrpPC,GrpPerm,GrpMat,GrpAb] and IsFinite(G) : 
    "G must be a finite group of type GrpPC,GrpPerm,GrpMat or GrpAb";

  triv:=AbelianGroup([]);
  
  // cok=1 (Ritter-Segal), abelian, pre-computed small groups
  // Rasmussen for nilpotent groups
  if (#G eq 1) or IsPrimePower(#G) or IsAbelian(G) 
      or ((#G le 191) and not (IdentifyGroup(G) in SmallCokList)) 
      or (IsNilpotent(G) and not NilpotentHasCokernel(G)) then   
        return triv, func<rho|triv.0>, [];                        
  end if;

  R:=RationalCharacters(G);
  ok,C,P:=IsHyperelementary(G);
  
  if ok then                       // G Hyperelementary
    RP:=RationalCharacters(P);     // arxiv: 1405.6616, Thm 1.1
    bas:=[];
    orders:=[];
    for rho in R do
      rhoP:=Restriction(rho,P);
      chiorder:=#C div KernelOrder(Restriction(rho,C));
      dimsigmas:=[Degree(sigma): sigma in RP | InnerProduct(rhoP,sigma) ne 0];
      o:=Z!(EulerPhi(chiorder)*Min(dimsigmas)/Degree(rho));
      if o eq 1 then continue; end if;
      Append(~bas,rho);
      Append(~orders,o);
    end for;
    cok:=AbelianGroup(orders);
    return cok, #cok eq 1 select func<chi|cok.0> else func<chi|cok!Decomposition(bas,chi)>, bas;
  end if;

  B:=[[]: rho in R];               // G not Hyperelementary
  O:=[];                           // C(G) injects into prod_Q C(Q) under Res
  for C in CSGPS(G) do
    if #C eq 1 then continue; end if;
    N:=Normalizer(G,C);
    for p in Set(PrimeDivisors(#N)) diff Set(PrimeDivisors(#C)) do
      P:=SylowSubgroup(N,p);
      Q:=sub<G|C,P>;
      cokQ<[gens]>, qQ:=BurnsideCokernel(Q);
      Append(~O,[Order(g): g in gens]);
      if #cokQ eq 1 then continue; end if;
      for i:=1 to #R do
        rho:=R[i];
        dec:=Eltseq(qQ(Restriction(rho,Q)));
        B[i] cat:= [Rationals()|dec[j]/Order(gens[j]): j in [1..#gens]];
      end for;
    end for;
  end for;
  if IsEmpty(B[1]) then return triv, func<rho|triv.0>; end if;  
  M:=Matrix(B);

  L:=Lattice(M);
  B:=[Eltseq(r): r in Rows(Transpose(M))];
  Q,m:=quo<L|L meet StandardLattice(Degree(L))>;

  return Q, func<rho|m(L![InnerProductList(dec,b): b in B]) 
    where dec is Decomposition(R,rho)>, B;
end intrinsic;


intrinsic IsPermutationCharacter(c::AlgChtrElt) -> BoolElt
{
  Check whether a character c of a finite group G is a virtual permutation character, that is C[X]-C[Y] for some G-sets X and Y.
}
 
  require (Type(c) eq AlgChtrElt): "c must be a character of a finite group";
  G:=Group(Parent(c));
  require IsFinite(G): "c must be a character of a finite group";
    
  if c eq 0 then return true; end if;

  // Not rational-valued
  if AbsoluteDegree(CharacterField(c)) ne 1 then return false; end if;

  // Order 2
  if Degree(c) eq 1 then return true; end if;

  // Schur index
  if not forall{b: b in Basis(Parent(c)) | 
    (i eq 0) or IsCoercible(Integers(),i/SchurIndex(b)) where i is InnerProduct(b,c)} 
    then return false; end if;

  // cok=1 (Ritter-Segal), abelian, pre-computed small groups
  // Rasmussen for nilpotent groups
  if (#G eq 1) or IsPrimePower(#G) or IsAbelian(G) 
      or ((#G le 191) and not (IdentifyGroup(G) in SmallCokList)) 
      or (IsNilpotent(G) and not NilpotentHasCokernel(G)) then   
        return true;
  end if;

  ok,C,P:=IsHyperelementary(G);
  
  if ok then                       // G Hyperelementary
    RP:=RationalCharacters(P);     // arxiv: 1405.6616, Thm 1.1
    bas:=[];
    orders:=[];
    rhoP:=Restriction(c,P);
    chiorder:=#C div KernelOrder(Restriction(c,C));
    dimsigmas:=[Degree(sigma): sigma in RP | InnerProduct(rhoP,sigma) ne 0];
    o:=Z!(EulerPhi(chiorder)*Min(dimsigmas)/Degree(c));
    return o eq 1;
  end if;

  for C in CSGPS(G) do                  // G not Hyperelementary
    if #C eq 1 then continue; end if;   // C(G) injects into prod_Q C(Q) under Res
    N:=Normalizer(G,C);
    for p in Set(PrimeDivisors(#N)) diff Set(PrimeDivisors(#C)) do
      P:=SylowSubgroup(N,p);
      Q:=sub<G|C,P>;
      cokQ<[gens]>, qQ:=BurnsideCokernel(Q);
      if Order(qQ(Restriction(c,Q))) ne 1 then return false; end if;
    end for;  
  end for;  
  return true;
end intrinsic;


function IsSymmetricGroup(G)
  ok,n:=IsFactorial(#G);
  if not ok then return false; end if;
  if (Type(G) eq GrpPerm) and (#GSet(G) eq n) then return true; end if;
  if n le 5 then 
    return IdentifyGroup(G) in [<1,1>,<2,1>,<6,1>,<24,12>,<120,34>];
  end if;
  if Type(G) eq GrpPC then return false; end if;
  return exists{M: M in MaximalSubgroups(G: IndexEqual:=n) | 
    #Core(G,M`subgroup) eq 1};
end function;


intrinsic IsQGroup(G::Grp) -> BoolElt
{
  Check whether a finite group G is a Q-group (all characters are rational-valued)
}

  require Type(G) in [GrpPC,GrpPerm,GrpMat,GrpAb] and IsFinite(G) : 
    "G must be a finite group of type GrpPC,GrpPerm,GrpMat or GrpAb";

  // Abelian Q-groups are C2^n 
  if IsAbelian(G) then 
    return Exponent(G) le 2; 
  end if;

  // For large groups do a random check - fast and efficient
  for step:=1 to Round(Log(#G)) do
    g:=Random(G);
    n:=Order(g);
    if n eq 1 then continue; end if;
    repeat i:=Random(1,n); until GCD(i,n) eq 1;
    if not IsConjugate(G,g,g^i) then return false; end if;
  end for;

  // If G/G' is not C2^n, then not a Q-group
  GD:=CommutatorSubgroup(G);
  if (not IsPowerOf(Index(G,GD),2)) or (Exponent(quo<G|GD>) gt 2) 
    then return false; end if;

  // Sym(n) is a Q-group
  if IsSymmetricGroup(G) then return true; end if;

  //! Some day put in ChiefFactors that are possible here

  // Compute conjugacy classes and check them all
  CC:=ConjugacyClasses(G);
  for i:=1 to #CC do 
    order,size,g:=Explode(CC[i]);
    if not forall(j){j: j in PrimitiveRootsN(order) | IsConjugate(G,g,g^j)} then 
      return false;
    end if;
  end for;
  return true;  
end intrinsic;  
