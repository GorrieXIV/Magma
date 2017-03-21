freeze;

declare verbose Representation, 1;
declare attributes AlgChtr: CharacterFields;

intrinsic IsMonomial(M::Mtrx)->BoolElt
{True iff the square matrix M is monomial}
  n:=Ncols(M);
  return Nrows(M) eq n and &and{#Support(M[i]) eq 1:i in [1..n]};
end intrinsic;

intrinsic IsMonomialRepresentation(rho::Map)->BoolElt
{True iff the representation rho is monomial}
  require ISA(Type(Domain(rho)),Grp): "The domain of the argument must be a grou
p";
  require Type(Codomain(rho)) eq GrpMat: "The codomain of the argument must be a
 matrix group";
  return &and{IsMonomial(rho(g)):g in Generators(Domain(rho))};
end intrinsic;

intrinsic IsRepresentation(rho::Map)->BoolElt
{True iff rho is mapping from a group to a matrix group}
  return ISA(Type(Domain(rho)),Grp) and Type(Codomain(rho)) eq GrpMat;
end intrinsic;

intrinsic IsIrreducible(rho::Map)->BoolElt
{True iff rho is an irreducible representation}
  require IsRepresentation(rho): "Argument must be a group representation";
  return IsIrreducible(Character(rho));
end intrinsic;

intrinsic IsUnitaryRepresentation(rho::Map)->BoolElt
{True iff rho is a unitary representation}
  require IsRepresentation(rho): "Argument must be a group representation";
  dagger:=func<x|Generic(Parent(x))![ComplexConjugate(c):c in Eltseq(Transpose(x
))]>;
  return not exists{g:g in Generators(Domain(rho))|not IsOne(m*dagger(m)) where 
m:=rho(g)};
end intrinsic;

intrinsic RepresentationDegree(rho::Map)->RngIntElt
{The degree of the representation rho}
  require IsRepresentation(rho): "Argument must be a group representation";
  return Degree(Codomain(rho));
end intrinsic;

intrinsic ComplexConjugate(chi::AlgChtrElt)->AlgChtrElt
{The complex conjugate of the character chi}
  return Parent(chi)![ComplexConjugate(chi[i]): i in [1..#chi]];
end intrinsic;

intrinsic TrivialRepresentation(G::Grp)->Map
{The trivial one-dimensional representation of G}
  return hom<G->GL(1,Rationals())|[[1]:i in [1..Ngens(G)]]>;
end intrinsic;

intrinsic CharacterToRepresentation(chi::AlgChtrElt)->Map
{The representation corresponing to the character chi of degree one}
  require Degree(chi) eq 1: "The character is not one-dimensional";
  G:=Group(Parent(chi));
  K:=CoefficientField(chi);
  return hom<G->GL(1,K)|[[chi(G.i)]:i in [1..Ngens(G)]]>;
end intrinsic;

//-----------------------------------------------------------------------------
intrinsic DirectSum(r::Map,s::Map)->Map
{The direct sum of the group representations r and s}
  require IsRepresentation(r): "The first argument must be a group representatio
n";
  require IsRepresentation(s): "The second argument must be a group representati
on";
  require Domain(r) eq Domain(s): "The domains of the representations must be eq
ual";
  G:=Domain(r);
  im:=[DirectSum(r(G.i),s(G.i)):i in [1..Ngens(G)]];
  n:=Degree(Codomain(r))+Degree(Codomain(s));
  K:=CoefficientRing(Universe(im));
  return hom<G->GL(n,K)|im>;
end intrinsic;


//-----------------------------------------------------------------------------
intrinsic Induction(rho::Map,G::Grp)->Map
{Induce the representation rho of a subgroup of G to G} 
  H:=Domain(rho);
  require Type(H) eq Type(G) and H subset G: "The first argument must be a repre
sentation of a subgroup of the second argument";

  IndentPush();
  t:=Cputime();
  T:=Transversal(G,H);
  vprintf Representation: "Transversal computation time: %o s\n",Cputime(t);
  K:=CoefficientRing(Codomain(rho));
  d0:=Degree(Codomain(rho));
  d:=#T*d0;
  im:=[MatrixRing(K,d)!0: i in [1..Ngens(G)]];
  for i:=1 to Ngens(G) do
     t:=Cputime();
     for k,l in [1..#T] do
       x:=T[k]*G.i*T[l]^-1;
       if x in H then
         InsertBlock(~im[i],rho(x),1+(k-1)*d0,1+(l-1)*d0);
       end if;
     end for;
  vprintf Representation: "Generator %o: %o s\n",i,Cputime(t);
  end for;

  IndentPop();

  return hom<G->GL(d,K)|im>;
end intrinsic;


//-----------------------------------------------------------------------------
intrinsic Extension(chi::AlgChtrElt,rho::Map)->Map
{Given a character chi of a group G and a representation rho of a subgroup H of
 G such that the restriction of chi to H equals the character of rho, compute 
 a representation of G using the extension formula of Minkwitz}

 require IsRepresentation(rho): "The second argument must be a group representat
ion";

 G:=Group(Parent(chi));
 H:=Domain(rho);
 require Type(H) eq Type(G) and H subset G: "The second argument must be a chara
cter of a subgroup of group of the first argument";

 chi_H:=Restriction(chi,H);
 chi_rho:=Character(rho);

 require chi_H eq chi_rho: "The restriction of the first argument does not equal
 the character of the second argument";
  
  gl:=Codomain(rho);
  K:=MinimalCyclotomicField({CoefficientRing(gl).1} join {chi[i]:i in [1..#chi]});
  // K:=Compositum(CoefficientRing(gl), CharacterField(chi));
  n:=Degree(gl);
  M:=MatrixRing(K,n);
  im:=[];
  for i:=1 to Ngens(G) do
    t:=Cputime();
    rep:=M!0;
    for h in H do
      c:=chi(G.i*h^-1);
      if c ne 0 then
        rep+:=c*M!rho(h);
      end if;
    end for;
    Append(~im,n/#H*rep);
    vprintf Representation: "Generator %o: %o s\n",i,Cputime(t);
  end for;
  return hom<G->GL(n,K)|im>;

end intrinsic;

intrinsic CharacterOfImage(chi::AlgChtrElt, f::Map, I::Grp) -> AlgChtrElt
{The character of I given by projecting chi onto I. Assumes f is
homomorphism, I is contained in image of f and the kernel of f is contained
in the kernel of chi}

    R := CharacterRing(I);
    cl := Classes(I);
    phi := R![c[3]@@f@chi:c in cl];
    fl, val := HasAttribute(chi, "IsCharacter");
    if fl then AssertAttribute(phi, "IsCharacter", val); end if;
    return phi;
end intrinsic;

intrinsic Indicator(chi::AlgChtrElt) -> FldCycElt
{The Frobenius-Schur indicator of chi}
    return Schur(chi,2);
end intrinsic;

intrinsic CharacterField(chi::AlgChtrElt) -> FldNum
{The character field Q(chi)}

    e := Set(Eltseq(chi));
    CR := Parent(chi);
    C := Universe(e);

    a := assigned CR`CharacterFields;
    if a then
	CFA := CR`CharacterFields;
    else
	CFA := AssociativeArray();
    end if;

//"C:", C; "U:", Universe(CFA);
    if IsDefined(CFA, C) then
	A := CFA[C];
	if IsDefined(A, e) then
//"REUSE!";
	    return A[e];
	end if;
    else
	A := AssociativeArray();
    end if;

    K := sub<C | e>;

    A[e] := K;
    if a then delete CR`CharacterFields; end if; // for mutation
    CFA[C] := A;
    CR`CharacterFields := CFA;

    return K;
end intrinsic;

intrinsic DegreeOfCharacterField(chi::AlgChtrElt) -> RngIntElt
{The degree of the character field Q(chi)}
    /*
    if assigned chi`CharacterField then
	return Degree(chi`CharacterField);
    end if;
    */
    e := Eltseq(chi);
    U := Universe(e);
    d := FixedGroup(U, e);
    return Degree(U) div #d;
end intrinsic;

intrinsic IsRational(chi::AlgChtrElt) -> BoolElt
{Returns true if the character is rational valued, false otherwise}
    return ConductorOfCharacterField(chi) eq 1;
end intrinsic;

intrinsic CyclotomicField(chi::AlgChtrElt) -> FldCyc
{The minimal cyclotomic field containing the values of chi}
    e := Eltseq(chi);
    K := Universe(e);
    return K;
end intrinsic;

intrinsic ConductorOfCharacterField(chi::AlgChtrElt) -> RngIntElt
{The conductor of the character field Q(chi)}
    e := Eltseq(chi);
    K := Universe(e);
    return Conductor(K);

    /* this works...
       A Character is always returned over the minimal cyclotomic field
       containing the elements, so this should also be the smallest
       cyclotomic field containing the character field, thus they have 
       the same comductor.
    */     

    ZZ := MaximalOrder(Polynomial([-1,1]));
    A, mA := RayClassGroup(Conductor(K)*ZZ, [1]);
    //A is (should be) the automorphism group of K
    assert #A eq Degree(K);
    assert Type(K) eq FldCyc;
    // now we need the subgroup fixing the character:
    G, _, mG := AutomorphismGroup(K);
    U := FixedGroup(K, e);
    assert U subset G;
    gen := Generators(K);
    function A_to_G(a)
      i := mA(a);
      i := Generators(i)[1];
      i := Integers()!i;
      i := Abs(i);
      f := exists(g){g : g in G | forall{x :x in gen | Conjugate(x, i) eq (g@mG)(x)}};
      assert f;
      return g;
    end function;

    Ap, mAp := PermutationGroup(A);
    hA_G := hom<Ap -> G | [A_to_G(Ap.i@mAp) : i in [1..Ngens(Ap)]]>;
    assert #Kernel(hA_G) eq 1;
    assert Image(hA_G) eq G;
    q, mq := quo<A|U@@hA_G@mAp>;
    //Magma still has problems with the large number of different trivial groups
    //example:
    //G := PSL(2, 13);
    //C := CharacterTable(G);
    //[ConductorOfCharacterField(c) : c in C];
    //will crash without the special handling of #q eq 1
    return #q eq 1 select 1 else 
      Integers()!Generators(Conductor(AbelianExtension(Inverse(mq)*mA)))[1];
end intrinsic;

intrinsic Conjugate(x::AlgChtrElt, c::RngIntElt) -> AlgChtrElt
{The c-th conjugate of character x}
    R := Parent(x);
    return R![Conjugate(a,c):a in Eltseq(x)];
end intrinsic;


