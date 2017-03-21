freeze;

/**********************************************************
  Epsilon factors for Artin and local Galois representations 
  
  intrinsic EpsilonFactor(A:: GalRep) -> FldComElt   // local
  intrinsic RootNumber(A:: GalRep) -> FldComElt
  intrinsic EpsilonFactor(A:: ArtRep, p:: RngIntElt) -> FldComElt
  intrinsic RootNumber(A:: ArtRep, p:: RngIntElt) -> FldComElt
  intrinsic EpsilonFactor(A:: ArtRep, p:: Infty) -> FldComElt
  intrinsic RootNumber(A:: ArtRep, p:: Infty) -> FldComElt
  
  intrinsic EpsilonFactor(A:: ArtRep) -> FldComElt  // global
  intrinsic RootNumber(A:: ArtRep) -> FldComElt
  
  version 1: Tim Dokchitser, Oct 2014
    elliptic curves based on an earlier code by T+V Dokchitser 
    rest based straight on Tate's "Number theoretic background"
/*********************************************************/


// mmylib functions

Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;

import "../../Ring/RngLoc/splitfield.m": 
  ComputeSplittingField;
import "galrep.m": 
  PrintField,PrintComplex,GalRepCopy,IsNumZero,PrintEulerFactor,X,
  FixedFieldPoly,ChangeCharacter;



function RachelLocRecip(x,F,G)

  // From Rachel's paper on tame local reciprocity
  // Note: opposite convention for local reciprocity to Tate NTB

  K:=Parent(x);
  piF:=UniformizingElement(F);
  OF:=Integers(F);
  e:=RamificationDegree(F,K);

  i:=Valuation(x);
  pi:=UniformizingElement(K);
  k:=ResidueClassField(IntegerRing(K));
  u:=x/pi^i;
  q:=#k;
  kF:=ResidueClassField(IntegerRing(F));

  elts:=[piF,piF*OF!PrimitiveElement(ResidueClassField(OF))];
  rhs:=[kF| beta^(q^i-1) / ((-1)^(e-1)*pi)^(Z!((q^i-1)*vkb)) / u^(Z!((q-1)*vkb))
    where vkb is Valuation(beta)/RamificationDegree(Parent(beta),K)
    : beta in elts];
  for j:=1 to #G do
    sigma:=G[j];
    if [kF| sigma(beta)/beta: beta in elts] eq rhs then return j; end if;
  end for;
  error "Local reciprocity failed";
end function;


NPsi:=func<K|Valuation(Discriminant(Integers(K),PrimeRing(Integers(K))))>;


function EpsilonFactorTame(A)
  chi:=Character(A);

  Q:=Rationals();
  pi:=Pi(RealField());
  CF<I>:=ComplexField();
  exp:=func<x|Exp(2*pi*I*x)>;

  //assert IsCyclic(A`G);
  K0:=BaseField(A);
  O0:=Integers(K0);
  deg:=Degree(Field(A),K0);
  piKf:=UniformizingElement(K0);
  npsi:=NPsi(K0);
  shft2:=piKf^(-npsi-1);
  Qp:=PrimeField(K0);

  k,redk:=ResidueClassField(O0);             // Residue field

  frac:=func<x|x-Floor(x)>;
  Tr:=func<x|Trace(x*shft2,Qp)>;
  TrFrac:=func<x|frac(Q!Tr(O0!x))>;

  z:=exp(1/deg);
  u:=O0!PrimitiveElement(k);                  // generator of the residue field
  u:=K0!HenselLift(PR(O0).1^(#k-1)-1,u);      // Teichmuller lift
  Gelts:=[g: g in A`G];
  gu:=Gelts[RachelLocRecip(u,Field(A),[* A`act(g): g in Gelts *])];
  gs:=Gelts[RachelLocRecip(1/shft2,Field(A),[* A`act(g): g in Gelts *])]^(-1);
  
  epsilon:= CF!chi(gs) * 
    &+[CF!chi(gu^j)*exp(TrFrac(u^j)): j in [1..#k-1]];  //! * norm later
      // the formula actually says chi^-1 (Tate NTB 3.2.6.2) on 
      // gu^-j because Rachel's convention is opposite to Tate's
  
  vprintf GalRep,1: "G=%o I=%o Epsilon factor of a tame character %o of order %o for %o/%o = %o\n",
    GroupName(A`G),GroupName(A`I),
    chi,Order(chi),PrintField(Field(A)),PrintField(K0),PrintComplex(epsilon);
  
  return epsilon;
  
end function;


function mul(a,b)
  if (Type(a) eq FldCycElt) and (Type(b) in [FldReElt,FldComElt]) then 
    return ComplexField()!a * b;
  elif (Type(b) eq FldCycElt) and (Type(a) in [FldReElt,FldComElt]) then 
    return ComplexField()!b * a;
  else
    return a*b;
  end if;
end function;
    

function EpsilonFactorGeneral(A)
  if assigned A`epsilon then return A`epsilon; end if;

  if #A`co ne 1 then                     // Direct summmand -> decompose
    vprint GalRep,1: "Epsilon: Decomposition";
    eps:=1;
    for d in A`co do
      B:=GalRepCopy(A, [* d *]);
      e:=EpsilonFactorGeneral(B);
      if e eq 0 then return 0; end if;
      eps*:=e;
    end for;
    return eps;
  end if;
 
  DetFrob:=func<A|(-1)^Degree(f)*1/LeadingCoefficient(f) where f is EulerFactor(A)>;  
  DetMinusFrob:=func<A|1/LeadingCoefficient(EulerFactor(A))>;   
         //! Correct?
  
  if not IsSemisimple(A) then            // Not semisimple -> Tate NTB 4.2.4
    vprint GalRep,1: "Epsilon: Semisimplification";
    Ass:=Semisimplification(A);
    return EpsilonFactorGeneral(Ass) 
      * DetMinusFrob(InertiaInvariants(Ass))
      / DetMinusFrob(InertiaInvariants(A));   
  end if;

  // From now on we have one term <psi,1,chi>
  
  psi,n,chi:=Explode(A`co[1]);
  assert n eq 1;

  // Unramified twist formula Tate NTB 3.4.6 
  
  if (Degree(psi) ne 1) or not IsNumZero(Coefficient(psi,1)+1: precfactor:=1.3) then
    vprint GalRep,1: "Epsilon: Unramified twist",PrintEulerFactor(psi);
    B:=A!!chi;
    detfrob:=(-1)^Degree(psi)*1/LeadingCoefficient(psi);
    vprint GalRep,1: "Epsilon: Det(Frob) =",PrintComplex(detfrob);
    return mul(EpsilonFactorGeneral(B)^Degree(psi),
      detfrob^-(ConductorExponent(B)+Degree(B)*NPsi(BaseField(A))));  
        //! check sign detfrob^(-1)?
  end if;

  // Unramified 
  
  if IsUnramified(A) then 
    return chi(A`Frob^(-1))^NPsi(BaseField(A)); 
  end if;
     
  // Reducible
  
  if not IsIrreducible(chi) then
    vprint GalRep,1: "Epsilon: Irreducibles";
    C:=CharacterTable(Group(A));
    dec:=Decomposition(C,chi);
    eps:=1;
    for i:=1 to #dec do
      if dec[i] eq 0 then continue; end if;
      B:=A!!C[i];
      eps:=mul(eps,EpsilonFactorGeneral(B)^(Z!dec[i]));
      if eps eq 0 then return 0; end if;
    end for;
    return eps;
  end if;
     
  // Degree 1 ramified: Gauss sum Tate NTB 3.2.6.2

  // Tame
  
  if (Degree(chi) eq 1) and IsTamelyRamified(A) then 
    return EpsilonFactorTame(Minimize(A));
  end if;

  // Frohlich-Queyrut for 2-dim orthogonals [DD-Root2 proof of Prop. 4]
  
  if (Degree(chi) eq 2) and (Indicator(chi) eq 1) and IsUnramified(Determinant(A))
  then 
    vprint GalRep,1: "Epsilon: Frohlich-Queyrut /"*PrintField(BaseField(A)); 

    K0:=BaseField(A);
    det:=Determinant(A);       // A dihedral, det = det A cut out quadratic ext
    B:=Minimize(det);
    assert #Group(B) eq 2;
    F1:=Field(B);
    
    C:=BaseChange(A,F1);      // Over which C=Res A = sum of 2 1-dim chars
    F2:=Field(C);
    
    dec:=Decomposition(C);
    assert #dec eq 2;
    phi:=Character(dec[1]);   // so A = Ind phi, phi prim character on Gal(F2/F1)

    xi:=Discriminant(F1,K0);
    xi:=xi/UniformizingElement(K0)^(2*(Valuation(xi) div 2));
    xi:=Sqrt(F1!xi);
    
    U,m:=UnitGroup(Integers(F1));
    ok,XI:=NormEquation(Integers(F2),m,Integers(F1)!xi);
    eps:=ok select 1 else -1;
    
    vprintf GalRep,2: "Solving norm equation %o/%o with xi=%o -> FQ=%o\n",
      PrintField(F2),PrintField(F1),xi,eps;

    return eps/Abs(eps) * A`q^((NPsi(K0)+ConductorExponent(A))/2);  
        
  end if;
  
  // Wild representations: not implemented yet
  
  if not IsTamelyRamified(A) then
    Sprintf("Epsilon: wildly ramified representations (%o G=%o I=%o) are not implemented",
      DelSpaces(chi),GroupName(A`G),GroupName(A`I));
    return 0;          
  end if;
 
  // Monomials + Brauer induction for higher-dimensional representations

  G:=Group(A);  
  o:=#G / Degree(A);
  if IsCoercible(Z,o) then
  for D in Subgroups(G: OrderEqual:=Z!o) do                  // A monomial
    H:=D`subgroup;
    if not exists(c){c: c in LinearCharacters(H) | 
      Induction(c,G) eq chi} then continue; end if;

    f:=FixedFieldPoly(A,H);
    vprint GalRep,2: "Monomial: Subfield cut out by H";
    OH:=ComputeSplittingField(f,0: attempts:=1, Gal:=false);
    vprint GalRep,2: "Monomial: Restriction of A to it";
    AH:=Restriction(A,FieldOfFractions(OH));
    vprint GalRep,2: "Monomial: Linear character";
    chiH:=Character(AH);
    assert exists(c){c: c in LinearCharacters(Group(AH)) | InnerProduct(c,chiH) eq 1};
    eps3:=EpsilonFactor(ChangeCharacter(AH,PrincipalCharacter(AH`G)));
    vprint GalRep,2: "Monomial: eps(1)="*PrintComplex(eps3);
    if eps3 eq 0 then return 0; end if;
    B:=ChangeCharacter(AH,c);            // Ind B = A
    eps1:=EpsilonFactor(B);
    vprint GalRep,2: "Monomial: eps(B)="*PrintComplex(eps1);
    eps2:=EpsilonFactor(ChangeCharacter(A,PermutationCharacter(G,H)));
    vprint GalRep,2: "Monomial: eps(Ind 1)="*PrintComplex(eps2);

    // e(Ind B)/e(Ind 1) = e(B)/e(1) by inductivity in degree 0
    //   => answer/eps2 = eps1/eps3
    return eps2*eps1/eps3;
    
  end for;
  end if;
  
  Sprintf("Epsilon: Brauer induction in this case (%o G=%o I=%o) is not implemented",
    DelSpaces(chi),GroupName(A`G),GroupName(A`I));
  return 0;          
 
end function;


intrinsic EpsilonFactor(A:: GalRep) -> FldComElt
{Epsilon-factor of a Galois representation. Returns 0 if not implemented yet}
  eps:=EpsilonFactorGeneral(A);
  if IsNumZero(eps-Round(Real(eps))) then 
    eps:=Round(Real(eps));                   // Integer
  elif IsNumZero(Imaginary(eps)) then 
    eps:=Real(eps);                          // Real
  elif IsNumZero(Real(eps)) then 
    eps:=Imaginary(eps)*ComplexField().1;    // Purely imaginary
  end if;
  A`epsilon:=eps;
  return eps;    
end intrinsic;


intrinsic RootNumber(A:: GalRep) -> FldComElt
{Root number of a Galois representation. Returns 0 if not implemented yet}
  eps:=EpsilonFactor(A);
  if eps eq 0 then return 0; end if;
  root:=eps/Abs(eps);
  if IsNumZero(root-1: precfactor:=1.3) then return 1; end if;
  if IsNumZero(root+1: precfactor:=1.3) then return -1; end if;
  return root;
end intrinsic;


intrinsic EpsilonFactor(A:: ArtRep) -> FldComElt
{Global epsilon-factor of an Artin representation; its absolute value is 
Sqrt(Conductor(A)) and the complex angle is given by the root number. 
Returns 0 if not implemented yet}
  if Conductor(A) eq 1 then return 1; end if;
  eps:=ComplexField()!RootNumber(HodgeStructure(A));
      //! Complex conjugate because it seems our conventions are somewhere 
      //  opposite to Deligne's for Artin representations 
      //  [by comparing with root numbers at infinity for 1-dim Art reps]
  for p in PrimeDivisors(Conductor(A)) do
    loceps:=EpsilonFactor(GaloisRepresentation(A,p));
    if loceps eq 0 then return 0; end if;
    eps*:=loceps;
  end for;
  return eps;
end intrinsic;


intrinsic RootNumber(A:: ArtRep) -> FldComElt
{Global root number of an Artin representation, the sign in the functional 
equation for LSeries(A). It is computed as a product of local root numbers,
and returns 0 if not implemented yet}
  eps:=EpsilonFactor(A);
  if eps eq 0 then return 0; end if;
  root:=eps/Abs(eps);
  if IsNumZero(root-1: precfactor:=1.3) then return 1; end if;
  if IsNumZero(root+1: precfactor:=1.3) then return -1; end if;
  return root;
end intrinsic;
 

intrinsic EpsilonFactor(A:: ArtRep, p:: RngIntElt) -> FldComElt
{Local epsilon-factor of an Artin representation at a prime p. 
Returns 0 if not implemented yet}
  return EpsilonFactor(GaloisRepresentation(A,p));
end intrinsic;


intrinsic RootNumber(A:: ArtRep, p:: RngIntElt) -> FldComElt
{Local root number of an Artin representation at a prime p. 
Returns 0 if not implemented yet}
  return RootNumber(GaloisRepresentation(A,p));
end intrinsic;


intrinsic RootNumber(A:: ArtRep, p:: Infty) -> FldComElt
{Local root number of an Artin representation at infinity}
 return ComplexField()!RootNumber(HodgeStructure(A));
      //! Complex conjugate because it seems our conventions are somewhere 
      //  opposite to Deligne's for Artin representations 
      //  [by comparing with root numbers at infinity for 1-dim Art reps]
end intrinsic;


intrinsic EpsilonFactor(A:: ArtRep, p:: Infty) -> FldComElt
{Local epsilon-factor of an Artin representation at infinity}
  return RootNumber(A,p);
end intrinsic;


