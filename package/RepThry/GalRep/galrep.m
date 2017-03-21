freeze;

/*******************************************************************

  Local Galois representations 
  
  implements GalRep type and all related functionality
  
  version 1: Tim Dokchitser, Nov 2014

/*******************************************************************/

declare verbose GalRep,3;     // Verbose printing


declare type GalRep;
declare attributes GalRep: 
  K,             // Base field (p-adic)
  P,             // if it arises as a completion of some global field at P
  p,q,           // characteristic of the residue field of K, and its size
  co,            // [* <psi1,n1,char1>,<psi2,n2,char2>,...*] 
                 // with psi's in C[x] Frob char polys of unramified reps, 
                 // n's represent SP(n), and chars are finite characters of G
  F,f,r,G,I,ramgps,Frob,act,dimcomputed,     // main invariants
  conductor,eulerfactor,inertia,epsilon;     // stored to avoid recomputation
                                             // must not be copied by GalRepCopy


import "../ArtRep/artin.m":
  DeterminantCharacter,LocalData,LocalRepresentation;
import "../../Group/GrpFin/rational.m": 
  CSGPS;
import "../../Ring/RngLoc/splitfield.m":
  ComputeSplittingField,GaloisToPermutation,pAdicChangePrecision,MySquarefreePart;
import "../../Geometry/CrvHyp/hyplser.m":
  LocalDataGeneral;


// mmylib functions

Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
PSR:=PowerSeriesRing;
Left:=func<s,n|S[[1..Min(#S,n)]] where S is Sprint(s)>;
Count:=func<S,x|#[z: z in S | z eq x]>;   // count occurences of x in a list
DelCRs:=func<s|&cat([x: x in Eltseq(Sprint(s)) | x ne "\n"])>; // delete \n's
DelSpaces:=
func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;
RightCosetRepresentatives:=func<G,H|DoubleCosetRepresentatives(G,H,sub<G|>)>;
R:=PR(Q); x:=R.1;
RC:=func<|PR(ComplexField())>;

function Last(v)
  try return v[#v]; catch e; end try;
  try w:=Eltseq(v); return w[#w]; catch e; end try;
  error "Last: unrecognized type";
end function;

function ReplaceStringFunc(s,fs,ts)
  if Type(fs) eq SeqEnum then
    for i:=1 to #fs do
      s:=ReplaceStringFunc(s,fs[i],ts[i]);
    end for;
    return s;
  end if;
  s:=CodeToString(255) cat Sprint(s) cat CodeToString(255);
  while Position(s,fs) ne 0 do
    p:=Position(s,fs);
    p:=[p-1,#fs,#s-p-#fs+1];
    s1,s2,s3:=Explode(Partition(Eltseq(s),p));
    s:=&cat(s1) cat ts cat &cat(s3);
  end while;
  return s[[2..#s-1]];
end function;

procedure Swap(~A,i,j)
  t:=A[i]; A[i]:=A[j]; A[j]:=t;
end procedure;

procedure ReplaceString(~s,fs,ts)
  s:=ReplaceStringFunc(s,fs,ts);
end procedure;

CharacterCharPoly:=func<c,g|
  CharacteristicPolynomialFromTraces([c(g^i): i in [1..c[1]]])
>;


/////////////////////////////////////////////////////////////
//    Printing                                             //
/////////////////////////////////////////////////////////////


function IsNumZero(c: precfactor:=2)
  if Type(c) eq FldCycElt then c:=ComplexField()!c; end if;
  B:=Parent(c);
  if Type(B) in [RngInt,FldRat] then return c eq 0; end if;
  return Abs(c) lt 10^-(Precision(B)/precfactor);
end function;  


function IsNumRational(c,den)
  r:=BestApproximation(c,den);
  return IsNumZero(c-r: precfactor:=1.3),r;
end function;  


function IsZPoly(f)
  C:=ComplexField();
  if forall{c: c in Coefficients(f) | IsCoercible(C,c) and 
    IsNumZero(C!c-Round(Real(C!c)))} then   
      f:=PR(Q)![Round(Real(C!c)): c in Coefficients(f)];
      return true,f;
  else
      return false,_;
  end if;
end function;


function IsQPoly(f)
  C:=ComplexField();
  if forall{c: c in Coefficients(f) | IsCoercible(C,c) and 
    IsNumZero(C!c-BestApproximation(Real(C!c),1000): precfactor:=1.5)} then   
      f:=PR(Q)![BestApproximation(Real(C!c),1000): c in Coefficients(f)];
      return true,f;
  else
      return false,_;
  end if;
end function;


function PrintPolynomial(cfs: Reverse:=false, Var:="x")
  s:="";
  for step:=0 to #cfs-1 do
    i:=Reverse select step else #cfs-1-step;
    c:=Sprint(cfs[i+1]);
    
    if c eq "0" then continue; end if;
    c:=("+" in E) or ("-" in E) select "("*c*")" else c where E is Eltseq(c)[[2..#c]];

    if i eq 0 then ;
      elif i eq 1 then c cat:="*"*Var;
      else c cat:= Sprintf("*%o^%o",Var,i);
    end if;
    if Left(c,2) eq "1*" then c:=c[[3..#c]]; end if;
    if Left(c,3) eq "-1*" then c:="-"*c[[4..#c]]; end if;
    if (c[[1]] in ["-","+"]) and (#s ne 0) and (s[[#s]] eq "+") then
      s:=Left(s,#s-1);
    end if;
    s cat:= c cat "+";
  end for;
  s:=Left(s,#s-1);
  if #s eq 0 then s:="0"; end if;
  return s;
end function;  


function PrintComplex(c)
  C:=ComplexField();
  pi:=Pi(C);
  c:=C!c;

  if IsNumZero(c-Round(Real(c))) then      // Integer
    return Sprint(Round(Real(c))); 
  end if;

  if IsNumZero(Abs(c)-1) and IsNumRational(Arg(c)/pi,10^4) then   // Root of 1
    ok,c:=IsNumRational(Arg(c)/2/pi,10^4);
    if c eq 1/4 then return "I"; end if;
    if c eq -1/4 then return "-I"; end if;
    return Sprintf("zeta_%o%o",Denominator(c),
      Numerator(c) eq 1 select "" else "^"*Sprint(Numerator(c)));
  end if;

  if not IsNumZero(Imaginary(c)) then      // Reduce to reals
    re:=PrintComplex(Real(c)); 
    im:=PrintComplex(Imaginary(c));
    return PrintPolynomial([re,im]: Var:="i", Reverse:=true);
  end if;
  c:=Real(c);  

  ok,cQ:=IsNumRational(c,10^8);            // Rational
  if ok then return Sprint(cQ); end if;

  lin:=IntegerRelation([C|1,c,c^2]);
  if Max([Abs(c): c in lin]) le 10^3 then  // Quadratic irrational 
    D:=Squarefree(lin[2]^2-4*lin[1]*lin[3]);
    assert D ne 1;
    F<S>:=QuadraticField(D);
    R:=[d[1]: d in Roots(Polynomial(lin),F)];
    assert exists(sigma){sigma: sigma in InfinitePlaces(F) | Evaluate(S,sigma) gt 0};
    assert exists(r){r: r in R | Abs(Evaluate(r,sigma)-c) lt 10^-8};
    return ReplaceStringFunc(r,"S","sqrt("*Sprint(D)*")");
  end if;
  return Sprint(c);
end function;


function PrintEulerFactor(f,d)
  R:=BaseRing(f);
  C:=ComplexField();
  cfs:=[PrintComplex(Coefficient(f,i)): i in [0..Min(Degree(f),d)]];
  return PrintPolynomial(cfs: Reverse:=true, Var:="x")*
    (d eq Infinity() select "" else (d eq 0 select "+O(x)" 
    else Sprintf("+O(x^%o)",d+1)));
end function;


function PrintField(F)
  if AbsoluteDegree(F) eq 1 then
    return Sprintf("Q%o[%o]",Characteristic(ResidueClassField(Integers(F))),Precision(F)); 
  end if;
  B:=BaseField(F);
  if RamificationDegree(F,B) eq 1 then 
    return Sprintf("ext<%o|%o>",PrintField(B),Degree(F,B));
  end if;
  R:=PR(Integers(B)); _<x>:=PR(Integers(B),1); // Mark's hack
  return Sprintf("ext<%o|%o>",PrintField(B),
		 DelSpaces(Evaluate(R!DefiningPolynomial(F),x)));
end function;


function RLog(q,c) 
  prec:=Precision(RealField());
  C:=ComplexField(prec);
  if (c eq 0) or not IsCoercible(C,c) or not IsNumZero(Imaginary(C!c)) 
    or Real(C!c) lt 10^-(2/3*prec) then return false,_; end if;
  c:=Log(q,RealField()!c);
  if Abs(c-BestApproximation(c,10^(prec div 5))) lt 10^-(2/3*prec)
    then return true,BestApproximation(c,10^(prec div 5));
    else return false,_;
  end if;
end function;


intrinsic Print(A::GalRep, level::MonStgElt)
{Print a Galois representation.}
  field:=Sprintf(" over %o",PrintField(A`K));
  C:=ComplexField();
  I:=A`I;
  triv:=PrincipalCharacter(A`G);
  full:=A`dimcomputed eq Infinity();
  R<X>:=PR(C);
 
  if level ne "Minimal" then     // "Galois representation" header
    if IsZero(A) then
      printf "Galois representation ";
    else 
      printf "%o-dim%o Galois representation ",Degree(A),
        IsOne(A) select " trivial" else (IsRamified(A) select "" else " unramified");
    end if;
  end if;
    
  if IsZero(A) then 
    printf "0";
  end if;
  sps:=[];                               // components
  for i:=1 to #A`co do
    d:=A`co[i];
    f,n,char:=Explode(d);
    if char eq 0 then continue; end if;
    ok,r:=RLog(1/A`q,(-1)^Degree(f)*LeadingCoefficient(f));
    if full and (f eq 1-Parent(f).1) then 
      s:=Sprintf("SP(%o)",n);
    else
      fpr:=full and (Degree(f) eq 1)
        select PrintComplex(-LeadingCoefficient(f))
        else   PrintEulerFactor(f, A`dimcomputed);
      if n eq 1 then
        s:=Sprintf("Unr(%o)",fpr);
      else
        s:=Sprintf("Unr(%o)*SP(%o)",fpr,n);
      end if;
    end if;
    if Left(s,4) eq "w^0*" then s:=s[[5..#s]]; end if;
    if s eq "SP(1)" then s:=""; end if;
    if char ne triv then
      if s ne "" then s cat:= "*"; end if;
      s cat:= DelSpaces(char);    
    end if;
    
    printf (s eq "") select "1" else s;
    if i ne #(A`co) then printf " + "; end if;
  end for;
                                                          // G, I, conductor

  if level eq "Maximal" or 
     level ne "Minimal" and exists{c: c in A`co | c[3] ne triv} then
    if ConductorExponent(A) eq 0 then                      
      printf Sprintf(" with G=%o, I=%o",
        GroupName(A`G),GroupName(A`I));
    else
      printf Sprintf(" with G=%o, I=%o, conductor %o^%o",
        GroupName(A`G),GroupName(A`I),
        AbsoluteRamificationDegree(A`K) eq 1 select A`p else "pi",
        ConductorExponent(A));
    end if;
  end if;

  if level ne "Minimal" then
    printf field;
  end if;

end intrinsic;


///////////////////////////////////////////////////////////////////
// Handling polynomials over Q, cyclotomic fields, number fields, C
///////////////////////////////////////////////////////////////////


function poly(f: R:=0, cut:=Infinity(), dim:=Infinity())   //! TODO: Use R
  if Type(f) eq SeqEnum then f:=Polynomial(f); end if;
  if Type(f) ne RngUPolElt then f:=Polynomial([f]); end if;

  if dim eq Infinity() then dim:=Degree(f); end if;
  if cut lt dim then
    f:=Polynomial([Coefficient(f,i): i in [0..cut]]);
    f+:=666*Parent(f).1^dim;
  end if;

  if forall{c: c in Coefficients(f) | IsCoercible(Q,c)} 
    then return PR(Q)!ChangeUniverse(Coefficients(f),Q);
  end if;
  ok,g:=IsQPoly(f);
  if ok then return PR(Q)!g; end if;
  return f;   
end function;  


function poly2(f,g)
  if Type(f) eq SeqEnum then f:=Polynomial(f); end if;
  if Type(f) ne RngUPolElt then f:=Polynomial([f]); end if;
  if Type(g) eq SeqEnum then g:=Polynomial(g); end if;
  if Type(g) ne RngUPolElt then g:=Polynomial([g]); end if;
  R1:=BaseRing(f);  
  t1:=Type(R1);
  R2:=BaseRing(g);  
  t2:=Type(R2);
  if (t1 eq FldCom) or (t1 eq FldRe) and (t2 eq FldRat)
    then return [PR(R1)|Coefficients(f),Coefficients(g)]; end if;
  if (t2 eq FldCom) or (t2 eq FldRe) and (t1 eq FldRat)
    then return [PR(R2)|Coefficients(f),Coefficients(g)]; end if;
  if t1 eq FldRe then return [PR(ComplexField(Precision(R1)))|Coefficients(f),Coefficients(g)]; end if;
  if t2 eq FldRe then return [PR(ComplexField(Precision(R2)))|Coefficients(f),Coefficients(g)]; end if;
  if (t1 eq FldCyc) or (t2 eq FldCyc) then
    K:=Parent(Coefficient(f,0)+Coefficient(g,0));
    return [PR(K)|Coefficients(f),Coefficients(g)];
  end if;
  return [f,g];   
end function;  


function EulerTensor(f,g)                                // Mellit convolution
  f,g:=Explode(poly2(f,g));
  df:=Degree(f);
  dg:=Degree(g);
  if (df eq 0) or (dg eq 0) then return PR(R)!1; end if;
  f:=PSR(FieldOfFractions(BaseRing(f)),df*dg+1)!f;
  g:=PSR(FieldOfFractions(BaseRing(g)),df*dg+1)!g;
  assert Coefficient(f,0) eq 1;
  df:=Derivative(Log(f));
  assert Coefficient(g,0) eq 1;
  dg:=Derivative(Log(g));
  tens:=Exp(-Integral(Convolution(df,dg))); 
  return poly(Eltseq(tens));
end function;


/////////////////////////////////////////////////////////////
//    Basic type functions                                 //
/////////////////////////////////////////////////////////////


intrinsic IsCoercible(A::GalRep, y::.) -> BoolElt, .
{Coerce a Galois representation.}
  return false, _;
end intrinsic;


intrinsic 'in'(x::GalRep, y::.) -> BoolElt
{"in" function for an Galois representation.}
  return false;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Creation functions                                   //
/////////////////////////////////////////////////////////////


function NewGalRep(K) 
  if Type(K) eq RngPad then 
    K:=FieldOfFractions(K);
  end if;
  error if Type(K) ne FldPad, "K must be a p-adic field";

  A:=New(GalRep);
  A`K:=K;
  k:=ResidueClassField(Integers(K));
  A`p:=Characteristic(k);
  A`q:=#k;
  A`F:=K;
  A`f:=PR(K).1;
  A`r:=[K|0];
  G:=Sym(1);
  A`G:=G;
  A`I:=G;
  A`ramgps:=[<G,0>];
  A`Frob:=G.0;
  A`act:=func<g|map<K->K|x:->x>>;
  A`co:=[* <1-x,1,PrincipalCharacter(G)> *];
  A`dimcomputed:=Infinity();
  return A;
end function;


function GalRepCopy(A0,co) 
  A:=New(GalRep);
  A`K:=A0`K;
  A`p:=A0`p;
  A`q:=A0`q;
  A`co:=co;
  A`F:=A0`F;
  A`f:=A0`f;
  A`r:=A0`r;
  A`G:=A0`G;
  A`I:=A0`I;
  A`ramgps:=A0`ramgps;
  A`Frob:=A0`Frob;
  A`act:=A0`act;
  A`dimcomputed:=A0`dimcomputed;
  return A;
end function;


intrinsic SP(K::FldPad, n::RngIntElt) -> GalRep
{Galois representation SP(n) over a p-adic field K.}
  requirege n,0;
  A:=NewGalRep(K);
  A`co[1][2]:=n;
  return A;
end intrinsic;


intrinsic ZeroRepresentation(K::FldPad) -> GalRep
{Galois representation 0 over a p-adic field K.}
  A:=NewGalRep(K);
  A`co[1][3]*:=0;
  return A;
end intrinsic;


intrinsic SP(K::FldPad, f::RngUPolElt, n::RngIntElt) -> GalRep
{Unramified twist U*SP(n) over a p-adic field K, with U specified by its Euler factor f.}
  requirege n,0;
  A:=NewGalRep(K);
  A`co:=[* <poly(f),n,PrincipalCharacter(A`G)> *];
  return A;
end intrinsic;


intrinsic UnramifiedRepresentation(K::FldPad, CharPoly::RngUPolElt) -> GalRep
{Unique unramified Galois representation rho over K with Euler factor 
det(1-Frob^-1|rho)=CharPoly.}
  require IsCoercible(ComplexField(),ConstantCoefficient(CharPoly)):
    "CharPoly must be a complex polynomial";
  if Degree(CharPoly) eq 0 then return ZeroRepresentation(K); end if;
  A:=NewGalRep(K);
  A`co[1]:=<poly(CharPoly),1,PrincipalCharacter(A`G)>;
  return A;
end intrinsic;


intrinsic UnramifiedRepresentation(K::FldPad, dim::RngIntElt, dimcomputed::RngIntElt, CharPoly::RngUPolElt) -> GalRep
{Unramified Galois representation rho over K of dimension dim, with Euler factor 
CharPoly computed up to and inclusive degree dimcomputed.}
  requirege dim,0;
  requirege dimcomputed,0;
  require IsCoercible(ComplexField(),ConstantCoefficient(CharPoly)):
    "CharPoly must be a complex polynomial";

  //if dim eq 0 then return ZeroRepresentation(K); end if;
  if dimcomputed ge dim then 
    return UnramifiedRepresentation(K,
      Polynomial([Coefficient(CharPoly,i): i in [0..dim]])); end if;

  A:=NewGalRep(K);
  A`co[1]:=<poly(CharPoly: cut:=dimcomputed, dim:=dim),1,PrincipalCharacter(A`G)>;
  A`dimcomputed:=dimcomputed;
   
  return A;
end intrinsic;


intrinsic UnramifiedCharacter(K::FldPad, c::Any) -> GalRep
{Unique unramified character that sends a Frobenius element to c^(-1), 
as a Galois representation over K. The parameter c must be a non-zero 
complex number.} 
  require (c ne 0) and IsCoercible(ComplexField(),c): 
    "c must be a non-zero complex number";
  A:=NewGalRep(K);
  A`co[1]:=<poly([1,-c]),1,PrincipalCharacter(A`G)>;
  return A;
end intrinsic;


intrinsic PrincipalCharacter(K::FldPad) -> GalRep
{Principal character of the absolute Galois group of K, as a Galois representation.}
  return UnramifiedCharacter(K, 1);
end intrinsic;


intrinsic CyclotomicCharacter(K::FldPad) -> GalRep
{Cyclotomic character over K (trivial on inertia, q on Frobenius).}
  return UnramifiedCharacter(K,1/#ResidueClassField(Integers(K)));
end intrinsic;


intrinsic TateTwist(A::GalRep, n::RngIntElt) -> GalRep
{Tate twist A(n) of a Galois representation.}
  return CyclotomicCharacter(BaseField(A))^n * A;      
end intrinsic;


intrinsic Factorization(A:: GalRep) -> List,GalRep
{Returns the list of tuples <chi_i,n_i,rho_i>, where A is the direct sum over i of
twists by SP(n_i) by unramified representations with characteristic polynomial of 
Frobenius chi_i, and a finite Weil representation given by a character rho_i of Group(A).}
  return A`co; 
end intrinsic;


intrinsic IsSemisimple(A:: GalRep) -> BoolElt
{true if a Galois representation A is semisimple.}
  return forall{d: d in A`co | d[2] eq 1};
end intrinsic;


function SPs(q,n)    // Frob char poly on SP(n)
  return &*[1-q^(-i)*x: i in [0..n-1]];    // Powers of cyclotomic character
end function;


intrinsic Semisimplification(A:: GalRep) -> GalRep
{Semisimplification of a Galois representation A.}
  return IsSemisimple(A) 
    select A
    else   GalRepCopy(A,[* <EulerTensor(d[1],SPs(A`q,d[2])),1,d[3]>: d in A`co *]);
end intrinsic;


function GaloisRepresentationsPoly(f: OnlyOne:=false, squarefree:=true)
  O,O0,r,G,I,ramgps,frob,act,f:=ComputeSplittingField(f,0: Gal:=true, squarefree:=squarefree);
  K:=FieldOfFractions(O0);
  F:=FieldOfFractions(O);
  list:=[];
  for chi in CharacterTable(G) do
    A:=NewGalRep(K);
    A`F:=F;
    A`G:=G;
    A`I:=I;
    A`f:=f;
    A`r:=r;
    A`ramgps:=ramgps;
    A`Frob:=frob;
    A`act:=act;
    A`co:=[* <1-x,1,chi >*];
    if OnlyOne then return A; end if;
    Append(~list,A);
  end for;  
  return list;
end function;


intrinsic GaloisRepresentations(f::RngUPolElt[FldPad]: squarefree:=false) -> SeqEnum[GalRep]
{For a polynomial f over a p-adic field K and splitting field F, returns irreducible representations of Gal(F/K).}
  return GaloisRepresentationsPoly(f: OnlyOne:=false, squarefree:=squarefree);
end intrinsic;


function ChangeCharacter(A,ch)
  return GalRepCopy(A, [* <A`co[1][1],A`co[1][2],ch> *]);
end function;


intrinsic PermutationCharacter(F::FldPad, K::FldPad) -> GalRep
{For a p-adic extension F/K, compute C[Gal(Kbar/K)/Gal(Kbar/F)] as a Galois representation over K of degree [F:K].}

  vprint GalRep,1: "PermChar: F="*PrintField(F)*" K="*PrintField(K);

  if F eq K then return UnramifiedCharacter(K,1); end if;

  // Intermediate fields between K and F, and their degrees
  
  flds:=[F];
  L:=F;
  while BaseField(L) ne K do
    error if AbsoluteDegree(L) le AbsoluteDegree(K),
      "F is not given as an extension of K";
    repeat L:=BaseField(L); until AbsoluteDegree(L) lt AbsoluteDegree(Last(flds));
    Append(~flds,L);
  end while;
  degs:=[Degree(L): L in flds];
  U:=#flds ge 2 select flds[2] else K;
  
  // Primitive element
  
  found:=false;
  for E in CartesianProduct([Integers(d): d in degs]) do
    if E[1] eq 0 then continue; end if;
    x:=&+[flds[i].1^(Z!E[i]): i in [1..#flds]];
    if x in U then continue; end if;
    f:=MinimalPolynomial(x,K);
    if Degree(f) ne Degree(F,K) then continue; end if;
    found:=true;
    break;
  end for;
  
  error if not found,"Could not find a primitive element";
  
  // Permutation character C[G/H]
  
  A:=GaloisRepresentationsPoly(f: OnlyOne:=true);
  H:=Stabilizer(A`G,1);
  return ChangeCharacter(A,PermutationCharacter(A`G,H));

end intrinsic;


intrinsic GaloisRepresentations(F::FldPad, K::FldPad) -> SeqEnum[GalRep]
{For a p-adic extension F/K, compute all irreducible Galois representations
 that factor through the (Galois closure of) F/K.}
  A:=PermutationCharacter(F,K);
  return [ChangeCharacter(A,c): c in CharacterTable(A`G)];
end intrinsic;


/////////////////////////////////////////////////////////////
//    Basic invariants                                     //
/////////////////////////////////////////////////////////////


intrinsic Precision(A:: GalRep) -> RngIntElt
{Precision of the base field of a Galois representation.}
  return Precision(A`K);
end intrinsic;


intrinsic Group(A:: GalRep) -> GrpPerm
{Finite Galois group Gal(F/K) that computes the finite part
 of a Galois representation; F=Field(A), K=BaseField(A).}
  return A`G;
end intrinsic;


intrinsic GaloisGroup(A:: GalRep) -> GrpPerm
{"} //"
  return A`G;
end intrinsic;


intrinsic BaseField(A::GalRep) -> FldPad
{Base field of the Galois representation.}
  return A`K;
end intrinsic;


intrinsic Field(A::GalRep) -> FldPad
{p-adic field F such that the finite part of A factors through Gal(F/K).}
  return A`F;
end intrinsic;


intrinsic Automorphism(A::GalRep, g::GrpPermElt) -> Map
{The automorphism of Field(A)/BaseField(A) given by g.}
  ok,g:=IsCoercible(A`G,g);
  error if not ok, "g is not an element of Group(A)";
  return A`act(g);
end intrinsic;


intrinsic FrobeniusElement(A::GalRep) -> GrpPermElt
{Frobenius element of Group(A) for a Galois representation A.}
  return A`Frob;
end intrinsic;


vKernel:=func<ch|ch eq 0 select Group(Parent(ch)) else Kernel(ch)>;


intrinsic InertiaGroup(A:: GalRep) -> GrpPerm, Map
{Inertia subgroup of the finite part of a Galois representation.}
  if assigned A`inertia then return A`inertia; end if;
  A`inertia,q:=quo<A`I|&meet([vKernel(d[3]): d in A`co]) meet A`I>;
  return A`inertia,q;
end intrinsic;


intrinsic InertiaGroup(A:: GalRep, n::RngIntElt) -> GrpPerm, Map
{nth (lower) ramification subgroup of the finite part of a Galois representation.}
  requirege n,0;
  R:=[d: d in A`ramgps | d[2] ge n];
  I:=IsEmpty(R) select sub<A`I|> else R[1][1];
  return quo<I|&meet([Kernel(d[3]): d in A`co]) meet I>;
end intrinsic;


intrinsic IsUnramified(A:: GalRep) -> BoolElt
{True if a Galois representation is unramified.}
  return forall{d: d in A`co | d[2] eq 1}    // no Weil-Deligne part 
    and #InertiaGroup(A) eq 1;               // & trivial inertia on finite part
end intrinsic;


intrinsic IsRamified(A:: GalRep) -> BoolElt
{True if a Galois representation is ramified.}
  return not IsUnramified(A);
end intrinsic;


intrinsic IsTamelyRamified(A:: GalRep) -> BoolElt
{True if a Galois representation is tamely ramified.}
  return #InertiaGroup(A,2) eq 1;
end intrinsic;


intrinsic IsWildlyRamified(A:: GalRep) -> BoolElt
{True if a Galois representation is wildly ramified.}
  return not IsTamelyRamified(A);
end intrinsic;


intrinsic ConductorExponent(A::GalRep) -> RngIntElt
{Conductor exponent of a Galois representation.}
  if assigned A`conductor then return A`conductor; end if;

  A`conductor:=0;
  for d in A`co do
    psi,n,ch:=Explode(d);

    // Weil part
    
    first:=true;
    delta:=0;                                   // conductor exponent
    lastindex:=0;
    g0:=#A`I;
    first:=true;

    for I in A`ramgps do
      coinvdim:=Degree(ch)-InnerProduct(Restriction(ch,I[1]),
                PrincipalCharacter(I[1]));
      if first then weiltame:=coinvdim; first:=false; end if;
      if coinvdim eq 0 then break; end if;
      delta +:= coinvdim * (I[2]-lastindex) * #(I[1]) / g0;
      lastindex:=I[2];
    end for;

    weilwild := Z!delta - weiltame;

    // Full conductor
  
    A`conductor +:= Z!((Degree(psi)*n*Degree(ch)-Degree(psi)*(Degree(ch)-weiltame)) 
      + Degree(psi)*n*weilwild);
  end for;  

  return A`conductor;
end intrinsic;


intrinsic Conductor(A::GalRep) -> FldPadElt
{Conductor of a Galois representation.}
  return UniformizingElement(A`K)^ConductorExponent(A);
end intrinsic;


intrinsic DefiningPolynomial(A:: GalRep) -> RngUPolElt
{The polynomial whose roots Group(A) permutes.}
  return A`f;
end intrinsic;


intrinsic Degree(A::GalRep) -> RngIntElt
{Degree (=dimension) of a Galois representation.}
  return &+[Degree(d[1])*d[2]*(Z!Degree(d[3])): d in A`co];
end intrinsic;


intrinsic Dimension(A::GalRep) -> RngIntElt
{Degree (=dimension) of a Galois representation.}
  return Degree(A);
end intrinsic;


intrinsic IsIndecomposable(A::GalRep) -> BoolElt
{True if the Galois representation A is indecomposable}
  return (#A`co eq 1) and (Degree(A`co[1][1]) eq 1) and IsIrreducible(A`co[1][3]);
end intrinsic;


intrinsic IsIrreducible(A::GalRep) -> BoolElt
{True if the Galois representation A is irreducible}
  return (#A`co eq 1) and (A`co[1][2] eq 1) and (Degree(A`co[1][1]) eq 1) 
    and IsIrreducible(A`co[1][3]);
end intrinsic;


intrinsic Character(A:: GalRep) -> AlgChtrElt
{Character of a Galois representation A. To be defined A must have one component.}
  require #A`co eq 1: "A must have one component for its character to be defined";
  return A`co[1][3];
end intrinsic;


intrinsic EulerFactor(A::GalRep: R:="default") -> RngUPolElt
{Euler factor of a Galois representation. The coefficient field 
(rational, complex or cyclotomic field) may be specified with the 
optional parameter R.}

  if assigned A`eulerfactor then return poly(A`eulerfactor: R:=R); end if;

  A`eulerfactor:=PR(Q)!1;
  for d in A`co do
    psi,n,ch:=Explode(d);
    if ch eq 0 then continue; end if;
  
    // Euler factor of the finite part
  
    if Restriction(ch,A`I) eq Degree(ch)*PrincipalCharacter(A`I) then
      f:=CharacterCharPoly(ch,A`Frob^(-1));
    else
      ichars:=[c: c in CharacterTable(A`G) | (InnerProduct(ch,c) ne 0) and
        (InnerProduct(Restriction(c,A`I),PrincipalCharacter(A`I)) ne 0)];
      f:=IsEmpty(ichars) select 1 else
        &*[CharacterCharPoly(c,A`Frob^(-1))^(Z!InnerProduct(ch,c)): c in ichars];
    end if;  

    // tensor with co part, tensor with SP part
    A`eulerfactor:=poly(&*poly2(A`eulerfactor,
      EulerTensor(EulerTensor(f,psi),1-1/A`q^(n-1)*x)
    ));
  end for;
 
  if Degree(A`eulerfactor) gt A`dimcomputed then 
    A`eulerfactor:=[Coefficient(A`eulerfactor,i): i in [0..A`dimcomputed]];
  end if;

  return poly(A`eulerfactor: R:=R);
  
end intrinsic;


function EulerFactorSubfield(A, H)      // variation: Euler factor of A 
                                        // over the subfield cut out by H
  I:=A`I meet H;
  assert exists(Frob){f: f in H | f^-1*A`Frob in A`I};
  q:=A`q ^ (Index(A`G,H) div Index(A`I,I));
  
  eulerfactor:=PR(Q)!1;
  for d in A`co do
    psi,n,ch:=Explode(d);
    if ch eq 0 then continue; end if;
    ch:=Restriction(ch,H);
  
    if Restriction(ch,I) eq Degree(ch)*PrincipalCharacter(I) then
      f:=CharacterCharPoly(ch,Frob^(-1));
    else
      ichars:=[c: c in CharacterTable(H) | (InnerProduct(ch,c) ne 0) and
        (InnerProduct(Restriction(c,I),PrincipalCharacter(I)) ne 0)];
      f:=IsEmpty(ichars) select 1 else
        &*[CharacterCharPoly(c,Frob^(-1))^(Z!InnerProduct(ch,c)): c in ichars];
    end if;  

    eulerfactor:=poly(&*poly2(eulerfactor,
      EulerTensor(EulerTensor(f,psi),1-1/q^(n-1)*x)));
  end for;

  return poly(eulerfactor);
  
end function;


intrinsic InertiaInvariants(A:: GalRep) -> GalRep
{Inertia invariants of a Galois representation A (an unramified Galois representation).}
  if IsUnramified(A) then return A; end if;
  B:=GalRepCopy(A,[* *]);
  for dA in A`co do
    psi,n,chi:=Explode(dA);
    C:=CharacterTable(A`G);
    dec:=Decomposition(C,chi);
    psitwist:=n eq 1 select psi else EulerTensor(psi,1-1/A`q^(n-1)*x);
    dB:=<psitwist,
      1,&+[CharacterRing(A`G) | dec[i]*C[i]: i in [1..#C] | (dec[i] ne 0) and
      Restriction(C[i],A`I) eq PrincipalCharacter(A`I)]>;
    Append(~B`co,dB);
  end for;  
  return B;
end intrinsic;


intrinsic IsZero(A:: GalRep) -> BoolElt
{True if A is the Galois representation 0.}
  return Degree(A) eq 0;
end intrinsic;


intrinsic IsOne(A:: GalRep) -> BoolElt
{True if A is the trivial 1-dimensional Galois representation.}
  if (Degree(A) ne 1) or IsRamified(A) then return false; end if;
  psi,n,c:=Explode(A`co[1]);
  C:=ComplexField();
  frob:=C!c(A`Frob)*-1/C!Coefficient(psi,1);
  return IsNumZero(frob-1);  
end intrinsic;


/////////////////////////////////////////////////////////////
//     Changing fields                                     //
/////////////////////////////////////////////////////////////


procedure CleanSP(~A)
 
  D:=A`dimcomputed;
 
  // Remove 0 characters and deal with 0 representation

  L:=[c: c in A`co | Degree(c[3]) gt 0]; 

  if IsEmpty(L) then 
    A`co:=[* <1-x,1,CharacterRing(A`G)!0> *]; return;
  end if;
   
  // Merge ones with the same twist and n

  i:=0;
  repeat
    i+:=1;
    I:=[j: j in [i+1..#L] | (L[i][1] eq L[j][1]) and (L[i][2] eq L[j][2])];
    if IsEmpty(I) then continue; end if;
    L[i][3]+:=&+[L[j][3]: j in I];
    L:=L[[j: j in [1..#L] | j notin I]];
  until i ge #L;

  // Merge ones with the same n and character
   
  indices:=SetToSequence(Set([<d[2],d[3]>: d in L]));
  for i:=1 to #indices-1 do
  for j:=1 to #indices-1 do
    if (indices[j+1][1] lt indices[j][1]) or 
       (indices[j+1][1] eq indices[j][1]) and (Degree(indices[j+1][2]) lt Degree(indices[j][2]))
         then Swap(~indices,j,j+1);
    end if;
  end for;
  end for;
  polys:=[* 1: i in indices *];
  for d in L do
    i:=Position(indices,<d[2],d[3]>);
    polys[i]:=poly(&*poly2(polys[i],d[1]): cut:=D);
  end for;

  A`co:=[* <polys[i],indices[i][1],indices[i][2]>: i in [1..#indices] *];
end procedure;


function FixedFieldPoly(A,H)

  vprintf GalRep,1: "FixedFieldPoly A=%o H=%o\n",A,GroupName(H);
 
  G:=Group(A);
  K:=BaseField(A);
  
  if #H eq 1  then return A`f; end if;
  if #H eq #G then return PR(K).1; end if;
  if A`I subset H then 
    return DefiningPolynomial(ext<K|Index(G,H)>); 
  end if;
  
  O0:=Integers(K);
  k0,m0:=ResidueClassField(O0);
  
  F:=Field(A);
  R<X>:=PR(F);
  O:=Integers(F);
  pi:=UniformizingElement(O);
  k,m:=ResidueClassField(O);
  
  Gelts:=[g: g in G];
  
  reps:=RightCosetRepresentatives(G,H);
  for i,j in [1..Degree(k,k0)] do
    z:=O!(k.1^i)*pi+O!(k.1^j)*pi^2;
    u:=&*[A`act(h)(z): h in H];
    a:=[A`act(g)(u): g in reps];
    m:=Max([Valuation(a[1]-a[m]): m in [2..#a]]);
    if m lt 0.7*Precision(F) then break; end if;
    a:="undefined";
  end for;
  
  error if a cmpeq "undefined", "Internal error: could not find a primitive element";
    
  f:=&*[X-r: r in a];
  f:=PR(K)![Trace(c,K)/Degree(Parent(c),K): c in Coefficients(f)];
  return f;
end function;


intrinsic '!!'(A::GalRep, chi::AlgChtrElt) -> GalRep
{Change a Galois representation by a finite representation with character chi, which must be a character of Group(A).}
  ok,chi:=IsCoercible(CharacterRing(Group(A)),chi);
  require ok: "chi must be a character of Group(A)";
  require (chi eq 0) or IsCharacter(chi): "chi may not be virtual";

  return GalRepCopy(A,[* <1-x,1,chi> *]);
end intrinsic;


intrinsic '!!'(A::GalRep, chi::SeqEnum) -> GalRep
{Change a Galois representation by a finite representation with character chi, a character of Group(A) 
represented as a sequence of values.
}
  ok,chi:=IsCoercible(CharacterRing(Group(A)),chi);
  require ok: "chi must be a character of Group(A)";
  require (chi eq 0) or IsCharacter(chi): "chi may not be virtual";
   
  return GalRepCopy(A,[* <1-x,1,chi> *]);
end intrinsic;


function embed1(K1,L,h0)        // Embed a simple extension K1 of K into L
  K:=BaseRing(K1);              // given an embedding h0: K->L
  f:=DefiningPolynomial(K1);    // returns true, H: K1->L if possible
  assert BaseRing(f) eq K;
  
  f:=PR(L)![L!(h0(c)): c in Coefficients(f)];
  r:=Roots(f,L: Max:=1);
  if IsEmpty(r) then return false,_; end if;
  
  r:=r[1][1];
  return true,map<K1->L|x:->Evaluate(Polynomial(L,[h0(c): c in Coefficients(x)]),r)>;
  
end function;


function embed2(K2,L,h0,K)        // Embed a 0- 1- or 2-step extension K2 of K 
  if K2 eq K then                 // into L given an embedding h0: K->L
    H:=h0;                        // returns true, H: K2->L if possible
  elif BaseRing(K2) eq K then
    ok,H:=embed1(K2,L,h0);
    if not ok then return false,_; end if;
  else
    assert BaseRing(BaseRing(K2)) eq K;
    ok,h1:=embed1(BaseRing(K2),L,h0);
    if not ok then return false,_; end if;
    ok,H:=embed1(K2,L,h1);
    if not ok then return false,_; end if;
  end if;
  return true,H;
end function;


function IsGalQuotient(A1,A2)    // Is A2`G a quotient of A1`G?
                                 // if yes, return true,hom:A1`G->A2`G
                                 // Used to lift representations (e.g. Commonify)

  vprint GalRep,3: "IsGalQuotient",A1,A2;

  K:=A1`K;
  assert K eq A2`K;
  
  K1:=A1`F;
  K2:=A2`F;
  if #A1`G mod #A2`G ne 0 then return false,_,_; end if;

  // Is K2 actually embeddable in K1 ?
  K0emb:=hom<A2`K->K1|x:->K1!K!x>;
  ok,H:=embed2(K2,K1,K0emb,K);
  if not ok then return false,_,_; end if;

  vprint GalRep,3: "IsGalQuotient: embedding";

  // Embed the roots of K2
  r:=[H(x): x in A2`r];

  // And recover the action of G1 on them
  _<[gens]>:=A1`G;
  h:=hom<A1`G->A2`G|[GaloisToPermutation(A1`act(g),r): g in gens]>;

  return true,h,H;
  
end function;


function QuotientCharacter(ch,h)
  error if not (Kernel(h) subset Kernel(ch)),
    "The character does not factor through Ker(h)";
  G:=Domain(h);
  Q:=Codomain(h);
  ok,ch:=IsCoercible(CharacterRing(G),ch);
  error if not ok, "ch is not a character of Domain(h)";
  
  return CharacterRing(Q)!&+[InnerProduct(ch,LiftCharacter(c,h,G))*c: c in CharacterTable(Q)];
end function;


intrinsic Minimize(A:: GalRep: To:="default") -> GalRep
{Replace Group(A) by its smallest possible quotient through which all 
components of A factor. If To is specified, instead replace Group(A) by 
Group(To), assuming the A factors through it.}

  vprint GalRep,1: "Minimizing",A;

  require Type(To) in [MonStgElt,GalRep]: 
    "The To parameter must be \"default\" or of type GalRep";

  if IsZero(A) then return ZeroRepresentation(BaseField(A)); end if;
  N:=&meet([Kernel(d[3]): d in A`co]);
  if #N eq 1 then return A; end if;
  if N eq A`G then return UnramifiedCharacter(A`K,1); end if;

  if Type(To) eq GalRep then
    ok,m:=IsGalQuotient(A,To);
    error if not ok, "A does not appear to factor through Group(To)";
    co:=[* <d[1],d[2],QuotientCharacter(d[3],m)>: d in A`co *];
    return GalRepCopy(To,co);
  end if;

  f:=FixedFieldPoly(A,N);
  vprint GalRep,2: "Minimize: Recomputing GalReps";
  B:=GaloisRepresentationsPoly(f: OnlyOne:=true);
 
  vprint GalRep,2: "Minimize: IsGalQuotient?";
  ok,h:=IsGalQuotient(A,B);
  assert ok;

  vprint GalRep,2: "Minimize: Quotient characters";
  B:=GalRepCopy(B,[* <d[1],d[2],QuotientCharacter(d[3],h)>: d in A`co *]);  
  
  assert forall{d: d in B`co | Parent(d[3]) cmpeq CharacterRing(Group(B))};

  vprint GalRep,2: "Minimize: Done";
  return B;
end intrinsic;
Minimise:=Minimize;


function Commonify(A1,A2)      // Lift A1 and A2 to the same group

  vprint GalRep,3: "Commonify",A1,A2;

  d:=Min(A1`dimcomputed,A2`dimcomputed);

  ok,H:=IsGalQuotient(A1,A2);
  if ok then
    B2:=GalRepCopy(A1,[* <d[1],d[2],LiftCharacter(d[3],H,A1`G)>: d in A2`co *]);
    B2`dimcomputed:=d;
    return A1,B2;
  end if;

  ok,H:=IsGalQuotient(A2,A1);
  if ok then
    B1:=GalRepCopy(A2,[* <d[1],d[2],LiftCharacter(d[3],H,A2`G)>: d in A1`co *]);
    B1`dimcomputed:=d;
    return B1,A2;
  end if;

  vprint GalRep,3: "Not a quotient, computing common poly";

  newf:=A1`f*(A2`f div GCD(A1`f,A2`f));
  A:=GaloisRepresentationsPoly(PR(BaseField(A1))!newf: OnlyOne:=true);
  A`dimcomputed:=d;

  ok,H1,emb1:=IsGalQuotient(A,A1); assert ok;
  ok,H2,emb2:=IsGalQuotient(A,A2); assert ok;
  G:=A`G;

  B1:=GalRepCopy(A, [* <d[1],d[2],LiftCharacter(d[3],H1,G)>: d in A1`co *]);
  B2:=GalRepCopy(A, [* <d[1],d[2],LiftCharacter(d[3],H2,G)>: d in A2`co *]);
  
  return B1,B2;
end function;


intrinsic ChangePrecision(~A:: GalRep, Prec:: RngIntElt)
{Change precision of the base field of a Galois representation.}
  if Prec eq Precision(A) then return; end if;
  
  requirege Prec,1;
  
  error if Prec mod AbsoluteRamificationDegree(A`K) ne 0,
    Sprintf("Precision parameter is not a multiple of the absolute ramification degree (%o) of K over Qp",AbsoluteRamificationDegree(A`K));

  oldK0:=A`K;
  oldK:=A`F;
  oldaction:=A`act;

  // new F and K

  F,m:=pAdicChangePrecision(A`F,Prec*RamificationDegree(A`F,A`K));
  K:=F;
  while AbsoluteDegree(K) gt AbsoluteDegree(A`K) do 
    K:=BaseRing(K); 
  end while;

  // new f and r
  
  A`f:=PR(K)![Trace(m(A`F!c),K): c in Coefficients(A`f)] / Degree(F,K);
  A`r:=[HenselLift(PR(F)!(A`f),m(x)): x in A`r];
  A`K:=K;
  A`F:=F;

  // new action

  e:=RamificationDegree(F,K);
  f:=InertiaDegree(F,K);
  oldpi:=UniformizingElement(oldK);
  pi:=UniformizingElement(F);
  oldKU:=BaseField(oldK);               // K - KU - F
  KU:=BaseField(F);              

  KUf:=DefiningPolynomial(KU);
  Kf:=DefiningPolynomial(F);

  function newact(g)
    a:=oldaction(g);
    u:=KU!m(a(oldKU.1));
    u:=HenselLift(PR(KU)!KUf,u);
    ue:=map<KU->KU|x:->Evaluate(Polynomial(KU,[KU!m(c): c in Coefficients(x)]),u)>;
    pi:=m(a(oldK.1));
    pi:=HenselLift(PR(F)![ue(c): c in Coefficients(Kf)],pi);
    pie:=map<F->F|x:->Evaluate(Polynomial(F,[F!ue(c): c in Coefficients(x)]),pi)>;
    return pie;
  end function;
  A`act:=func<g|map<F->F|x:->newact(g)(x)>>;

end intrinsic;


intrinsic ChangePrecision(A:: GalRep, Prec::RngIntElt) -> GalRep
{Change precision of the base field of a Galois representation.}
  if Prec eq Precision(A) then return A; end if;
  B:=GalRepCopy(A,A`co);
  ChangePrecision(~B,Prec);
  return B;
end intrinsic;


procedure CommonifyBase(~A1,~A2)
  error if AbsoluteDegree(A1`K) ne AbsoluteDegree(A2`K) or
    AbsoluteRamificationDegree(A1`K) ne AbsoluteRamificationDegree(A2`K),
      "The two Galois representations are over different fields";  

  vprint GalRep,3: "CommonifyBase",A1,A2;

  p1:=Precision(A1);
  p2:=Precision(A2);
  if p1 gt p2 then ChangePrecision(~A2,p1); end if;
  if p2 gt p1 then ChangePrecision(~A1,p2); end if;
  error if A1`K ne A2`K,
    "The two Galois representations are over different fields";  
    
end procedure;


function RootsToThePower(f,n)  

  if IsCoercible(Z,n) and (Z!n ge 1) then
    n:=Z!n;  
    d:=Degree(f);
    R:=Parent(f); x:=R.1;
    C:=Coefficients(f)[[2..d+1]];
    P:=ElementarySymmetricToPowerSums(C: MaxDeg:=d*n);
    PP:=PowerSumsToPolynomial(P[[n*i: i in [1..d]]]);
    return Evaluate(Reverse(PP),(-1)^n*x);
  end if;

  C:=ComplexField();
  R<X>:=PR(C);
  r:=Roots(R!f);
  return poly(&*[(1-d[1]^(-n)*X)^d[2]: d in r]);
end function;


intrinsic BaseChange(A::GalRep, E::FldPad) -> GalRep
{Base change (restriction) of a Galois representation A over K over a finite extension E/K.}
  K:=A`K;
  FA:=GaloisRepresentationsPoly(PR(E)!A`f: OnlyOne:=true, squarefree:=false);
  ok,H:=embed2(A`F,FA`F,map<K->E|x:->E!x>,K);
  error if not ok, "Failed to embed K->E, F->L";
    
  // Embed the roots of K2
  r:=[H(x): x in A`r];
  
  // And recover the action of G1 on them

  _<[gens]>:=FA`G;
  h:=hom<FA`G->A`G|[GaloisToPermutation(FA`act(g),r): g in gens]>;
  img:=h(FA`G);
  
  // Restrict the character
  f:=InertiaDegree(E,K);
  FA`co:=[* <RootsToThePower(d[1],f),d[2],
    LiftCharacter(Restriction(d[3],img),h,FA`G)> : d in A`co *];

  return FA;
end intrinsic;


intrinsic Restriction(A::GalRep, E::FldPad) -> GalRep
{Restriction (base change) of a Galois representation A over K over a finite extension E/K.}
  return BaseChange(A,E);
end intrinsic;


intrinsic Induction(A::GalRep, K0::FldPad) -> GalRep
{Induction of a Galois representation A over K to K0, a subfield of K.}
  // K0 - A`K - A`F         ->     K0 - I`F  
  //         A`G                     I`G

  I:=PermutationCharacter(A`F,K0);          // Embedding H: Field(I)->Field(H)
  ok,H:=embed2(I`F,A`F,func<x|x>,K0);
  require ok: "Could not embed Field(A) into the the full Galois field";

  // Embed the roots 
  r:=[H(x): x in I`r];
  
  // And recover the action of A`G on them

  _<[gens]>:=A`G;                           // h: Gal(A`F/A`K) -> Gal(I`F/K0)
  h:=hom<A`G->I`G|[GaloisToPermutation(A`act(g),r): g in gens]>;
  assert #Kernel(h) eq 1;
  S<[sgens]>:=h(A`G);
  hinv:=hom<S->A`G|[g@@h: g in sgens]>;     // Inverse hom
  
  // Induce the character
  f:=InertiaDegree(A`K,K0);
  I`co:=[* <RootsToThePower(d[1],1/f),d[2],
    Induction(LiftCharacter(d[3],hinv,S),I`G)> : d in A`co *];

  return I;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Arithmetic                                           //
/////////////////////////////////////////////////////////////


intrinsic '*'(A1::GalRep, A2::GalRep) -> GalRep
{Tensor product of two Galois representations.}
  CommonifyBase(~A1,~A2);

  if IsZero(A1) then return A1; end if;        // one of them 0
  if IsZero(A2) then return A2; end if;

  d:=Min(A1`dimcomputed,A2`dimcomputed);

  if IsUnramified(A1) then                     // one of them unramified
    f:=EulerFactor(A1);
    if Degree(f) lt Dimension(A1) then f+:=Parent(f).1^Dimension(A1); end if;
    A:=GalRepCopy(A2, [* <EulerTensor(d[1],f),d[2],d[3]>: d in A2`co *]);
    A`dimcomputed:=d;
    CleanSP(~A);
    return A;
  end if;
  if IsUnramified(A2) then 
    f:=EulerFactor(A2);
    if Degree(f) lt Dimension(A2) then f+:=Parent(f).1^Dimension(A2); end if;
    A:=GalRepCopy(A1, [* <EulerTensor(d[1],f),d[2],d[3]>: d in A1`co *]);
    A`dimcomputed:=d;
    CleanSP(~A);
    return A;
  end if;
   
  unr1:=#InertiaGroup(A1) eq 1;
  unr2:=#InertiaGroup(A2) eq 1;
  
  if unr1 or unr2 or ((A1`F eq A2`F) and (A1`f eq A2`f) and (A1`G eq A2`G)) then
    // one of them with unramified semisimplification, or both over the same field
    A:=GalRepCopy(unr1 select A2 else A1, [* *]);
    A`dimcomputed:=d;
    q:=A`q;
    for d1 in A1`co do            
    for d2 in A2`co do            
      f1,n1,c1:=Explode(d1);      
      f2,n2,c2:=Explode(d2);      
      f:=EulerTensor(f1,f2);
      i:=0;
      n:=n1+n2-1;               // Clebsch Gordan
      omega:=0;                 // Sp(n1)*Sp(n2) = 
      repeat                    //   Sp(n1+n2-1) + omega*Sp(n1+n2-3) + ...+ omega^... Sp(|n1-n2|+1)
        if unr1 then Append(~A`co,<EulerTensor(f,poly([1,-c1(A1`Frob)*q^(-i)])),n,c2>);
        elif unr2 then Append(~A`co,<EulerTensor(f,poly([1,-c2(A2`Frob)*q^(-i)])),n,c1>);
        else Append(~A`co,<f,n,c1*c2>);
        end if;
        n-:=2;
        i+:=1;
      until n lt Abs(n1-n2)+1;
    end for;
    end for;
    CleanSP(~A);
    return A;
  end if;

  B1,B2:=Commonify(A1,A2);
  return B1*B2;
end intrinsic;


intrinsic '/'(A1::GalRep, A2::GalRep) -> GalRep
{Tensor A1 with A2^(-1), for 1-dimensional A2.}
  require Degree(A2) eq 1: "A1/A2: Representation A2 must be 1-dimensional";
  return A1*(A2^(-1));
end intrinsic;


intrinsic '/'(A1::RngIntElt, A2::GalRep) -> GalRep
{Tensor A1 with A2^(-1), for 1-dimensional A2.}
  require (A1 eq 0) or (A1 eq 1):
    "A1/A2: Only 0/A2 and 1/A2 make sense when A1 is an integer";
  require Degree(A2) eq 1: 
    "A1/A2: Representation A2 must be 1-dimensional";
  if A1 eq 0 then 
    return ZeroRepresentation(BaseField(A2)); 
  else
    return A2^(-1);
  end if;
end intrinsic;


intrinsic '+'(A1::GalRep, A2::GalRep) -> GalRep
{Direct sum of two Galois representations.}
  CommonifyBase(~A1,~A2);
  
  if (A1`F eq A2`F) and (A1`f eq A2`f) and (A1`G eq A2`G) then    // Same F
    A:=GalRepCopy(A1, A1`co cat A2`co);
    A`dimcomputed:=Min(A1`dimcomputed,A2`dimcomputed);
    CleanSP(~A);
    return A;
  end if;
  
  B1,B2:=Commonify(A1,A2);
  return B1+B2;
  
end intrinsic;


intrinsic '^'(A::GalRep, n::Any) -> GalRep
{Tensor power of a Galois representation.}
  
  C:=ComplexField();
  
  require IsCoercible(C,n): "n must be a number";

  n:=IsCoercible(Z,n) select Z!n else C!n;
   
  if (Degree(A) eq 1) then                // Character
    f,_,ch:=Explode(A`co[1]);
    c:=(-Coefficient(f,1)) ^ n;
    return GalRepCopy(A, [* <poly([1,-c]), 1, ch eq PrincipalCharacter(Group(A)) 
      select ch else ch^n> *]);
  end if;

  require (Type(n) eq RngIntElt) and (n ge 0): 
    "Only characters can be raised to a non-natural power";
  if n eq 0 then return UnramifiedCharacter(A`K,1); end if;
  if n eq 1 then return A; end if;
  B:=A;
  for i:=2 to n do
    B:=B*A;
  end for;
  return B;
    
end intrinsic;


intrinsic Decomposition(A::GalRep) -> SeqEnum[GalRep]
{Decompose $A$ into indecomposable (for semisimple representations 
same as irreducible) consituents.}

  error if A`dimcomputed ne Infinity(),
    "Cannot decompose a representation when it is not known to full degree";
  
  C:=CharacterTable(A`G);
  CC:=ComplexField();
  list:=[];
  for d in A`co do
    f,n,ch:=Explode(d);
    dec:=Decomposition(C,ch);
    rts:=Roots(f,CC);
    for i:=1 to #C do
    for j:=1 to Z!(dec[i]) do
    for r in rts do
    for k:=1 to r[2] do
      Append(~list,GalRepCopy(A,[* <poly([1,-1/r[1]]),n,C[i]> *]));
    end for;
    end for;
    end for;
    end for;
  end for;
  return list;
end intrinsic;


intrinsic Determinant(A:: GalRep) -> GalRep
{Determinant of a Galois representation (a 1-dimensional Galois representation).}
  D1:=ComplexField()!1;
  D2:=PrincipalCharacter(A`G);
  for d in A`co do
    psi,n,chi:=Explode(d);
    detpsi:=(-1)^m*Coefficient(psi,m) where m is Degree(psi);
    detSPn:=(A`q)^-((n-1)*n div 2);        
    detchi:=DeterminantCharacter(chi);
    D1*:=detpsi^(n*Degree(chi))*detSPn^(Degree(chi)*Degree(psi));
    D2*:=detchi^(Degree(psi)*n);
  end for;
  return GalRepCopy(A, [* <poly([1,-D1]),1,D2> *]);
end intrinsic;


function equalcomponents(d1,d2,G,I,frob,CC)
  psi1,n1,c1:=Explode(d1);
  psi2,n2,c2:=Explode(d2);
  if (n1 ne n2) or (Restriction(c1,I) ne Restriction(c2,I)) 
    then return false; end if;
  C:=ComplexField();
  for c in CC do 
    assert exists(i){i: i in [0..Order(frob)] | frob^-i*c in I};
    g:=frob^-i*c;  // c = frob^i*g
    f1:=C!c1(c)*-1/C!Coefficient(psi1,1)^i;
    f2:=C!c2(c)*-1/C!Coefficient(psi2,1)^i;
    if not IsNumZero(f1-f2) then return false; end if;
  end for;
  return true;  
end function;


intrinsic '-'(A1::GalRep, A2::GalRep) -> BoolElt
{Assuming A2 is a Galois subrepresentation of A1, compute A1-A2.}
  error if Min(A1`dimcomputed,A2`dimcomputed) ne Infinity(),
    "Cannot compute A1-A2 when they are not known to full degree";
  
  CommonifyBase(~A1,~A2);
  B1,B2:=Commonify(A1,A2);
  D1:=[* C`co[1]: C in Decomposition(B1) *];
  D2:=[* C`co[1]: C in Decomposition(B2) *];
  CC:=[c[3]: c in ConjugacyClasses(B1`G)];
  for i:=#D1 to 1 by -1 do
    for j:=#D2 to 1 by -1 do
      if equalcomponents(D1[i],D2[j],B1`G,B1`I,B1`Frob,CC) then
        Remove(~D1,i);
        Remove(~D2,j);
        break;
      end if;  
    end for;
  end for;
  error if not IsEmpty(D2),
    "Component "*DelSpaces(D2[1])*" of A2 not found in A1";
  S:=GalRepCopy(B1, D1);
  CleanSP(~S);
  return S;
end intrinsic;


intrinsic 'eq'(A1::GalRep, A2::GalRep) -> BoolElt
{True if the two Galois representations are equal.}
  error if Min(A1`dimcomputed,A2`dimcomputed) ne Infinity(),
    "Cannot compare Galois representations when they are not known to full degree";

  //if A1 cmpeq A2 then return true; end if;         //! cmpeq crashes

  CommonifyBase(~A1,~A2);
  B1,B2:=Commonify(A1,A2);
  D1:=[* C`co[1]: C in Decomposition(B1) *];
  D2:=[* C`co[1]: C in Decomposition(B2) *];
  if #D1 ne #D2 then return false; end if;
  CC:=[c[3]: c in ConjugacyClasses(B1`G)];
  for d in D1 do
    found:=false;
    for j:=1 to #D2 do
      if equalcomponents(d,D2[j],B1`G,B1`I,B1`Frob,CC) then
        found:=true;
        Remove(~D2,j);
        break;
      end if;  
    end for;
    if not found then return false; end if;
  end for;
  return true;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Galois representations of elliptic curves            //                                
/////////////////////////////////////////////////////////////


function E3TorsPoly(E)
  F:=BaseRing(E);
  R:=PR(F); x:=R.1;

  loc,E:=LocalInformation(E);
  Fnew,m:=pAdicChangePrecision(F,4*Precision(F));
  E:=EllipticCurve([m(a): a in aInvariants(E)]);

  O:=Integers(Fnew);
  pi:=UniformizingElement(O);

  c4,c6:=Explode(cInvariants(E));
  c4zero:=IsZero(c4) or (Valuation(c4) ge 3/4*Precision(F));

  if c4zero then
    v := Valuation(c6) div 6;
  else
      v:=Min(Valuation(c4) div 4,Valuation(c6) div 6);
      c4:=ChangePrecision((O!c4) div (pi^(4*v)),Precision(O))@@m;
  end if;
  c6:=ChangePrecision((O!c6) div (pi^(6*v)),Precision(O))@@m;

  return c4zero select MySquarefreePart((x^6-8*c6)*(x^2+6*c6))
                else   MySquarefreePart(x^8-6*c4*x^4-8*c6*x^2-3*c4^2);
end function;


function E4TorsPoly(E)
  F:=BaseRing(E);
  R:=PR(F); x:=R.1;
  loc,E:=LocalInformation(E);
  Fnew,m:=pAdicChangePrecision(F,4*Precision(F));
  E:=EllipticCurve([m(a): a in aInvariants(E)]);
  
  c4,c6:=Explode(cInvariants(E));
  D:=Discriminant(E);
  error if Valuation(D) gt (Precision(F) div 2), 
    "Insufficient precision in 4-torsion polynomial";
  C1:=-32*D;
  C2:=4*c4*D;

  O:=Integers(Fnew);
  pi:=UniformizingElement(O);

  v:=Valuation(D) div 4;
  D:=ChangePrecision((O!D) div (pi^(4*v)),Precision(O))@@m;

  v:=Min(Valuation(C1) div 3,Valuation(C2) div 4);
  C1:=ChangePrecision((O!C1) div (pi^(3*v)),Precision(O))@@m;
  C2:=ChangePrecision((O!C2) div (pi^(4*v)),Precision(O))@@m;

  // see 4tors.m
  return MySquarefreePart((x^4-D) * (x^4+C1*x+C2));

  /*
  // see 4tors.m
  return (x^4-D) * (x^4-4*A4*x^3+6*A4^2*x^2+(28*A4^3+216*A6^2)*x+(17*A4^4+108*A6^2*A4));

  return x^12+(10*A4+54*A6)*x^10+(-120*A4^2+40*A6)*x^9+(132*A4^3+15*A4^2-810*A4*A6+891*A6^2)*x^8+
         (96*A4^3+192*A4*A6-2592*A6^2)*x^7+(560*A4^4+432*A4^3*A6-52*A4^3+1260*A4^2*A6+3780*A4*A6^2+2916*A6^3+384*A6^2)*x^6+
         (-576*A4^5-336*A4^4+1344*A4^3*A6-3888*A4^2*A6^2-240*A4^2*A6+9072*A6^3)*x^5+
         (-528*A4^6+280*A4^5-2160*A4^4*A6+15*A4^4-7128*A4^3*A6^2-420*A4^3*A6+1890*A4^2*A6^2-14580*A4*A6^3-240*A4*A6^2-24057*A6^4)*x^4+
         (128*A4^6-160*A4^5+1792*A4^4*A6-2592*A4^3*A6^2-1440*A4^2*A6^2+12096*A4*A6^3-23328*A6^4-320*A6^3)*x^3+
         (-480*A4^7+864*A4^6*A6-208*A4^6+720*A4^5*A6+10*A4^5-6480*A4^4*A6^2-354*A4^4*A6+11664*A4^3*A6^3+132*A4^3*A6^2+4860*A4^2*A6^3+96*A4^2*A6^2-21870*A4*A6^4-2592*A4*A6^3+39366*A6^5+10368*A6^4)*x^2+
         (-384*A4^8-64*A4^7-384*A4^6*A6+8*A4^6-5184*A4^5*A6^2-320*A4^5*A6-432*A4^4*A6^2+8*A4^4*A6-5184*A4^3*A6^3-192*A4^3*A6^2-17496*A4^2*A6^4-2160*A4^2*A6^3+64*A4*A6^3-17496*A6^5-1728*A6^4)*x
         -64*A4^9-16*A4^8-288*A4^7*A6+4*A4^7-1296*A4^6*A6^2-16*A4^6*A6+A4^6-216*A4^5*A6^2+14*A4^5*A6-3888*A4^4*A6^3-37*A4^4*A6^2-8748*A4^3*A6^4-108*A4^3*A6^3+16*A4^3*A6^2-729*A4^2*A6^4+96*A4^2*A6^3-13122*A4*A6^5-432*A4*A6^4-19683*A6^6+64*A6^4;
  */ 
end function;


function ThreeTorsExtType(E)
  K:=BaseField(E);
  K,m:=pAdicChangePrecision(K,Precision(K)*4);
  E:=EllipticCurve([m(a): a in aInvariants(E)]);
  fct:=[Degree(d[1]): d in Factorization(E3TorsPoly(E))];
  c4,c6:=Explode(cInvariants(E));
  if Valuation(c4) ge Precision(K) then c4:=0; end if;
  if Valuation(c6) ge Precision(K) then c6:=0; end if;
  delta:=Discriminant(E);
  mu3:=IsEven(InertiaDegree(K,PrimeField(K)));
  del,rt:=IsPower(delta,3);
  mi:=Min(fct);
  ma:=Max(fct);
  vprintf GalRep,2: "ThreeTorsExtType: fct=%o mu3=%o del=%o\n",
    DelSpaces(fct),mu3,del;
  fct:=Set(fct);
  if mu3 and del then
    if mi lt 8 then return "C" cat Sprint(mi); else return "Q8"; end if;
  end if;
  if mu3 then
    if mi le 2 then return "C" cat Sprint(3*mi); else return "SL(2,3)"; end if;
  end if;
  if del then
    if mi le 2 then return "C2",1; end if;
    if mi eq 4 then return "D4",1; end if;
    if IsSquare(-3*(c4-12*rt)) and IsSquare(-3*(c4^2+12*c4*rt+(12*rt)^2))
      then return "C8",0;
      else return "SD16",2;
    end if;
  end if;
  if (fct eq {1,6}) or (fct eq {2,3}) then return "S3",1; end if;
  if mi eq 2 then return "D6"; else return "GL(2,3)"; end if;
end function;


function EEulerExt(E,F)
  k:=ResidueClassField(IntegerRing(F));
  q:=#k;
  p:=Characteristic(k);
  EK:=BaseChange(E,F);
  red,model:=LocalInformation(EK);
  assert red[3] eq 0;                       // good reduction over F
  ered:=EllipticCurve([k!a: a in aInvariants(model)]);
  return EulerFactor(ered);
end function;


function QuadraticExtensions2Adic(F)
  U<[ug]>,m:=UnitGroup(F);
  U2:=sub<U|[2*g: g in ug]>;
  Q,h:=quo<U|U2>;
  return [m(g@@h): g in Q];
end function;


intrinsic GaloisRepresentation(E::CrvEll[FldPad]: Minimize:=true) -> GalRep
{Local Galois representation of an elliptic curve over a p-adic field.}
  F:=BaseField(E);
  require Type(F) eq FldPad: 
   "E must be defined over a p-adic field; over global fields"*
   " use GaloisRepresentation(E,p)";
  O:=Integers(F);
  pi:=UniformizingElement(O);
  k,m:=ResidueClassField(O);
  p:=Characteristic(k);
  q:=#k;
  C<i>:=ComplexField();
 
  R:=PR(Z); x:=R.1;
  U:=PR(F); X:=U.1;  

  loc,E:=LocalInformation(E);

  _,vdisc,vcond,cv,kod,split:=Explode(loc); kod:=Sprint(kod);
  c4,c6:=Explode(cInvariants(E));
  if vcond eq 0 then                                                    // Good 
    vprint GalRep,2: "GR(E): Good reduction";
    t:=q+1-#EllipticCurve([k|m(a): a in aInvariants(E)]);
    return UnramifiedRepresentation(F,1-t*x+q*x^2);
  elif (vcond eq 1) and split then                                // Split mult
    vprint GalRep,2: "GR(E): Split mult reduction";
    return SP(F,1-q*x,2);
  elif (vcond eq 1) and not split then                        // Non-split mult
    vprint GalRep,2: "GR(E): Non-split mult reduction";
    return UnramifiedCharacter(F,-1)*SP(F,1-q*x,2);
  elif (Valuation(jInvariant(E)) lt 0) then                // Additive pot mult
    vprint GalRep,2: "GR(E): Add pot mult reduction";
    v:=Valuation(c6);
    d:=-c6 / pi^(2*(v div 2));
    f:=X^2-d;
    return GaloisRepresentations(f)[2]*SP(F,1-q*x,2);
  elif (p gt 3) or ((p eq 3) and kod in ["III","I0*","III*"]) or
     ((p eq 2) and kod in ["IV","IV*"]) then          // Additive pot good tame
    vprint GalRep,2: "GR(E): Add pot good tame reduction";
    e:=12 div GCD(12,vdisc);
    if e eq 2 then                                    // Quadratic twist of good
      vprint GalRep,2: "GR(E): Quadratic twist of good reduction";
      f:=X^2-pi;
      return GaloisRepresentations(f)[2]*GaloisRepresentation(QuadraticTwist(E,pi));
    end if;
    GR:=GaloisRepresentations(X^e-pi);
    a:=Last(GR);
    G:=Group(a);
    act:=a`act;
    L:=a`F;
    if not IsAbelian(G) then                          // Dihedral case D_2e
      vprint GalRep,2: "GR(E): Dihedral case",GroupName(G);
      list:=[U: U in GR | (Degree(U) eq 2) and IsFaithful(Character(U)) and
        DeterminantCharacter(Restriction(Character(U),U`I)) 
          eq PrincipalCharacter(U`I)      
      ];
      assert #list eq 1;
      return UnramifiedCharacter(F,(i*Sqrt(C!p))^AbsoluteInertiaDegree(F))*list[1];       
        //! Check - see below
    end if;

    vprint GalRep,2: "GR(E): Cyclic case";
    assert (e in [3,4,6]) and IsCyclic(G);            // Cyclic case C_e
    list:=[U: U in GR | IsFaithful(Character(U))];
    assert #list eq 2;
    K1<piK1>:=ext<F|X^e-pi>;
    f1:=EEulerExt(E,K1);
    r1:=&cat[ [r[1]^(-1): j in [1..r[2]]] : r in Roots(f1,C)];

    u:=PrimitiveElement(k);
    assert Order(u) eq #k-1;
    u:=F!O!u;
    K2:=ext<F|X^e-u*pi>;
    f2:=EEulerExt(E,K2);
    r2:=&cat[ [r[1]^(-1): j in [1..r[2]]] : r in Roots(f2,C)];
    prim:=Exp(2*Pi(C)*C.1/e);
    v:=[r1[1]/r2[1]/prim,r1[1]/r2[2]/prim,r1[1]/r2[1]*prim,r1[1]/r2[2]*prim];
    err,j:=Min([Abs(x-1): x in v]);
    error if not IsNumZero(err), "Wrong Frobenius eigenvalues on E";
    zeta:=j le 2 select prim else prim^(-1);
    if j in [2,4] then Swap(~r2,1,2); end if;

    // Galois acts on E as Phi -> ( r1[1]  0    )   i^(-1) -> ( zeta^(-1) 0 )
    //                            (   0   r1[2] )             (    0   zeta )

    etabar:=u^((#k-1) div e);
    piK1:=Roots(X^e-pi,L: Max:=1)[1,1];
    Gelts:=[g: g in G];
    vals:=[Valuation(act(g)(piK1)/piK1 - etabar): g in Gelts];
    v,m:=Max(vals);
    
    assert v gt 0;
    assert exists(chi){chi: chi in GR | IsNumZero(C!(Character(chi)(Gelts[m]))-zeta)};

    return UnramifiedCharacter(F,r1[1])*chi^(-1) + UnramifiedCharacter(F,r1[2])*chi;
  end if;

  // Wild case 

  vprint GalRep,2: "GR(E): Wild case";

  if (p eq 2) and ThreeTorsExtType(E) in ["SD16","GL(2,3)"] then  // hard case
    vprint GalRep,2: "GR(E): hard case SD16 or GL(2,3) at p=2";
 
    f1:=U!E3TorsPoly(E);

    f2:=X^8+X^4+X^3+X^2+1;     // ext<F|8>
    f:=f1*f2;                  
    
    A:=GaloisRepresentations(f: squarefree:=true);
    G:=A[1]`G;                 // G=SL(2,3):C8 or Q8:C8
    I:=A[1]`I;                 //   SL(2,3)    or Q8
    vprintf GalRep,2: "GR(E): Big extension G=%o I=%o\n",GroupName(G),GroupName(I);
    
    FS:=[H: H in CSGPS(G) | (#H eq 8) and #(H meet I) eq 1 and #Core(G,H) eq 2];
    assert #FS eq 2;
    vprint GalRep,2: "GR(E): Computing FixedFieldPoly";
    g1:=FixedFieldPoly(A[1],FS[1]);
    vprint GalRep,2: "GR(E): Comparing Euler factors";
    FP:=Integers(ChangePrecision(F,4*Precision(F)));
    g1:=PR(FP)![c: c in Eltseq(g1)];  
    _,_,e:=Factorization(g1: Extensions:=true);
    FH:=FieldOfFractions(e[1]`Extension);
    Eeuler:=EEulerExt(E,FH);
    
    tw:=UnramifiedCharacter(F,(i*Sqrt(C!p))^AbsoluteInertiaDegree(F));
    GE:=[tw*c: c in A | (Degree(c) eq 2) and IsFaithful(Restriction(Character(c),I))
      and (#Kernel(Character(c)) eq 4) and not IsOne(Determinant(c))];
    assert #GE eq 2;
    
    GE1euler:=EulerFactorSubfield(GE[1], FS[1]);
    GE2euler:=EulerFactorSubfield(GE[2], FS[1]);
    ok:=[GE1euler eq Eeuler,GE2euler eq Eeuler];
    assert #Set(ok) eq 2;
    GE:=GE[Position(ok,true)];
    
    if Minimize then
      vprint GalRep,2: "Computing 3-torsion poly for minimization";
      A:=GaloisRepresentationsPoly(f1: squarefree:=true, OnlyOne:=true);
      vprint GalRep,2: "Minimizing GR(E)";
      GE:=Minimise(GE: To:=A);
    end if;    
    return GE;

  end if;

                                                       // another hard case
                             
  if (p eq 3) and not IsSquare(q) and (kod in ["II","II*","IV","IV*"]) 
  and IsOdd(vdisc) then
    vprint GalRep,2: "GR(E): hard case C3:C4 at p=3";                 

    f1:=U!E4TorsPoly(E);
    f2:=X^3+2*X+1;                // ext<F|3>
    f:=f1*f2;                  

    A:=GaloisRepresentations(f: squarefree:=true);
    G:=A[1]`G;                 // 
    I:=A[1]`I;                 // 
    vprintf GalRep,2: "GR(E): Big extension G=%o I=%o G/I=%o\n",
      GroupName(G),GroupName(I),GroupName(quo<G|I>);

    FS:=[H: H in CSGPS(G) | (#H eq 6) and #(H meet I) eq 1 and #Core(G,H) eq 1]; 
    assert #FS eq 2;
    vprint GalRep,2: "GR(E): Computing FixedFieldPoly";
    g1:=FixedFieldPoly(A[1],FS[1]);
    vprint GalRep,2: "GR(E): Comparing Euler factors";
    FP:=Integers(ChangePrecision(F,4*Precision(F)));
    g1:=PR(FP)![c: c in Eltseq(g1)];  
    _,_,e:=Factorization(g1: Extensions:=true);
    FH:=FieldOfFractions(e[1]`Extension);
    Eeuler:=EEulerExt(E,FH);

    tw:=UnramifiedCharacter(F,(i*Sqrt(C!p))^AbsoluteInertiaDegree(F));
    GE:=[tw*c: c in A | (Degree(c) eq 2) and IsFaithful(Restriction(Character(c),I))
      and not IsOne(Determinant(c)) and Order(Character(Determinant(c))) eq 2];
    assert #GE eq 2;
    
    GE1euler:=EulerFactorSubfield(GE[1], FS[1]);
    GE2euler:=EulerFactorSubfield(GE[2], FS[1]);
    ok:=[GE1euler eq Eeuler,GE2euler eq Eeuler];
    assert #Set(ok) eq 2;

    GE:=GE[Position(ok,true)];
    
    if Minimize then
      vprint GalRep,2: "Computing 4-torsion poly for minimization";
      A:=GaloisRepresentationsPoly(f1: squarefree:=true, OnlyOne:=true);
      vprint GalRep,2: "Minimizing GR(E)";
      GE:=Minimise(GE: To:=A);
    end if;    
    return GE;
    
  end if;
      
  f:=p eq 3 select E4TorsPoly(E) else E3TorsPoly(E);

  GR:=GaloisRepresentations(f);
  G:=GR[1]`G;
  I:=GR[1]`I;
  
  // Quadratic twist of good
  if #I eq 2 then
    assert exists(t){t: t in QuadraticExtensions2Adic(F) | 
      Valuation(Conductor(QuadraticTwist(E,t))) eq 0};
    return GaloisRepresentations(X^2-t)[2]*GaloisRepresentation(QuadraticTwist(E,t));
  end if;

  if IsAbelian(G) then
    list:=SetToSequence({U+U^(-1): U in GR});
  else
    list:=[U: U in GR | (Degree(U) eq 2) and
      DeterminantCharacter(Restriction(Character(U),U`I)) 
        eq PrincipalCharacter(U`I)];
  end if;
  
  error if IsEmpty(list), 
    Sprintf("Galois representation: reduction is not implemented (G=%o I=%o)",
      GroupName(G),GroupName(I));
  isize:=[#InertiaGroup(U): U in list];
  m,i:=Max(isize);

  error if Count(isize,m) ne 1, 
    Sprintf("Multiple faithful representations of dimension 2 (G=%o I=%o)",
      GroupName(G),GroupName(I));
    
  return UnramifiedCharacter(F,(i*Sqrt(C!p))^AbsoluteInertiaDegree(F))*list[i];       
     //! check for p>2; for p=2 this is Lemma 1 in D.-D. "Root numbers of ECs in res char 2"
     //  determinant is correct though (i sqrt p)^2 * -1 = p on Frob
     //  same above, dihedral case
end intrinsic;


intrinsic GaloisRepresentation(E::CrvEll[FldRat], p::RngIntElt: Precision:=40, Minimize:=true) -> GalRep
{Local Galois representation of an elliptic curve over Q at p.}
  K:=BaseField(E);
  require Type(K) eq FldRat: "E must be defined over the rationals";
  for prec in [d*Precision: d in [1,2,4,10]] do
  try
    F:=pAdicField(p,prec);
    A:=GaloisRepresentation(BaseChange(E,F): Minimize:=Minimize);
    return A;
  catch e
    s:=e`Object;
    vprint GalRep,2: "FAILED: "*s*"; INCREASING PRECISION";
  end try;
  end for;
  error s;
end intrinsic;


intrinsic GaloisRepresentation(E::CrvEll[FldNum], P::RngOrdIdl: Precision:=40, Minimize:=true) -> GalRep
{Local Galois representation of an elliptic curve E over a number field F at a given prime ideal P.}
  K:=BaseField(E);
  for prec in [d*Precision: d in [1,2,4,10]] do
  try
    K1,m:=Completion(K,P: Precision:=prec);
    K2:=ChangePrecision(K1,prec);
    A:=GaloisRepresentation(EllipticCurve([K2|m(a): a in aInvariants(E)]): Minimize:=Minimize);
    return A;
  catch e
    s:=e`Object;
    vprint GalRep,2: "FAILED: "*s*"; INCREASING PRECISION";
  end try;
  end for;
  error s;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Galois representations of hyperelliptic curves       //
/////////////////////////////////////////////////////////////


intrinsic GaloisRepresentation(C::CrvHyp[FldRat], p::RngIntElt: Degree:=Infinity(), Minimize:=false, Precision:=20) -> GalRep
{Galois representation associated to (H^1 of) a hyperelliptic curve C/Q at p.}
  D:=LocalDataGeneral(C,p: degree:=Degree, Precision:=Precision);
  error if not assigned D`A, 
    "Galois representations of hyperelliptic curves with `additive' pieces are not implemented yet";
  A:=D`A;
  return Minimize select Minimise(A) else A;
end intrinsic;


intrinsic GaloisRepresentation(C::CrvHyp[FldPad]: Degree:=Infinity(), Minimize:=false) -> GalRep
{Galois representation associated to (H^1 of) a hyperelliptic curve C over a p-adic field}
  D:=LocalDataGeneral(C,0: degree:=Degree);
  error if not assigned D`A, 
    "Galois representations of hyperelliptic curves with `additive' pieces are not implemented yet";
  A:=D`A;
  return Minimize select Minimise(A) else A;
end intrinsic;


intrinsic GaloisRepresentation(C::CrvHyp[FldNum], P::RngOrdIdl: Degree:=Infinity(), Minimize:=false, Precision:=20) -> GalRep
{Galois representation associated to (H^1 of) a hyperelliptic curve C over a number field at a prime ideal P}
  D:=LocalDataGeneral(C,P: degree:=Degree, Precision:=Precision);
  error if not assigned D`A, 
    "Galois representations of hyperelliptic curves with `additive' pieces are not implemented yet";
  A:=D`A;
  return Minimize select Minimise(A) else A;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Galois representations of Artin representations      //                                 
/////////////////////////////////////////////////////////////


intrinsic GaloisRepresentation(A::ArtRep, p::RngIntElt: Precision:=40, Minimize:=false) -> GalRep
{Local Galois representation at p of the dual of an Artin representation A.}
  require (p ge 2) and IsPrime(p): "p must be a prime number";
  r,G,Frob,ramgps,classmap,Zpprec,act:=LocalData(A`K`artinrepdata`K,p: prec:=Precision);
  F:=FieldOfFractions(Parent(r[1]));
  Qp:=PrimeField(F);
  AG:=NewGalRep(Qp);
  AG`G:=G;
  AG`I:=ramgps[1][1];
  AG`ramgps:=ramgps;
  AG`Frob:=Frob;
  AG`f:=A`K`artinrepdata`f;
  AG`r:=r;
  char:=ComplexConjugate(Character(A)); 
  AG`co:=[* <1-x,1,LocalRepresentation(A`K,char,p)> *];
  AG`F:=F;
  AG`act:=act;
  if Minimize then AG:=Minimise(AG); end if;
  return AG;
end intrinsic;


/////////////////////////////////////////////////////////////
//    Galois representations of Dirichlet characters       //
/////////////////////////////////////////////////////////////


intrinsic GaloisRepresentation(chi::GrpDrchElt, p::RngIntElt: Precision:=40) -> GalRep
{Local Galois representation at p of a Dirichlet character chi.}
  require (p ge 2) and IsPrime(p): "p must be a prime number";
  return GaloisRepresentation(ArtinRepresentation(chi),p: Precision:=Precision);
end intrinsic;

// do this w/o going via ArtRep? or for GrpHeckeElt?


/////////////////////////////////////////////////////////////
//    Galois representations of modular forms              //
/////////////////////////////////////////////////////////////


intrinsic GaloisRepresentation(f::ModFrmElt, p::RngIntElt: Precision:=40) -> GalRep
{Local Galois representation at p of a modular form f.}

  require (p ge 2) and IsPrime(p): "p must be a prime number";
  N:=Level(f);
  require N mod p^2 ne 0: 
    "Not implemented when p^2 divides the level";
  require Type(BaseRing(f)) in [RngInt,FldRat]: 
    "Modular form must be defined over Q";
  if not assigned f`is_newform or not f`is_newform then
    "WARNING: Modular form is not known to be a newform";
  end if;
  F:=pAdicField(p,Precision);

  a1:=Q!Coefficient(f,p);
  a2:=Q!DirichletCharacter(f)(p) * p^(Weight(f)-1);

  R:=PR(Q); x:=R.1;    
  if N mod p ne 0 then                                      // good 
    return UnramifiedRepresentation(F,1-a1*x+a2*x^2);  
  end if;

  return UnramifiedCharacter(F,a1)*SP(F,1-p*x,2);           // p||Level

end intrinsic;


