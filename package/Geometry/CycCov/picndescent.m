freeze;

//
//  Pic1desc.m
//  BrendanCreutz
//	Sept. 2011
//
//	Intrinsics for descents on hyperelliptic Jacobians
//  and on the Pic1 torsor.
//
//
//

import "../CrvG2/selmer.m" : MakeTry, CasselsKernel;
import "../Algaem/resolvent.m" : degnres;
import "localfieldsDB.m" : RelativeExtensionsOfQ_pzeta_p, AbsoluteExtensionsOfQ_5,
  AbsoluteExtensionsOfQ_3;

declare verbose ConstantNeighborhoods, 2;
declare attributes JacHyp: TwoSelmerSet;
declare attributes JacHyp: TwoSelmerRank;
declare attributes CrvHyp: ResolventFactorization;

/***********************************************************************************
 Processing precision errors from p-adic Roots and Factorization
 ***********************************************************************************/
//Since the returned string has unpredictable linebreaks in it,
//remove all non-alphabetic characters from either string and compare those.

alphabetic_characters:={CodeToString(c): c in {StringToCode("A")..StringToCode("Z")}
                                         join {StringToCode("a")..StringToCode("z")}};

FactorizationErrorMessage:=&cat[a
   : a in Eltseq("Runtime error in'LocalFactorization': Factorization: Insufficient precision in factorization of a non-squarefree polynomial.")
   | a in alphabetic_characters];

RootFindingErrorMessage:=&cat[a
   : a in Eltseq("Runtime error in 'Roots': Insufficient precision to find roots")
   | a in alphabetic_characters];

function IsFactorizationPrecisionError(ERR)
   return FactorizationErrorMessage eq
          &cat[a: a in Eltseq(ERR`Object) | a in alphabetic_characters];
end function;

function IsRootFindingPrecisionError(ERR)
   return RootFindingErrorMessage eq
          &cat[a: a in Eltseq(ERR`Object) | a in alphabetic_characters];
end function;

/***********************************************************************************
***********************************************************************************/



SwapVar := func< a | a ne 0 select &+[ Coefficient(a,i)*Parent(a).1^(Degree(a)-i) : i in [0..Degree(a)]] else 0 >;

intrinsic MonicModel(f :: RngUPolElt,q :: RngIntElt) -> RngUPolElt
{A model for the cyclic cover y^q = f(x) of the form y^q = cg(x)
 with g monic}
  // make a change of variables so that C: y^q = f is isomorphic to
  // C_2: y^q = c*f_mon(x) with f_mon(x) monic of the same degree.
  kpol := Parent(f);
  k := BaseRing(kpol);
  R<X,Y,Z> := PolynomialRing(k,3);
  d := Degree(f);
  lcf := LeadingCoefficient(f);
  //flcf := [ pp : pp in Factorization(Numerator(lcf)) | pp[2] ge q ];
	
  if d mod q eq 0 then
    while Evaluate(f,0) eq 0 do
      f := Evaluate(f,kpol.1+1);
    end while;
    if not &and[ IsIntegral(c) : c in Coefficients(f/lcf) ] then
      f2 := SwapVar(Evaluate(SwapVar(f),kpol.1*lcf));
      if IsIrreducible(f2) and Degree(k) eq 1 then
        //we can use this trick to get a nicer model
        O_A := Integers(ext<k|f/lcf>);
        // call optimised representation?
        f_mon := MinimalPolynomial(O_A.2);
        if q eq 2 and Degree(k) eq 1 then
          lcf *:= &*([ pp[1]^(- q*(pp[2] div q)) : pp in Factorization(Numerator(lcf)) ] cat [1]);
        end if;
        f2 := lcf*Polynomial([ k ! c : c in Coefficients(f_mon) ]);
	//f2 *:= &*([1] cat [ pp[1]^(- q*(pp[2] div q)) :  pp in Factorization(Numerator(lcf)) ]);
      end if; //IsIrreducible(f2)
    else // not &and[ IsIntegral(c) : c in Coefficients(f/lcf) ]
      f2 := f;
      if q eq 2 and Degree(k) eq 1 then
        f2 *:= &*([ pp[1]^(- q*(pp[2] div q)) :
           pp in Factorization(Numerator(lcf)) ] cat [1]);
      end if;
    end if;
    return f2;
  else // d mod q eq 0
    // homogenize differently:
    // f(x,z^q) = a_0*x^d + a_1*x^(d-1)*z^q + ... + a_d*z^(q*d)
    n := Integers()!( -(GF(q)!d)^1);
    f := Polynomial( [ k | Coefficient(f,j)*lcf^((d-j)*(q-n)-1) : j in [0..d-1] ] cat [1] );
    // (leading coefficient is now 1);
    // x2 <- c^n*x
    // z2 <- c*z
    // y2 <- c^((dn+1)/q - d)*y
    // satisfy y2^q = f(x2)
    return f;
  end if; // d mod q eq 0
	
end intrinsic; //MonicModel


CasselsKernel2 := function(f);
  // the imported CasselsKernel only works for genus 2
  d := Degree(f);
  if d eq 6 then
    CasGlob, resfact, subext_disc := CasselsKernel([a[1] : a in Factorization(f)]);
    return CasGlob,resfact;
  end if;
  ress := degnres(f,d div 2);
  resfact := Factorization(ress);
  CasGlob := exists{ r[1] : r in resfact | Degree(r[1]) eq 1 };
  return CasGlob,[ a[1] : a in resfact ];
end function; //CasselsKernel2


SelmerDiagram := function(f,S,q : Fields);

//==============================================================//
//                                                              //
//  Returns maps defining the following diagram                 //
//  where Prod_p is the product over p in S.                    //
//                                                              //
//  A ---------AtoASqmodk-----------> G > KerNorm + c1          //
//  |                                 |                         //
//  |                                 |                         //
// respFlds                         respGrps                    //
//  |                                 |                         //
//  |                                 |                         //
//  v                                 v                         //
// Prod_v K_v ----ApModqQs---------> G_v                        //
//                                                              //
//                                                              //
//  A = Q[x]/f                                                  //
//  G is the unramified outside S subgroup of                   //
//   either (A^* / A^*q) or (A^* / k^*A^*q) depending on        //
//   whether degree(f) is prime to q or not.                    //
//                                                              //
//  G_v is the local version (G tensored with k_v)              //
//                                                              //
//  c_1 is an element of G whose norm is = c mod k^*q           //
//  KerNorm is the kernel of the norm                           //
//                                                              //
//  AtoLocs is the map top left to bottom right                 //
//                                                              //
//==============================================================//

  c := LeadingCoefficient(f);
  kpol := Parent(f);
  k := BaseRing(kpol);

  if Degree(f) mod q eq 0 then
    modscalars := true;
  else
    modscalars := false;
  end if;	

  // Handle Q differently.
  if Type(k) eq FldRat then
    k := NumberField(kpol.1-1 : DoLinearExtension);
  end if;
  
  O_k := MaximalOrder(k);
  A := quo<kpol|f>; // The etale algebra corresponding to the roots of f
  vprintf Selmer, 3: "    Computing class/unit group info.\n";
  ASq,AtoASq,mB,B := pSelmerGroup(A,q,Set(S):Raw := true);
  kSq,ktokSq := pSelmerGroup(q,Set(S));
  
  vprintf Selmer, 3: "kSq generated by :%o.\n", {Inverse(ktokSq)(a) : a in Generators(kSq) };
  ImageOfkSq := { AtoASq(Inverse(ktokSq)(a)) : a in Generators(kSq) };
		
  // Quotient to obtain A(S,q)/k(S,q) 
  if modscalars then
    ASqmodk, modk := quo<ASq | ImageOfkSq>;
  else
    ASqmodk := ASq;
    modk := hom< ASq -> ASq | OrderedGenerators(ASq)>;
  end if;
  // Labelling maps...
  AtoASqmodk := AtoASq * modk;
  ASqmodktoA := Inverse(AtoASqmodk);
  modki := Inverse(modk);
  //ClearDenom := func<g | g*LCM([ Denominator(d) : d in Coefficients(g) ])>;
  //AtoASqQ := map< A -> ASqQ | x :-> AtoASqQ(ClearDenom(x)) >; 
  //Clearing denoms is not neccessary if we take f = c*monicpoly

  vprintf Selmer, 3: "    Getting representatives in A using power products.\n";
  B := Eltseq(B);
  // Representatives in A for the generators of ASqmodk (will be used later)
  repAs := [ PowerProduct(B,[c mod q : c in Eltseq(mB(g @@ modk))] ) : g in OrderedGenerators(ASqmodk) ];

  // Define the norm on ASqmodk
  NB := [Norm(b) : b in B];
  // N : A(S,q) -> k(S,q)
  Norm1 := hom< ASq -> kSq | [ktokSq(PowerProduct(NB,[c mod q : c in Eltseq(mB(g))])) : g in OrderedGenerators(ASq)] >;
  // N2 : A(S,q)/k(S,q) -> k(S,q)
  Norm2 := hom< ASqmodk -> kSq | [ Norm1( a @@ modk ) : a in OrderedGenerators(ASqmodk) ] >;
  // The Norm condition
  bool, c1 := HasPreimage(ktokSq(1/c),Norm2);
  Ker := Kernel(Norm2);
  // Representation of the coset c1*Ker:
  _, modKer := quo<ASqmodk | Ker>;
  if bool then
    NormAndPreimc := <modKer, c1>;
    // The coset of KSqQ of elements satisfying the norm condition is
    // { c1 @@ quomap + x : x in Ker(quomap) }
  else
    // The norm condition is not satisfiable.
    NormAndPreimc := <modKer,{}>;
  end if;

  vprintf Selmer, 3: "    Computing absolute algebra.\n";
  // Represents A as a cartesian product of number fields.
  Aflds, AtoAflds := AbsoluteAlgebra(A : Fields := Fields);

  LocalSelmerGroup := function(K,v);
  // *******************
  //  input: 
  //  K: a number field (one of the factors of Aflds)
  //  v: a prime ideal of Integers(k)
  //  (We will work with K_v = K tensor k_v given as a Cartsesian product of completions of K)
  // 
  //  output: maps
  //   ModqthPowers: PROD K_w --> PROD K_w^* / K_w^*q  	
  //   KtoKtensork_v: K --> PROD K_w
  // ******************* 

    O_K := MaximalOrder(K);
    pids := [ pid : pid in Factorization(ideal<O_K| Generators(v)>)];
    injs := [];
    ress := [];
    dim := 0;

    for pid in pids do
      K_p, inj := Completion(K,pid[1]);
      K_p`DefaultPrecision *:= 2*RamificationIndex(pid[1])*Degree(pid[1]);
      G,m := pSelmerGroup(q,K_p);
      injs cat:= [inj];
      ress cat:= [m];
      dim +:= #Generators(G);
    end for; // pid in pids

    G := AbelianGroup([ q : i in [1..dim]]);
    dima := 0;
    lis := [];
    for i in [1..#injs] do
      G_i := Codomain(ress[i]);
      lis cat:= [hom< G_i -> G | [G.(i+dima) : i in [1..#Generators(G_i)]] >];
      dima +:= #Generators(G_i);
    end for; // i 

    ModqthPowers := map< CartesianProduct([K_p : K_p in [ Domain(m) : m in ress]]) -> G | x :-> &+[ lis[i](ress[i](x[i])) : i in [1..#ress] ]>;
    KtoKtensork_v := map< K -> Domain(ModqthPowers) | x :-> < injs[i](x) : i in [1..#injs] > >;
    return ModqthPowers, KtoKtensork_v,pids;

  end function; // LocalSelmerGroup


  // The following will be sequences (parameterized by S) of maps to the various local objects
  respGrps := [];
  AtoLocs := [];
  CompletionsOfk := [];

  // Deal with Q differently
  if Degree(k) eq 1 then
    kk := Rationals();
  else
    kk := k;
  end if;

  for v in S do
		
    KstoKvqs := <>;
    pids := <>;
    vprintf Selmer, 3: "    Computing Local Selmer Groups at the prime v = %o.\n", v;
    for i in [1..NumberOfComponents(Aflds)] do
      m1,m2,pids_i := LocalSelmerGroup(Aflds[i],v);
      Append(~KstoKvqs, <m1,m2>);
      Append(~pids,pids_i);
    end for;// i in [1..NumberOfComponents(Aflds)]
    
    //Piece everything together and (if modscalars then) take the quotient by the image of k_v under diagonal embedding.
    Avq := CartesianProduct([Codomain(m[1]) : m in KstoKvqs ]);	
    Avq2 := AbelianGroup( &cat([ [q : i in [1..#Generators(Codomain(M[1]))] ]  : M in KstoKvqs ]));
    AvqtoAvq2 := map< Avq -> Avq2 | x :-> Avq2 ! &cat([ Eltseq(x[i]) : i in [1..NumberOfComponents(Avq)] ]) >;
    k_v,ktok_v := Completion(kk,v);
   // if Degree(k) gt 1 then
      k_v`DefaultPrecision := 50*(q-1);
   // end if;
    k_vq, k_vtok_vq := pSelmerGroup(q,k_v);
    k_vqtok_v := Inverse(k_vtok_vq);
    vprintf Selmer, 3: "k_vmodq-th powers generated by %o.\n", { k_vqtok_v(a) : a in Generators(k_vq) };
    // The diagonal image of k_v in K_v
    if modscalars then	
      Imk_v := sub<Avq2 | [&cat[ Eltseq( M[1](M[2](Inverse(ktok_v)(k_vqtok_v(g))))) : M in KstoKvqs ] : g in OrderedGenerators(k_vq) ]>;
    else
      Imk_v := sub<Avq2 | Avq2!0>;
    end if;
    //vprintf Selmer, 3: "  its image in Avq is %o.\n", Imk_v;
    // Quotient by Imk_v to get the local (at v) version of A^* / k^*A^*q or A^* / A^*q 
    Avqmodk_v, modk_v := quo<Avq2| Imk_v>;
    AtoAvqmodk_v := map< A -> Avqmodk_v | 
      x :-> modk_v(AvqtoAvq2( Avq ! < KstoKvqs[i][1](KstoKvqs[i][2]( AtoAflds(x)[i] )) 
      : i in [1..NumberOfComponents(Aflds)] > )) >; 
    ASqmodkToAvqmodk_v := hom< ASqmodk -> Avqmodk_v | 
      [ modk_v(Avq2 ! &cat[ Eltseq( KstoKvqs[i][1] ( KstoKvqs[i][2] ( AtoAflds(x)[i] ) ) ) 
      : i in [1..NumberOfComponents(Aflds)] ]) : x in repAs] >;
    //store this information for later use:
    respGrps cat:= [ASqmodkToAvqmodk_v];
    AtoLocs cat:= [AtoAvqmodk_v];
    CompletionsOfk cat:= [ <ktok_v,k_vtok_vq,pids> ];
  //error if v eq 2, "";
  end for; // v in S
  return NormAndPreimc,AtoASqmodk,ASqmodktoA,respGrps,AtoLocs,
         repAs,CompletionsOfk,AtoAflds, modki*mB, B;

end function; //SelmerDiagram


intrinsic PicnDescent(f :: RngUPolElt,q :: RngIntElt : Safety := 0, Fields := {}) -> Tup
{Computes fake phi-Selmer group of Jac(C) and the fake phi-Selmer set of Pic^1(C).}

// Doing a phi-descent on the curve y^q = f(x)

// In order to compute the phi-Selmer group of Pic^1 we need:
//  (q = 2) C has index one everywhere locally
//  (q > 2) C has points everywhere locally 
if q eq 2 then
  MethodIsValid := HasIndexOneEverywhereLocally(f,2);
else
  MethodIsValid := true;
  // we will check later to see if the curve is ELS
end if;
Pic1kEmpty := false;
// Issues to keep in mind:
  // when q > 2:
   // If C is not ELS, Pic1 descent is not proven to 
   // give the Selmer set of Pic1, though it may still
   // prove Pic1(k) is empty, provided the curve has index one locally
  // for all q
   // If C does not have period 1 everywhere locally,
   // then Pic^0(C) may not equal J(k), so we are not able 
   // to compute the Selmer group of the Jacobian.

kpol := Parent(f);
x := kpol.1;
k := BaseRing(f);
if Degree(k) gt 1 then
  k<alpha> := k;
end if;
k0 := k;
f_original := f;

f := MonicModel(f,q);

// We need the q-th roots of unity.
if #Roots(CyclotomicPolynomial(q),k) eq 0 then
  k<zeta> := ext<k|CyclotomicPolynomial(q)>;
  if Degree(k0) ne 1 then
    k<nu> := AbsoluteField(k);
  end if;
  kpol := PolynomialRing(k); x := kpol.1;
  f := Evaluate(f,kpol.1);
  vprintf Selmer, 1: "  Adjoining %o-th roots of unity to base field.\n", q;
end if;

O_k := Integers(k);
vprintf Selmer, 1: "Doing descents for the curve with defining equation: y^%o = %o defined over %o.\n", q, f_original, k;


lcf := LeadingCoefficient(f);
f_mon := f/lcf;
//error if not &and[ IsIntegral(c) : c in Coefficients(f_mon) ], "you didn't give me a c*monic model";
// TO DO: Check that Integral Model works correctly, then use it.
// f := MonicModel(f,q);
// should give a change variables so that f_new = c * monic defines an isomorphic curve

degree := Degree(f);
g := degree mod q eq 0 select Integers()!((degree - 2)*(q-1)/2) else Integers()!((degree-1)*(q-1)/2);

vprintf Selmer, 1: "  Model changed to y^%o = %o.\n", q, f;
vprintf Selmer, 3: "  Curve has genus %o.\n", g;

fact := [ a[1] : a in Factorization(f_mon) ];
PrimeToq := exists(primetoqf){ a : a in fact | GCD(Degree(a),q) eq 1 };
PrimeToqGlob := PrimeToq;

// We now want to compute a lower bound for J(k)[phi] (it can yield better rank bounds)
ranktorsglobal := #fact-1;
if degree mod q ne 0 then ranktorsglobal +:= 1; end if; // to account for ramification above infinity.
extratwotorsion := 0; // until we show otherwise we assume this to be the case. (see below)
flagphitorsglobal := false; // this flag will be set to true if we encounter problems computing J(k)[phi]

if PrimeToq then
  Seltofakeinj := true;
  resfact := [];
  CasGlob := true;
  ranktorsglobal -:= 1; // ranktors = #ramification points - 2.
else
  if q eq 2 then
    CasGlob, resfact := CasselsKernel2(f);
    vprintf Selmer, 3: "  Resolvent factors as: %o.\n", resfact;
    if g mod 2 ne 0 then
      Seltofakeinj := false;
      //We need the roots of resfact can lead to extra 2-torsion.
      roots := &cat[ [ r[1] : r in Roots(g)  ]: g in resfact ] ;
      DegreesOfFactors := [ Degree(g) : g in fact ];
      Pd := Partitions(Integers()!(degree/2));
      PartitionsOfRoots2 := 0;
      for P in Pd do
        vals := Set(P);
	ct := 1;
        for v in vals do
          v1 := #[ w : w in P | w eq v ];
          v2 := #[ w : w in DegreesOfFactors | w eq v];
          ct *:= Binomial(v2,v1);
          if ct eq 0 then break; end if;
        end for;
        PartitionsOfRoots2 +:= ct;
      end for;
      PartitionsOfRoots2 := Integers()!(PartitionsOfRoots2/2);
      //PartionsOfRoots2 is the number of distinct partitions of the roots of f into 
      //2 Galois stable subsets of equal size. These correspond to roots of the resolvent
      //which are accounted for by the factorization of f.
      if Ilog(2,#roots - PartitionsOfRoots2 + 1) gt 0 then
      //there are 2-torsion points coming from a proper factorization over a quadratic extension.
      //if f has factors of degree 2, some of these may lead to the torsion points.
      dblct := Max([0,#[ g : g in fact | Degree(g) eq 2 ]-1]);
    else
      dblct := 0;
    end if;
      dimn := Ilog(2,#roots - PartitionsOfRoots2 + 1) - dblct;
      extratwotorsion := Ilog(2,#roots - PartitionsOfRoots2 + 1) - dblct;
      vprintf Selmer, 1: "    Factorizations over quadratic extensions ==> %o extra dimensions of 2-torsion.\n", extratwotorsion;
      ranktorsglobal +:= extratwotorsion;
    else
      Seltofakeinj := CasGlob;
      // g = 0 mod 2 no factors of odd degree
    end if; // g mod 2 ne 0
  else // q eq 2
    Seltofakeinj := false;
    resfact := [];
    CasGlob := false;
    flagphitorsglobal := true;
    vprintf Selmer, 2: "Computation of J(k)[phi] not implemented for this case.\n";
  end if; //q eq 2
	
end if; //PrimeToq

discr := O_k!Discriminant(f);
if Type(k) eq FldRat then
  S_small := Setseq( { p[1] : p in Factorization(discr) | p[2] ge 2 } 
    join { p[1] : p in Factorization(Numerator(lcf*q)*Denominator(lcf*q)) });
else
  S_small := Setseq({ p[1] : p in Factorization(discr*O_k) | p[2] ge 2 }
    join { p[1] : p in Factorization(lcf*q*O_k) } );
end if;
//if SSize eq "Small" then
S := S_small;

// S is the set of bad primes. This can be fed in as a set of rational primes
// in which case we take the primes of k above these, or a set of prime ideals of O_k
if Type(Random(S)) eq RngOrdIdl then
  S := [ pid[1] : pid in Factorization((&*S)) ];
end if;

//Reorder the primes to put q last
S_1 := Sort([ a : a in S | Norm(a) mod q ne 0 ]);
S_2 := [ a : a in S | Norm(a) mod q eq 0 ];
S := S_1 cat S_2;


//Now we do all the class/unit group computations and compute all the restriction maps.
vprintf Selmer, 2: "  Constructing Local-Global Selmer diagram:\n    Discriminant(O_A) = %o.\n    Set of bad primes is S = %o.\n", discr, S;
NormAndPreimc,AtoASqmodk,ASqmodktoA,respGrps,AtoLocs,
    repAs,CompletionsOfk,AtoAflds, toVec, FB := SelmerDiagram(f,S,q : Fields := Fields);
A := Domain(AtoASqmodk); // the etale algebra as RngUPolRes.
Aflds := Codomain(AtoAflds);
AfldsToA := Inverse(AtoAflds);
ASqmodk := Codomain(AtoASqmodk); // The unramified outside S subgroup mod scalars and q-th powers
NASqmodktokq := NormAndPreimc[1]; // The induced norm on ASqmodk;
if Type(NormAndPreimc[2]) eq SetEnum then
  vprintf Selmer, 1: "  Norm condition not satisfiable.\n  --> Sel(C) and Sel(Pic^1(C)) are empty.\n";
  Pic1kEmpty := true;
  alpha_c := ASqmodk ! 0;
else
  alpha_c := NormAndPreimc[2]; // an element of norm = c mod k^*2
  //assert IsPower(Norm(ASqmodktoA(alpha_c))*lcf,q);
end if;

//printf "what is norm of alpha_c? %o.\n", Norm(ASqmodktoA(alpha_c));

vprintf Selmer, 2: "  Unramified outsides S subgroup of L*/k*L*^q has dimension %o.\n", Ngens(ASqmodk);
vprintf Selmer, 2: "  Bound on dimension of fake Selmer group after norm condition : %o.\n", NumberOfGenerators(Kernel(NormAndPreimc[1]));

muOfTors := function(factor,cofactor,lc);
  //determines the image of the divisor sum (x,0) as x runs over roots a factor of f.
  sign,w := Max([(q-1)*Degree(factor),Degree(cofactor)]);
  if w eq 1 then
    return (-1)^sign*(factor-(lc*cofactor)^(q-1));
  else
    return (-1)^sign*(cofactor^(q-1)-lc*factor);
  end if;
end function; //muOfTors


// Determine the image of some known points.
if ranktorsglobal gt 0 and #fact gt 1 then
  if not PrimeToq then
    // all factors of f define divisors of degree = 0 mod q
    Im_tors := {};
    for g in fact do
      cofactor := &*[ h : h in fact | h ne g];
      Include(~Im_tors,AtoASqmodk(Evaluate(muOfTors(g,cofactor,lcf),A.1)));
    end for;
  else
    //primetoqf is a divisors of degree prime to q
    cofactor := &*[ h : h in fact | h ne primetoqf];
    imageofprimetoqf := AtoASqmodk( Evaluate(muOfTors(primetoqf,cofactor,lcf),A.1));
    dp_v := Degree(primetoqf);
    //imprimetoq_v is the image under Pic(C) --> ASQmodk of a divisor of degree dp_v.
    im1global := (Integers()!((GF(q)!dp_v)^-1))*imageofprimetoqf;
    //im1global is the image of a divisor of degree 1 (which is not neccesarily a point)
	
    // We compute the images of the ramifiction points
    // and save them as they will be needed for descent on the curve.
    muOmegaGlobal := {};
    for g in { g : g in fact | Degree(g) eq 1 } do
      cofactor := &*[ h : h in fact | h ne g];
      image := AtoASqmodk( Evaluate(muOfTors(g,cofactor,lcf),A.1) );
      //vprintf Selmer, 3:  "       Ramification point x=%o maps to %o\n", Roots(g)[1][1], Eltseq(image);
      Include(~muOmegaGlobal,image);	
    end for;		
    //vprintf Selmer, 3: "        Image of k-rational ramification points : %o.\n", {Eltseq(a) : a in muOmegaGlobal};
    // we compute the image of some phi-torsion points.
    Im_tors := {};
    for g in fact do
      cofactor := &*[ h : h in fact | h ne g];
      Include(~Im_tors,AtoASqmodk(Evaluate(muOfTors(g,cofactor,lcf),A.1)) - Degree(g)*im1global);
    end for;
  end if;
else // ranktorsglobal gt 0
  Im_tors := { ASqmodk ! 0 };
end if;

//This is the image under (x-T) of some of the k-rational phi-torsion
muJktors := sub< ASqmodk | Im_tors >;

LocalImages := function(v);
  // Computes the images of (x-T) on Pic^0(C) and Pic^1(C) over k_v
  // v is a prime ideal of O_k (or a rational prime if k eq Q...
  vprintf Selmer, 1: "\n\n  Computing local image at %o.\n",v;
  //Import data from SelmerDiagram:
  ind_v := Index(S,v);
  AtoLoc := AtoLocs[ind_v];
  Avqmodk_v := Codomain(AtoLoc);
  res_v := respGrps[ind_v];
	
  //printf "kernel and image of res_v are %o\n\n %o\n\n", Kernel(res_v), Domain(res_v);
  k_vdata := CompletionsOfk[ind_v];
  pids := k_vdata[3];
  ktok_v := k_vdata[1];
  k_v := Codomain(ktok_v);
  modqthpowers := k_vdata[2];
  k_vq := Codomain(modqthpowers);
  Onemodqthpowers := k_vq ! 0;
  if Type(k) eq FldRat then
    O_v := pAdicRing(v);
    O_ktoO_v := map< O_k -> O_v | x :-> O_v ! x >;
    O_vtoO_k := map< O_v -> O_k | x :-> O_k ! x >;
    k_vtok := map< k_v -> k | x :-> k ! x >;
    relDeg := 1;
    e_v := 1;
    nv := v;
  else
    O_v,O_ktoO_v := Completion(O_k,v);
    O_vtoO_k := Inverse(O_ktoO_v);
    k_vtok := Inverse(ktok_v);
    e_v := RamificationIndex(v);
    relDeg := Degree(v)*e_v;
    nv := Norm(v)^e_v;
  end if;
  k_v`DefaultPrecision +:= 2*Max([ Valuation(c,v) : c in Coefficients(f) | c ne 0 ]);
  O_v`DefaultPrecision +:= 2*Max([ Valuation(c,v) : c in Coefficients(f) | c ne 0 ]);
  k_v`DefaultPrecision *:= (2*e_v);
  O_v`DefaultPrecision *:= (2*e_v);	
  pi_v := UniformizingElement(O_v);
  pi := O_vtoO_k(pi_v);
  p := Factorization(nv)[1][1]; // rational prime under v
  liesaboveq := nv mod q eq 0; // is p = q?
  k_vpol := PolynomialRing(k_v);
  O_vpol := PolynomialRing(O_v); 
  F_v,modv := ResidueClassField(O_v);
  FF := PolynomialRing(F_v); xbar := FF.1;
  // functions for coercing polynomials around
  Polytok_v := func< h | h ne 0 select Polynomial([ O_ktoO_v(c) : c in Coefficients(h)]) else O_vpol!0>;
  Polytok := func< h | Polynomial([ O_vtoO_k(c) : c in Coefficients(h)])>;
  PolytoF_v := func< h | Polynomial([ modv(O_ktoO_v(c)) : c in Coefficients(h)])>;
  Polymodvtok := func< h | h ne 0 select Polynomial([ O_vtoO_k(c @@ modv)  : c in Coefficients(h)]) else kpol!0>;
	
  fmonlocal := Polytok_v(f_mon);
  flocal := O_ktoO_v(O_k!lcf)*fmonlocal;
  f_F := PolytoF_v(f);
  // valuation of a polynomial:
  dpolys := func< g,h | g-h ne 0 select Min([ Valuation(c,v) : c in Coefficients(g-h) ]) else Infinity() >;

  muOmega := {}; // initializing image of ramification points (and point above infinity)
  Foundim1 := false; // until we get our hands on a divisor of degree 1.
  im1 := Avqmodk_v ! 0;
	
  // We have finished setting up our 'notation'.
  // Now factor f locally to determine size of local image etc.
  ff := [ a[1] : a in Factorization(fmonlocal) ];
  //Sometimes there are precision problems? 
  // if this persists do try--catch--increase precision... 

  ranktors := #ff - 1;
  if degree mod q ne 0 then ranktors +:= 1; end if; // to account for the ramification point above infinity
  PrimeToq := exists(primetoq_v){ a : a in ff | Degree(a) mod q ne 0 };
  if PrimeToq then
    // Locally we have a divisor of degree prime to q. 
    // This makes things a bit easier.
    resfact_v := [];
    CasLocal := true;
    ranktors -:= 1; // so in total ranktors = #ff - 2 (counting the extra factor at infty)
    vprintf Selmer, 1: "    Local Cassels kernel is trivial.\n";
    Foundim1 := true;
    vprintf Selmer, 2: "      Found k_v-rational divisor of degree 1 .\n";
    if degree mod q ne 0 then
      im1 := Codomain(AtoLoc)!0;
      Include(~muOmega,im1);
      //im1 is the image of the ramification point above infty
    else
      cofactor := &*[ g : g in ff | g ne primetoq_v];
      imprimetoq_v := AtoLoc(Evaluate( Polytok(muOfTors(primetoq_v,cofactor,(O_ktoO_v(lcf)))),A.1));
      //printf " the factor %o maps to %o.\n", primetoq_v, imprimetoq_v;
      dp_v := Degree(primetoq_v);
      //imprimetoq_v is the image under Pic(C) --> localSel of a divisor of degree dp_v.
      im1 := (Integers()!((GF(q)!dp_v)^-1))*imprimetoq_v;
      //im1 is the image of a divisor of degree 1 (which is not a point)
    end if;
    // We compute the images of the ramifiction points
    // and save them as they will be needed for descent on the curve.
    for g in { g : g in ff | Degree(g) eq 1 } do
      cofactor := &*[ h : h in ff | h ne g];
      image := AtoLoc( Evaluate(Polytok(muOfTors(g,cofactor,(O_ktoO_v(lcf)))),A.1) );
      //vprintf Selmer, 3:  "       Ramification point x=%o maps to %o\n", Roots(g)[1][1], Eltseq(image);
      Include(~muOmega,image);	
    end for;		
    //vprintf Selmer, 3: "        Image of ramification points : %o.\n", {Eltseq(a) : a in muOmega};
    if ranktors gt 0 then
      // we compute the image of all phi-torsion points.
      Im_tors := {};
      for g in ff do
        cofactor := &*[ h : h in ff | h ne g];
        imtt := AtoLoc(Evaluate(Polytok(muOfTors(g,cofactor,(O_ktoO_v(lcf)))),A.1)) - Degree(g)*im1;
        vprintf Selmer, 3: "factor %o maps to %o.\n", g, Eltseq(imtt);
        Include(~Im_tors,imtt);
      end for; // g in ff
    else
      Im_tors := { Avqmodk_v ! 0 };
    end if; //ranktors gt 0
    //Im_tors is the image under (x-T) of the phi-torsion in J(k_v)
		
  else //PrimeToq
    // Compute the image of effective divisors of degree 1
    if IsPower(ktok_v(lcf),q) then
      Foundim1 := true;
      im1 := Codomain(AtoLoc)!0;
      vprintf Selmer, 2: "      Found k_v-rational divisor of degree 1 .\n";	
      // image of a point above infinity
    end if;
		
    Im_tors := {};
    if #ff gt 1 then
      for g in ff do
        cofactor := &*[ h : h in ff | h ne g];
        Include(~Im_tors,AtoLoc(Evaluate(Polytok(muOfTors(g,cofactor,(O_ktoO_v(lcf)))),A.1) ));
      end for;
    else
      Im_tors := { Avqmodk_v ! 0};
    end if;
    //Im_tors is most of the image under (x-T) of the phi-torsion in J(k_v)
    //For q eq 2 and g odd there can be extra torsion coming from factorization 
    //over quadratic extensions which is not accounted for.
    //For q odd, the situation can be more complicated and is not yet satisfactorily dealt with.

    if q eq 2 then
		
      if (g mod 2 eq 0 and CasGlob) or #resfact eq 0 or PrimeToq then
        CasLocal := true;
	// no need to consider the resolvent again.
      else
        //we need to see if the resolvent has roots locally.
        if #resfact gt 0 then
          k_v_stored_precision:= k_v`DefaultPrecision;
          valres := Max( [ Max([Valuation(ktok_v(c)) : c in Coefficients(res) | c ne 0 ]) : res in resfact ]);
		
          k_v`DefaultPrecision := Max([ k_v`DefaultPrecision,Integers()! valres+5]);
          roots := [];
          for g in resfact do 
            while true do
              resP:=Polynomial([ ktok_v(c) : c in Coefficients(g)] );
              try
                roots cat:= [ r[1] : r in Roots(resP)];
                no_error:=true;
              catch ERR
                if IsRootFindingPrecisionError(ERR) then
                  no_error:=false;
                else
                  error ERR;
                end if;
              end try;
              if no_error then break; end if;
              k_v`DefaultPrecision *:= 2;
              vprintf Selmer, 3: "    Finding roots of resolvent requires: increasing precision to %o", k_v`DefaultPrecision;
            end while;
          end for;
          k_v`DefaultPrecision:=k_v_stored_precision;
          vprintf Selmer, 3: "    Resolvent has %o roots locally.\n",#roots;
        end if; //#resfact gt 0
		
        if g mod 2 eq 0 then
          CasLocal := #roots gt 0;
        else
          CasLocal := false;
          // g is odd.
          // We need the roots of resfact can lead to extra 2-torsion.
          DegreesOfFactors := [ Degree(g) : g in ff ];
          Pd := Partitions(Integers()!(degree/2));
          PartitionsOfRoots2 := 0;
          for P in Pd do
            vals := Set(P);
            ct := 1;
            for v in vals do
              v1 := #[ w : w in P | w eq v ];
              v2 := #[ w : w in DegreesOfFactors | w eq v];
              ct *:= Binomial(v2,v1);
              if ct eq 0 then break; end if;
            end for;
            PartitionsOfRoots2 +:= ct;
          end for;
          PartitionsOfRoots2 := Integers()!(PartitionsOfRoots2/2);
          vprintf Selmer,3 : "Partitions coming from factorization %o.\n",PartitionsOfRoots2;
          //PartionsOfRoots2 is the number of distinct partitions of the roots of f into 
          //2 Galois stable subsets of equal size. These correspond to roots of the resolvent
          //which are accounted for by the factorization of f.
          if Ilog(2,#roots - PartitionsOfRoots2 + 1) gt 0 then
            //there are 2-torsion points coming from a proper factorization over a quadratic extension.
            //if f has factors of degree 2, some of these may lead to the torsion points.
            dblct := Max([0,#[ g : g in ff ] - 2]);
          else
            dblct := 0;
          end if;
          vprintf Selmer,3 : "Size before double count %o\n", Ilog(2,#roots - PartitionsOfRoots2 + 1);
          vprintf Selmer,3 : "Double counted = %o.\n", dblct;
          dimn := Ilog(2,#roots - PartitionsOfRoots2 + 1) - dblct;
          vprintf Selmer, 1: "    Factorizations over quadratic extensions ==> %o extra dimensions of 2-torsion.\n", dimn;
          ranktors +:= dimn;
        end if;	 // g mod 2 eq 0
			
      end if; // g mod 2 eq 0 and CasGlob or #resfact eq 0 
    else // q eq 2
		  
      if q eq 3 and Degree(f) eq 6 then
				
        // there are really only two possibilities for the factorization type:
        // irreducible ==> phi-torsion has dim le 1, Cassels kernel is non trivial
        // (3,3) ==> same as above unless the Galois group is Z/3
        if #ff eq 1 then
          ranktors := 1;
          //if liesaboveq then ranktors -:= 1;	
          //"ASSUMED dim is 0 when it could be 1!"; end if;	
          CasLocal := false;
        else
          // f = cubic*cubic
          ranktors := 1;
          flagtorsion := true; // this lets us know we only have an upper bound.
          // in fact: ranktors = 2 iff both cubics split over the same cubic field
	  // otherwise ranktors = 1.
          // TO DO: deal with this!
          //printf "Flagging phi-torsion computation over %o.\n", k_v;
          //printf "Dimension computed is not necessarily an upper bound.\n";			
          CasLocal := false;
        end if; // #ff eq 1
      else
        if q eq 5 and Degree(f) eq 5 then
          // the only possibility is that $f$ is irreducible.
          // then J[phi] has dim le 1 and the Cassels Kernel is nontrivial so
          ranktors := 1;
          flagtorsion := true;// this lets us know we only have an upper bound.
          // in fact: ranktors = 1 iff f defines a cyclic extension
          // otherwise ranktors = 0
          printf "Flagging phi-torsion computation over %o.\n", k_v;
          printf "Dimension computed is only an upper bound.\n";			
          CasLocal := false;
        else
          error "Not yet implemented in this q = %o, Degree(f) = %o.\n", q, Degree(f);
        end if;
      end if;
    end if; //q eq 2
  end if; //PrimeToq

  // Determine dim(J(k_v)/phiJ(k_v)) and dimension of its image under (x-T)
  dim := ranktors + (liesaboveq select Integers()!(g*relDeg/(q-1)) else 0); 
  extraval := liesaboveq select 2*e_v else 0; 
  if not CasLocal then dimim := dim - 1; else dimim := dim; end if;
  vprintf Selmer, 1: "    J(k_v)[phi] has dimension %o.\n", ranktors;
  vprintf Selmer, 1: "    J(k_v)/phi(J(k_v)) has dimension %o, its image in the fake Selmer group has dimension %o.\n", dim, dimim;
  ImPic0 := sub<Avqmodk_v | Im_tors >;
  vprintf Selmer, 1: "    Obvious torsion generates a space of dimension %o.\n",Ngens(ImPic0);
  // At this point we know the size of the local image
  // We have computed the images of some torsion points
  // The next step is to search for divisors and take their images under (x-T) until we get
  // enough points.
  // To do this we will search for points over extensions of k_v of degree d
  // then take the images under (x-T) of their traces

  SwapVar := func< a | a ne 0 select &+[ Coefficient(a,i)*Parent(a).1^(Degree(a)-i) : i in [0..Degree(a)]] else 0 >;
  
  TraceOfxminusT := function(f,h,v,ktok_v);
    // Input: h in kpol of degree d defines an extension K_w of k_v of degree d.
    // Output: K_w, KtoK_w and the map C(K_w) --Tr--> Div^d(C_v) --(x-T)--> L_v*	
    //printf " Entering trace of x minus T using h = %o.\n",h;
    kpol := Parent(f);
    T := kpol.1;
    k := BaseRing(kpol);
    d := Degree(h);
    if d eq 1 then
      //effective divisor of degree 1 (i.e. points in C(k_v)) the map is easier:
      TraceMap := func< x |  (x @@ ktok_v) - T >;
      if (-Degree(f)) mod q in {0} then 
        TraceMap2 := func< z | (z @@ ktok_v)*(1 - (z@@ktok_v)*T) >;
      else
        TraceMap2 := func< z | (1 - (z)^q*T) >;
      end if;
      f_K := f;
      K_w := Codomain(ktok_v);
      KtoK_w := ktok_v;
      if Degree(k) ne 1 then
        K_wtoK := k_vtok;
      else
        K_wtoK := Inverse(KtoK_w);
      end if;
    else
      //need to construct the extension
      Krel := ext<k | h>;
      O_Krel := Integers(Krel);
      K := AbsoluteField(Krel);
      O_K := Integers(K);
    if Type(v) eq RngIntElt then
      vO_K := ideal< O_K | v >;
    else
      vO_K := ideal< O_K | [ O_K ! g : g in Generators(v) ] >;
    end if;
    p := Factorization(Norm(v))[1][1];
    pids := { Ideal(w[1]) : w in Decomposition(K,p) };
    wabovev := { w: w in Support(vO_K) } meet pids;
    // if the polys satisfy what I said there will be only one prime here.
    assert #wabovev eq 1;
    //wds := { w : w in wabovev | RamificationIndex(w)*Degree(w)/(RamificationIndex(v)*Degree(v)) eq Degree(Koverk) };
    w := Random(wabovev);
    K_w<eta>, KtoK_w := Completion(K,w);
    K_wtoK := Inverse(KtoK_w);
    K_w`DefaultPrecision +:= 2*Max([ Valuation(KtoK_w(K!c)) : c in Coefficients(f) | c ne 0 ])+extraval*d;
    K_w`DefaultPrecision *:= (d+1);
    f_K := Polynomial([ K ! c : c in Coefficients(f) ]);
    // think about if we need precision *:= d?
    TraceMap := function(x);
      // for (x,y) in C(K_w) computes prod_sigma (sigma(x) - T) in k[T]
      rp := RelativePrecision(x);
      if IsWeaklyZero(x) then
        xoverk := Krel!0;
      else
        xoverk := (x @@ KtoK_w);
        xoverk := Krel ! xoverk;
      end if;
      //if not (rp le Valuation(x - KtoK_w(xoverk))) then
        //printf "Started with x = %o, has relative precision %o.\n",x,RelativePrecision(x);
        //printf "K_w`DefaultPrecision = %o.\n",K_w`DefaultPrecision;
        //printf "K_wtoK(x) = %o.\n", K_wtoK(x);
        //printf "KtoK_w(K_wtoK(x)) = %o.\n", KtoK_w(K_wtoK(x));
        //printf "Valuation(x - KtoK_w(xoverk)) = %o.\n ", Valuation(x - KtoK_w(xoverk));
	//assert (rp le Valuation(x - KtoK_w(xoverk)));
      //end if;
      return (-1)^d*CharacteristicPolynomial(xoverk);	
    end function; //TraceMap
			
    if (-Degree(f)) mod q in {0} then 
      TraceMap2 := function(z);
        // As above, but used when z = 1/x in pi*O_v
        // computes prod_sigma sigma(z)*(1 - sigma(z)*T) = prod_sigma (1/sigma(z) - T)
        zoverk := Krel ! (z @@ KtoK_w);
        //return (-1)^d*CharacteristicPolynomial(zoverk^-1);
        return Norm(zoverk)^(q-1)*SwapVar(CharacteristicPolynomial(zoverk));
      end function;//TraceMap2
    else
      TraceMap2 := function(z);
        zoverk := Krel ! z;
        return SwapVar(CharacteristicPolynomial(zoverk^q));
      end function;//TraceMap2
    end if;//(-Degree(f)) mod q in {0}

    //printf " exiting TraceOfXminusT with K_w = %o\n", DefiningPolynomial(K_w);
    //assert Degree(DefiningPolynomial(K_w)) eq Degree(h);
  end if; // Degree(h) eq 1 
  return f_K,K_w,KtoK_w,K_wtoK,TraceMap,TraceMap2;
end function; // TraceOfxminusT
	

TamelyRamifiedPolys := function(d);
  //Computes polynomials (over k) which define all (at worst) tamely 
  //ramified extensions of k_v of degree d.
  //These will be plugged into TraceOfxminusT above
  // currently only for k_v = Q_p (though k may be of arbitrary degree),
  // or for d prime and k_v/Q_p unramified.
		
  polys := [  ];
  p := Characteristic(F_v);
  id := Ilog(p,#F_v);
  error if e_v gt 1, "Computation of tamely ramified extensions of k_v not implemented in this case: k_v/Q_p is ramified.\n";
  if id eq 1 then
    // k_v = Q_p
    Z_p := pAdicQuotientRing(p,2);
    for m in Divisors(d) do
      n := d div m;
      if n mod p ne 0 then
        // we construct extensions with ramification degree d/m = n
        R := ext< Z_p | m >;
	fR := Polynomial([ Rationals()! c : c in Coefficients(DefiningPolynomial(R))]);
        F_R,modw := ResidueClassField(R);
        zeta := PrimitiveElement(F_R)@@ modw;
        S := PolynomialRing(Rationals()); T := S.1;
        SS := PolynomialRing(S); TT := SS.1;
        exps := GCD(n,p^m -1);
        for s in [1..exps] do
          a_r := (zeta^s*p);
          a_rpol := &+[ Rationals()!(Eltseq(a_r)[i])*T^(i-1) : i in [1..#Eltseq(a_r)] ];
          polys cat:= [Resultant(Evaluate(fR,TT),(S.1-TT)^n+Evaluate(a_rpol,TT))];
        end for;
      end if; //n mod p ne 0
    end for;// m in Divisors(d)
    return polys;
  else
    error if not IsPrime(d), "Computation of tamely ramified extensions of k_v not implemented in this case: k_v/Q_p nontrivial and d composite.";
    // this leaves totally ramified and totally unramified cases
    unr := Polymodvtok(IrreduciblePolynomial(F_v,d));
    unr := Polynomial([ c mod v : c in Coefficients(unr) ]);
    polys cat:= [ unr ];
    // this takes care of the unramified case.
    if d mod p ne 0 then 
      //we have some tamely ramified extensions to compute
      zeta := PrimitiveElement(F_v)@@ modv;
      zeta := O_vtoO_k(zeta) mod v; // we only need it to precision 1 
      exps := GCD(d,p^d -1);
      for s in [1..exps] do
        polys cat:= [ kpol.1^d - zeta^s*p ];
      end for;
    end if;
    return polys;
  end if; // id eq 1
end function; // TamelyRamifiedPolys
		

LocalImageCk_v := function(d,f_global,k_v,ktok_v,k_vtok,mu_1,mu_2,q,im1,Foundim1,ImPic0);

  SpaceGenerated := ImPic0;
  // for C : y^q = f_global(x), f_global a poly over k with completion k_v
  // Computes the image of C(k_v) under mu = (x - T)
  // using mu_1 for x in O_v
  // using mu_2 for 1/x in O_v

  // implicit input: Foundim1, im1
  // we pass the degree of the extension under consideration as d.
  // for points on the Jacobian use mu(x) - d*im1

  nzs := [ c : c in Coefficients(f_global) | c ne 0 ];
  while &or[ IsWeaklyZero(ktok_v(c)) : c in nzs ] do
    k_v`DefaultPrecision +:= 5;
  end while;
  ppp1 := Max([ Valuation(ktok_v(c)) : c in Coefficients(f_global) | c ne 0 ]);
  k_v`DefaultPrecision := Max([k_v`DefaultPrecision,ppp1+1]);
  f := Polynomial([ k_v | ktok_v(c) : c in Coefficients(f_global) ]);
  extraval := 2*Valuation(k_v!q);
  //printf " 2*val(q) = %o.\n", extraval;
  lcf := LeadingCoefficient(f);
  k_v_stored_precision:= k_v`DefaultPrecision;
  while true do
    try
      ff := { g[1] : g in Factorization( f/lcf)};
      no_error:=true;
    catch ERR
      if IsFactorizationPrecisionError(ERR) then
        no_error:=false;
      else
        error ERR;
      end if;
    end try;
    if no_error then break; end if;
    k_v`DefaultPrecision +:= 10;
    vprintf Selmer, 3: "    Factorization requires: increasing precision to %o", k_v`DefaultPrecision;
    error if k_v`DefaultPrecision gt 100*k_v_stored_precision, "Precision problems while factoring.\n";;
  end while;
  ppp := Max( &cat[[ Valuation(c[1]) : c in Roots(g) | not IsWeaklyZero(c[1]) ] : g in ff] cat [ 1 ]);
  k_v`DefaultPrecision:=Max([k_v_stored_precision,ppp+extraval+1,ppp1 + extraval+1]);
  k_vpol := Parent(f);
  T := k_vpol.1;
  O_v := Integers(k_v);
  if GetVerbose("Selmer") ge 2 then
    AssignNames(~k_v,["r"]);
    U_v := BaseRing(k_v);
    if Degree(U_v) gt 1 then
      t := Parent(MinimalPolynomial(k_v.1)).1;
      s := Parent(MinimalPolynomial(U_v.1)).1;
      vprintf Selmer, 3: "        Working over Q_%o(u)(r), where\n",p;
      vprintf Selmer, 3: "          r is a root of %o\n", MinimalPolynomial(k_v.1);
      vprintf Selmer, 3: "          u is a root of %o.\n", MinimalPolynomial(U_v.1);
    else
      t := Parent(MinimalPolynomial(k_v.1)).1;
      vprintf Selmer, 3: "        Working over Q_%o(r), where\n",p;
      vprintf Selmer, 3: "          r is a root of %o\n", MinimalPolynomial(k_v.1);
    end if;
  end if;
  extralval := 2*Valuation(ktok_v(q));
  pi := UniformizingElement(k_v);
  PiO := UniformizingElement(O_v);
  piO_k := k_vtok(pi);
  F_v, modv := ResidueClassField(O_v);
  RepsForF_v := [ a@@modv : a in F_v ];
  valpoly := func< g | g eq 0 select Infinity() else Min([Valuation(c) : c in Coefficients(g)])>;
  if extraval gt 0 then
    //we precompute the q-th powers modulo pi^extraval 
    vprintf ConstantNeighborhoods, 1: "        Precomputing %o-th powers modulo pi^%o.", q,extraval+1;
    t0 := Cputime();
    v1 := Integers()!(extraval/2);			
    R<[b]> := PolynomialRing(Integers(q^2),extraval+1);
    RZ<[B]> := PolynomialRing(Integers(),extraval+1);
    RQ := PolynomialRing(Rationals(),extraval+1);
    RR := PolynomialRing(R); PI := RR.1;
    genericelt := &+[ b[i]*PI^(i-1) : i in [1..extraval+1] ];
    genericqp := genericelt^q;
    cs := Coefficients(genericqp);
    lowerhalf := [ RZ ! cs[i] : i in [1..v1+1] ];
    upperhalf := [ RZ ! (q*cs[i]) : i in [v1+2..extraval+1] ];
    upperhalf := [ RZ ! (1/q*(RQ ! gg)) : gg in upperhalf ];
    ms := Monomials(&+lowerhalf + &+upperhalf);
    ind := extraval;
    while [ Evaluate(r , [ B[i] : i in [1..ind] ] cat [ 0 : i in [ind + 1..extraval+1] ]) : r in ms ] eq ms do
      ind -:= 1;
    end while;
    ind +:= 1;
    PiO := UniformizingElement(O_v);
    Ove := quo< O_v | PiO^(extraval+1) >;
    R2<[a]> := PolynomialRing(Ove, ind);
    RR2 := PolynomialRing(R2); Pi := RR2.1;
    genqp := &+[ Evaluate(lowerhalf[j],a cat [ 0 : i in [ind + 1..extraval+1] ])*Pi^(j-1) : j in [1..ind] ];
    genqp +:= &+[ Evaluate(upperhalf[j],a cat [ 0 : i in [ind + 1..extraval+1] ])*Pi^(v1 + j) : j in [1..Min(ind,#upperhalf)] ];
    genpi := R2 ! Evaluate(genqp,Ove!PiO);
    repse := [ Ove ! r : r in RepsForF_v ];
    qthpowers := { Evaluate(genpi,Z) : Z in CartesianProduct([repse : i in [1..ind]]) };
    t1 := Cputime();
    vprintf ConstantNeighborhoods, 1: " Time: %o.\n", t1-t0;
  else
    qthpowers := { 0 }; // just so that its defined.
  end if;

  IsqthPowerOracle := function(e);
    // returns a function which given a in k_v decides if a is a q-th power mod Valuation(a) + e
    // compare with simple call IsPower(a,q)
    // no reason this should be any faster...?
    if extraval eq 0 then
      return func< a | IsPower(a,q)>;
    end if;
    if e eq 1 then
      if (#F_v - 1) mod q eq 0 then 
        oracle := function(a);
          // a in k_v
          if a eq 0 then return true; end if;
          val := Valuation(a);
          if val mod q ne 0 then return false; end if;
          ua := (O_v! (a/pi^(val)));
          return IsPower(modv(ua),q);
        end function;
      else
        oracle := func< a | true >;
      end if;
    else
      //e > 1 so we need to work in a residue Ring.
      //should only be needed for v | q
      O_ve := quo< O_v | PiO^e >;
      O_vE := Universe(qthpowers); // O_v mod pi^extraval
      qthpowerse := { O_ve ! O_v ! qp : qp in qthpowers };
      oracle := function(a);
        // a in k_v
        // if (O_ve ! a) eq 0 then return true; end if;
        val := Valuation(a);
        if val mod q ne 0 then return false; end if;
        ua := a/pi^(val);
        return (O_ve ! ua) in qthpowerse;
      end function;
    end if;
    return oracle;
  end function; // IsqthPowerOracle

  qporacles := [ IsqthPowerOracle(e) : e in [1..extraval + 1] ];
  ConditionToGoDeeper := function(fx1,v1,E1);
    // v1 = ord(fx1)
    // determines intersection of fx1 + pi^E1*O_v and (O_v)^q
    // verbosity explains the conditions.
    if E1 le v1 then 
      vprintf ConstantNeighborhoods, 2: " which contains q-th and non-qth powers.\n", E1,v1;
      return true;
    end if;
    s := Min({E1 - v1,extraval+1});
    isqthp := qporacles[s](fx1);
    if not isqthp then
      vprintf ConstantNeighborhoods, 2: " which is disjoint from O_v^q.\n";
    else
      if s eq extraval + 1 then
        vprintf ConstantNeighborhoods, 2: " subset (O_v)^q.\n";
      else
        vprintf ConstantNeighborhoods, 2: " which maps into (O_v/pi^%o)^q.\n",s;
      end if;
    end if;
    return isqthp;
  end function; //ConditionToGoDeeper
	
// k_v`DefaultPrecision := (extraval +1) + ??;
// 
// We need that the default precision remains at least
// as large as e in the recursive procedure below.
// (and this should be enough)
// 
// For the moment we just `hope' it is good enough.
//
k_v`DefaultPrecision := Max([ ppp + extraval+1 , ppp1 + extraval+1]);
pi := UniformizingElement(k_v);					
		
SetPrec := procedure(~k_v,~x0,~pi,nprec);
  k_v`DefaultPrecision := nprec;
  x0 := ktok_v( k_vtok( x0) );
  pi := UniformizingElement(k_v);
end procedure;
		
procedure qthPowerClasses(inf,f,x0,e,G0,c0,mu,~W,~im1,~Foundim1,~SpaceGenerated,~k_v,~pi);
		
  if e ge extraval then
    //We need to increase precision...
    if RelativePrecision(x0) + Valuation(x0) lt e + extraval then
      vprintf ConstantNeighborhoods, 2: "        Increasing precision to %o.\n", e+1;
      SetPrec(~k_v,~x0,~pi,e+1);
    end if;
  end if;

  if e ge 2 then
    assert RelativePrecision(x0) + Valuation(x0) ge e+1;
  end if;
  EXTRAGOS := 0; //used for safety and testing
  
  if (Ngens(SpaceGenerated) lt dimim) or Safety ge 1 or (not Foundim1 and d mod q ne 0) then
    //we are still looking for points...
    if Ngens(SpaceGenerated) ge dimim then
      EXTRAGOS +:= 1;
    end if;
    for r in RepsForF_v do
      // consider smaller nbhd of x0 + pi^(e-1)O_v
      c1 := c0;
      x1 := x0 + pi^e*r;
      fx1 := Evaluate(f,x1);
      sp := k_v`DefaultPrecision;
      ct := 0;
      while (RelativePrecision(fx1) lt (extraval +1)) do
        // if we enter this loop it is to ensure we handle the following case correctly
        //  x1 is given to sufficiently high precision that we know it is not a root of f (e gt ppp)
        //  f(x1) is still close to zero (IsWeaklyZero)
        SetPrec(~k_v,~x1,~pi,k_v`DefaultPrecision + 10);
        fx1 := Evaluate(f,x1);
        //  raise precision so that we see f(x1) ne 0.	
        // perhaps fx1 is zero?
        if Evaluate(Polynomial([k_vtok(c) : c in Coefficients(f) ]),k_vtok(x1)) eq 0 then
          break;
        end if;
        if Evaluate(f_global,k_vtok(x1)) eq 0 then
          break;
        end if;
        vprintf ConstantNeighborhoods, 1: " Relative precision of f(x1) too small... increasing to %o.\n",k_v`DefaultPrecision;
        ct +:= 1;
        if ct gt 6 and GetVerbose("ConstantNeighborhoods") le 0 then
          //you need to hear this...
          vprintf ConstantNeighborhoods, 0: " Relative precision of f(x1) too small... increasing to %o.\n",k_v`DefaultPrecision;
        end if;
        //printf "relp = %o\n extraval + 1 = %o.\n",RelativePrecision(fx1),extraval+1;
      end while;
      //Precision should be okay now...
      v1 := Valuation(fx1); 
      E1 := valpoly( Evaluate(f,x1+pi^(e+1)*T) - fx1);
      //printf " Evaluate(f,x1+pi^(e+1)*T) - fx1 = %o gives E1 = %o\n", Evaluate(f,x1+pi^(e+1)*T) - fx1,E1;
      if not inf then
        vprintf ConstantNeighborhoods, 2: "      For x in %o + pi^%o*O_v.\n",x1,e+1;
        vprintf ConstantNeighborhoods, 2: "        ==> f(x,1) in %o + pi^%o*O_v\n", fx1, E1;
      else
        vprintf ConstantNeighborhoods, 2: "      For z in %o + pi^%o*O_v.\n",x1,e+1;
        vprintf ConstantNeighborhoods, 2: "        ==> f(1,z) in %o + pi^%o*O_v\n", fx1, E1;
      end if;
      if ConditionToGoDeeper(fx1,v1,E1) then
        G1 := { g : g in G0 | valpoly( Evaluate(g,x1+pi^(e+1)*T)-Evaluate(g,x1)) le Valuation(Evaluate(g,x1)) };
        // printf " vals:\n";
        // [ valpoly( Evaluate(g,x1+pi^(e+1)*T)-Evaluate(g,x1)) : g in G0 ];
        // [ Valuation(Evaluate(g,x1)) : g in G0 ];
        if #G1 eq 0 or (#G1 eq 1 and #{ g : g in G1 | Degree(g) eq 1} eq 1) then
          if G1 ne G0 then
            c1 := extraval; //we need extraval more v-adic digits to ensure mu(x1) is proeprly determined.
          else
            c1 := c0 - 1; //we have specified another v-adic digit...
          end if;
          if c1 eq 0 then
            if #G1 eq 0 then
              vprintf ConstantNeighborhoods, 2: "         mu is constant.\n";
              impt := mu(x1);
              // we have found the image of this neighborhood
              // we just check if it is anyhting new:
              if d mod q ne 0 and not Foundim1 then
                Foundim1 := true;
                im1 := (Integers()! ((GF(q)!d)^(-1))) *impt;
                W := W join { impt };
                vprintf Selmer, 2: "      Found k_v-rational divisor of degree 1 .\n"; 
              else //
                if not impt in W then
                W := W join {impt};
                image := mu(x1) - d*im1;
                if not image in SpaceGenerated then
                  if not inf then
                    vprintf ConstantNeighborhoods, 1: "      For x in %o + pi^%o*O_v.\n",x1,e+1;
                    vprintf ConstantNeighborhoods, 1: "        ==> f(x,1) in %o + pi^%o*O_v\n", fx1, E1;
                    vprintf Selmer, 1: "        NEW GENERATOR: Image: %o.\n", Eltseq(image);
                  else
                    vprintf ConstantNeighborhoods, 1: "      For z in %o + pi^%o*O_v.\n",x1,e+1;
                    vprintf ConstantNeighborhoods, 1: "        ==> f(1,z) in %o + pi^%o*O_v\n", fx1, E1;
                    vprintf Selmer, 1: "        NEW GENERATOR: Image: %o.\n", Eltseq(image);
                  end if;
                  SpaceGenerated := sub< Avqmodk_v | Generators(SpaceGenerated) join {image}>;
                  error if Ngens(SpaceGenerated) gt dimim, "Found spurious point!";
                  if Ngens(SpaceGenerated) ge dimim and Foundim1 and Safety eq 0 then
                    break;
                  end if;
                end if; // not image in SpaceGenerated
              end if;	// not impt in W
            end if; // d mod q ne 0 and not Foundim1
          else
            vprintf ConstantNeighborhoods, 2: "         Image is torsion.\n";
          end if;
        else
          vprintf ConstantNeighborhoods, 2: "        higher precision needed to ensure mu is constant: %o.\n",c1;
          qthPowerClasses(inf,f,x1,e+1,G1,c1,mu,~W,~im1,~Foundim1,~SpaceGenerated,~k_v,~pi);
        end if;
      else
        //printf "G1 = %o.\nG0 = %o.\n", G1,G0;
        vprintf ConstantNeighborhoods, 2: "        higher precision needed to ensure mu is constant.\n";
        qthPowerClasses(inf,f,x1,e+1,G1,c1,mu,~W,~im1,~Foundim1,~SpaceGenerated,~k_v,~pi);
      end if; //#G1 eq 0 or (#G1 eq 1 and #{ g : g in G1 | Degree(g) eq 1} eq 1)
    end if; //ConditionToGoDeeper(fx1,v1,E1)
  end for; //r in RepsForF_v
end if; // Ngens lt SpaceGenerated etc.
end procedure; //qthPowerClasses

t0 := Cputime();
W := {};
// determines nbhds with x in O_v
qthPowerClasses(false,f,k_v!0,0,{ g : g in ff },-1,mu_1,~W,~im1,~Foundim1,~SpaceGenerated,~k_v,~pi);
W_inf := {};
// we also need nbhds with 1/x in O_v
// write d = m*q - s
s := (-Degree(f)) mod q;
if s in {0} then
  // change of vars: z = 1/x, w = y/x^m
  // y^q = f(x)  <===> w^q = z^s*SwapVar(f)(z)
  ftilde_global := SwapVar(f_global);
  if s gt 0 then
    ftilde_global *:= Parent(ftilde_global).1^s;
  end if;
  //? reset ppp???
  k_v`DefaultPrecision:=Max([k_v_stored_precision,ppp]);
  ftilde := Polynomial([ ktok_v(c) : c in Coefficients(ftilde_global)]);
  // factorization of ftilde over k_v
  fftilde := { SwapVar(g) : g in ff };
  fftilde := fftilde join { Universe(fftilde).1 };
  // we also include z even if s = 0 for two reasons:
  // 1) so the points with z = 0 are ignored by the procedure qthPowerClasses
  //	(since we can just compute these directly).
  // 2) we use (x - T) = (1/z - T) = z(1-zT), and the other polys in fftilde may only ensure (1-zT)
  //	 has constant q-th power class on the neighborhoods computed.
  vprintf ConstantNeighborhoods, 1: "      Computing neighborhoods above infty";
  vprintf ConstantNeighborhoods, 2: " using f_tilde = %o", ftilde;
  vprintf ConstantNeighborhoods, 1: ".\n";
  W_inf := {};
  qthPowerClasses(true,ftilde,k_v!0,1,fftilde,-1,mu_2,~W_inf,~im1,~Foundim1,~SpaceGenerated,~k_v,~pi);
else // s in {0}
  if liesaboveq then 
    //Homogenize as: F(x,z) = z^(dq) + z^(d*(q-1))*x + ... + z^q*x^(d-1) + x^d
    //  (x has weight q and z has weight 1)
    f1z_1 := (SwapVar(f_global));
    f1z := Evaluate(f1z_1,Parent(f1z_1).1^q);
    derz := Derivative(f1z);
    ppp2 := Max([ Valuation(ktok_v(c)) : c in Coefficients(f_global) cat Coefficients(derz) | c ne 0 ]);
    k_v`DefaultPrecision:=Max([k_v_stored_precision,ppp+1,ppp2+1]);
    f1zv := Polynomial([ ktok_v(c) : c in Coefficients(f1z)]);
    derzv := Polynomial([ ktok_v(c) : c in Coefficients(derz)]);
    //Find points (x:y:z) with z in pi*O_v
    //These map under (x-T) to 1 - th*z^q
    E := Ceiling(extraval/q+1); // = 2*val(q)/q
    //printf "E = %o.\n",E;
    //if val(z) gt E,    then 1 - th*z^q in O-v^*q
    //if val(z-z') gt E, then (x:y:z) and (x:y:z') have the same image under (x-T)
    RepsFormodpiE := CartesianProduct([RepsForF_v : i in [1..E-1]]);
    RepsFormodpiE2 := CartesianProduct([RepsForF_v : i in [1..E]]);
    RepsFormodpiE := [ &+[ k_vtok(k_v!a[i])*piO_k^i : i in [1..E-1] ] : a in RepsFormodpiE ];
    a1 := #RepsFormodpiE;
    RepsFormodpiE := [ a : a in RepsFormodpiE | not IsWeaklyZero(a) ];
    assert #RepsFormodpiE ne a1;
    RepsFormodpiE2 := [ &+[ k_vtok(k_v!a[i])*piO_k^(i-1) : i in [1..E] ] : a in RepsFormodpiE2 ];
    //Representatives in O_k for the classes in pi*O_v/pi^E*O_v.
    // we need to decide which neighborhoods contain z s.t. (1:*:z) lies on the curve.
    RepsForF_vInO_k := [ k_vtok(k_v!a) : a in RepsForF_v ];
	
    function ContainsPoints(e,Z,Y)
      // check if there is a point in z + pi^e*O where g takes value a q-th power
      for z in Z do
        z0 := z;
        for y in Y do
          y0 := y;
          //printf " Considering z= %o, y = %o.\n", z0,y0;
          n := Valuation(ktok_v(y0^q - Evaluate(f1z,z0)));
          m := Min([Valuation(ktok_v(Evaluate(derz,z0))), Valuation(ktok_v(q*y0^(q-1)))]);
          //printf " n = %o, m = %o.\n", n,m;
          if n gt 2*m and e le (n-m) then
            return true;
          else
            // check that g(z) ne 0.
            if n le 2*m and n ge 2*e then
              return ContainsPoints(e+1,[z0+a*piO_k^e : a in RepsForF_vInO_k],
                [y0+a*piO_k^e : a in RepsForF_vInO_k]);
            end if;
          end if;
        end for;
      end for;
      return false;
    end function; //ContainsPoints

    ttt1 := Cputime();
    //printf " Computing nbhds of infty SECOND way \n\n\n\n";
    //printf " RepsFormodpiE = %o.\n",RepsFormodpiE;	
    for z0 in RepsFormodpiE do
      impt := mu_2(z0);
      image := impt - d*im1;
      // we have found the image of this neighborhood
      // we just check if it is anyhting new:
      if not impt in W_inf then
        if not image in SpaceGenerated then
          if ContainsPoints(E,{z0}, RepsFormodpiE2) then
            // (1:*:z0) lies on the curve, so we add its image.
            W_inf := W_inf join { impt };
            vprintf Selmer, 2: "        NEW GENERATOR: For z in %o, f(1,z) in %o.\n", z0,"somewhere";
            vprintf Selmer, 2: "         Image: %o.\n", Eltseq(image);
            SpaceGenerated := sub< Avqmodk_v | Generators(SpaceGenerated) join {image}>;
            error if Ngens(SpaceGenerated) gt dimim, "Found spurious point!";
          end if;
        end if;
      end if;
    end for;
    ttt2 := Cputime();
    //printf " Computing nbhds of infty SECOND way took: %o secs\n", ttt2-ttt1;
  end if; //liesaboveq
end if; //s in {0}
return W join W_inf,im1,Foundim1,SpaceGenerated;
end function; //LocalImageCk_v


//printf "before doing anything: ImPic0 = %o, %o.\n", ImPic0, { Eltseq(a) : a in Generators(ImPic0) } ;
procedure ImagesOfExtensions(d,polys,~im1,~Foundim1,~ImPic0);
  // polys are polynomials defining degree d extensions K_w/k_v
  // Points in C(K_w) represent classes in Pic^d(C)
  // this procedure uses LocalImageCk_v() to compute the images 
  // of these classes.
  W_d := {};
  for h in polys do
    if Ngens(ImPic0) ge dimim and Safety eq 0 and Foundim1 then 
      vprintf Selmer, 1: "  Local image determined.\n";
      break; 
    end if;
    //vprintf Selmer, 1: "  Currently ImPic0 = %o %o.\n",ImPic0, { Eltseq(a) : a in Generators(ImPic0) };
    if d gt 1 then
      vprintf Selmer, 1: "      Looking for points over K_w = k_v(eta), where eta is a root of %o.\n", h;
    else
      vprintf Selmer, 1: "    Looking for points over k_v.\n";
    end if;		
    t0 := Cputime();
    kk := BaseRing(Parent(h));
    if Degree(kk) eq 1 then
      f_k := f;
      vv := p;
      kk_v,kktokk_v := Completion(kk,vv);
    else
      f_k := f;
      vv := v;
      kktokk_v := ktok_v;
    end if;
    f_K,K_w,KtoK_w,K_wtoK,mu1,mu2 := TraceOfxminusT(f_k,h,vv,kktokk_v);
    Mu1 := func< x | AtoLoc(Evaluate(mu1(x),A.1)) >;
    Mu2 := func< x | AtoLoc(Evaluate(mu2(x),A.1)) >;
    t1 := Cputime();
    vprintf Selmer, 2: "        Time to set up trace map: %o.\n", t1-t0;
    W_dh,im1,Foundim1,ImPic0 := LocalImageCk_v(d,f_K,K_w,KtoK_w,K_wtoK,Mu1,Mu2,q,im1,Foundim1,ImPic0);
    t2 := Cputime();
    W_d := W_d join W_dh;
    vprintf Selmer, 2: "        Time to compute constant neighborhoods: %o.\n", t2-t1;
    vprintf Selmer, 2: "        Total time: %o.\n", t2-t0;
    //vprintf Selmer, 1: "  Now ImPic0 = %o, %o.\n", ImPic0, { Eltseq(a) : a in Generators(ImPic0) };
  end for; // h in polys
end procedure; //ImagesOfExtensions

//First we compute C(k_v) (i.e. images of classes
// represented by divisors of degree 1)
ImagesOfExtensions(1,[kpol.1],~im1,~Foundim1,~ImPic0);
if not Foundim1 then
  vprintf Selmer, 1: "    Curve is not locally solvable.\n";
  if q ne 2 then MethodIsValid := false; end if;
  //The descent on PIC^1 is only proven to work if C is ELS
else
  vprintf Selmer, 2: "    Dimension of space generated by mu(C(k_v)) and torsion: %o.\n", Ngens(ImPic0);
end if;// not Foundim1
// Now search for divisors of higher degree
GuaranteedToFinish := false;

if liesaboveq and q in {2,3,5} and Degree(k) eq (q - 1) then
  // k is contained in the q-th cyclotomic field
  // we have precomputed all extensions of k_v of small degree
  if (q eq 2 and g le 7) or (q eq 3 and g le 5) or (q eq 5 and g le 4) then
    GuaranteedToFinish := true;
    // we have precomputed enough extensions of k_v to ensure that we compute the local image
  end if;						
  zeta_q := Roots(CyclotomicPolynomial(q),k)[1][1];
  Exts := RelativeExtensionsOfQ_pzeta_p(kpol,zeta_q);
  for d in [2..Min(7,g+1)] do 
    if Ngens(ImPic0) ge dimim and Safety eq 0 and Foundim1 then break; end if;
    Degdexts := [ g : g in Exts | Degree(g) eq d ];
    //if Ngens(ImPic0) ge dimim or #Degdexts eq 0 then break; end if;
    vprintf Selmer, 1: "    Searching for effective divisors of degree %o.\n", d;
    //printf " foundim1 ? %o.\n", Foundim1;
    ImagesOfExtensions(d,Degdexts,~im1,~Foundim1,~ImPic0);
    //printf " foundim1 ?? %o.\n", Foundim1;
  end for;
  error if dimim gt Ngens(ImPic0), "Failed to compute local image using precomputed extensions.";
else
  flag := false;
  for d in [2..g+1] do 
    // we want to compute images of points over extensions of degree d
    if Ngens(ImPic0) ge dimim and Safety eq 0 and Foundim1 then break; end if;
    if relDeg eq 1 and v in {3,5} then
      if v eq 3 then
        degreedextensions := [ h : h in AbsoluteExtensionsOfQ_3(k) | Degree(h) eq d ];
      else
        degreedextensions := [ h : h in AbsoluteExtensionsOfQ_5(k) | Degree(h) eq d ];;
      end if;
    elif relDeg eq 1 or IsPrime(d) then
      degreedextensions := TamelyRamifiedPolys(d);
    else
      flag := true;
    end if;
    //if Ngens(ImPic0) ge dimim or #Degdexts eq 0 then break; end if;
    vprintf Selmer, 1: "    Searching for effective divisors of degree %o.\n", d;
    //printf " foundim1 ? %o.\n", Foundim1;
    ImagesOfExtensions(d,degreedextensions,~im1,~Foundim1,~ImPic0);
    //printf " foundim1 ?? %o.\n", Foundim1;
  end for;
  if dimim gt Ngens(ImPic0) then
    if not (relDeg eq 1 or not flag) then
      printf "Failed to compute local image: Computation of tamely ramified extensions of k_v was not supported.\n";
    else	
      printf "Failed to compute local image: Tamely ramified extensions were not sufficient.\n Expected dimension was %o\n Only found dim = %o.\n",dimim, Ngens(ImPic0);
    end if;
  end if;
end if;

error if dimim gt Ngens(ImPic0), "Failed to compute local image.";
error if dimim lt Ngens(ImPic0), "Found spurious points!";
vprintf Selmer, 3: "  Local image of Pic^0 is %o.\n", ImPic0;

if Foundim1 then
  vprintf Selmer, 3: "  Local image of Pic^1 is the translate by %o.\n", im1;
end if;
//vprintf Selmer, 3: "  res_v( Kernel(Norm) ) = %o.\n", sub< Avqmodk_v | [ res_v(g) : g in Generators(ASqmodk)] >;
//vprintf Selmer, 3: "  Coset of norm 1/c maps to the translate by %o.\n", res_v(alpha_c);
//Now we want to find the preimages of ImPic0 and ImPic1p in ASqQ.
Avqmodk_vmodImPic0, modImPic0 := quo<Avqmodk_v|ImPic0>;
comp := hom<ASqmodk -> Avqmodk_vmodImPic0 | [ modImPic0(res_v(g)) : g in OrderedGenerators(ASqmodk) ] >;
if Foundim1 then
  ProperPrimeToq := true;
  d1 := im1;
else
  ProperPrimeToq := false;
  vprintf Selmer, 1: "  Could not find a divisor of degree prime to q.\n";
end if;

LC0 := Kernel(comp); // The subgroup of d in ASqmodk satisfying the local condition: res_v(d) in ImPic0
vprintf Selmer, 3: "  Local conditions on A(S,q)/k(S,q) cut out a space of dimension %o.\n",#Generators(LC0);
if ProperPrimeToq then	
  boo,preim := HasPreimage(modImPic0(d1-res_v(alpha_c)),comp);
  if boo then
    LC1 := < Kernel(comp),preim + alpha_c>;
    vprintf Selmer, 3: "  Pic1 coset is nonempty.\n";
  else
    LC1 := "empty";
    vprintf Selmer, 3: "  Pic1 coset is empty.\n";
  end if;
  //LC1 represents the coset of d in ASqmodk satisfying the local condition: res_v(d) in ImPic1
else	
  LC1 := "empty";
end if;
vprintf Selmer, 2: " Done with local computations at v = %o.\n\n",p;
return LC0,LC1;

end function; //LocalImages;


LocalImagesReals := function(pl);

  vprintf Selmer, 3 :"    Looking at %o.\n",pl;
  emb:=RealExtensions(A,pl);
  if # emb gt 0 then
    rts:=[e(A.1):e in emb];
    RH1:=AbelianGroup([2:i in rts]);
    AtoRH1:=map<A->RH1|
      a:->RH1![Real(cnj(a)) gt 0 select 0 else 1: cnj in emb]>;
    fR := Polynomial( [ emb[1](a) : a in Coefficients(f) ]);
    if #rts le 1 then
      eps := 1;
    else
      eps:=Minimum([Abs(rts[i]-rts[j]): i,j in [1..#rts] | i lt j])/1000;
    end if;
    if #rts eq 0 then
      Rimg:=sub<RH1|Identity(RH1)>;
      if Evaluate(fR,0) gt 0 then
        d1 := AtoRH1(-A.1); // Image of a real point under the descent map.
      else
        Pic1kEmpty := true;
        vprintf Selmer, 2: "     Curve has no real points.\n";
      end if;
    else
      if #rts eq 1 then
        L:=[[1]];
      else
        L:=[[ rt+eps gt r select 0 else 1 :r in rts]:rt in rts];
      end if;
      if Real(emb[1](A!lcf)) gt 0 then
        L:=[RH1!l: l in L| IsEven(#[c: c in l | c eq 1])];
      else
        L:=[RH1!l: l in L| IsOdd(#[c: c in l | c eq 1])];
      end if;
      if IsOdd(Degree(f)) then
        Append(~L,AtoRH1(lcf));
      end if;
      L:=[l-L[1]:l in L];
      if IsEven(Degree(f)) then
        Append(~L,RH1![1:i in [1..#rts]]);
      end if;
      pos := [ g + eps : g in rts | Evaluate(fR,g+eps) gt 0 ] cat [ g - eps : g in rts | Evaluate(fR,g-eps) gt 0];
      if #pos eq 0 then
        Pic1kEmpty := true;
        vprintf Selmer, 2: "     Curve has no real points.\n";
        // although there could be a real Weierstrass pt.
      else
        pre := Precision(Parent(rts[1]));
        approx := Floor(10^pre*pos[1])/10^pre; //rational approximation to rts[1]+eps
        d1 := AtoRH1(-A.1+A!approx); // Image of a real point under the descent map.
      end if;
      Rimg:=sub<RH1| [l:l in L]>;
    end if;
    LR2mRmodImJR,mR := quo< RH1 | Rimg >; 
    comp := hom<ASqmodk -> LR2mRmodImJR | [ mR(AtoRH1(g)) : g in repAs ] >;
    LC0R := Kernel(comp);
    vprintf Selmer, 3: "    Local conditions on A(S,q)/k(S,q) cut out a space of dimension %o.\n",#Generators(LC0R);
    boo,preim := HasPreimage(mR(d1) - comp(alpha_c),comp);
    if boo then
      LC1R := < Kernel(comp),preim + alpha_c>;
      vprintf Selmer, 3: "    Pic1 coset is nonempty.\n";
    else
      LC1R := "empty";
      vprintf Selmer, 3: "    Pic1 coset is empty.\n";
    end if;
    vprintf Selmer, 2: "  Done with local computations at p = infty.\n\n";
  else
    vprintf Selmer, 2: "  No real embeddings.\n";
    LC0R := ASqmodk;
    LC1R := <ASqmodk,alpha_c>;
  end if;
  return LC0R,LC1R;
end function; //LocalImagesReals

		
IntersectCosets := function(V,W);
  if Type(V) eq MonStgElt or Type(W) eq MonStgElt then
    return "empty";
  end if;
  V1 := V[1];
  v1 := V[2];
  V2 := W[1];
  v2 := W[2];
  // we want to find  ( V1 + v1 ) meet ( V2 + v2)
  VW,i1,i2 := DirectSum(V1,V2);
  p1 := Inverse(i1); p2 := Inverse(i2); 
  dif := hom< VW -> ASqmodk | [ -p1(VW.i) : i in [1..#Generators(V1)] ] cat [ p2(VW.i) : i in [#Generators(V1)+1..#Generators(VW)] ] >;
  if HasPreimage(v1-v2, dif) then
    alpha := v1 + p1((v1-v2) @@ dif);
    return <V1 meet V2,alpha>;
  else
    return "empty";
  end if;
end function; //IntersectCosets

SelfakeJ := Kernel(NASqmodktokq);
SelfakePic1 := <SelfakeJ,alpha_c>;
for v in S do
  LC0v,LC1v := LocalImages(v);
  SelfakeJ := SelfakeJ meet LC0v;
  currentdim := #Generators(SelfakeJ);
  vprintf Selmer, 2 : "  Bound for dimension of fake Selmer group is now %o.\n", currentdim;
  //vprintf Selmer, 3 : "  Lc1v = %o.\n", LC1v;
  //vprintf Selmer, 3 : "  So far, SelfakePic1 is contained in %o.\n", SelfakePic1;
  SelfakePic1 := IntersectCosets(SelfakePic1,LC1v);
  //vprintf Selmer, 3 : "  Intersection is %o.\n", SelfakePic1;
  if Type(SelfakePic1) eq MonStgElt and not Pic1kEmpty then
    vprintf Selmer, 2: "  Sel(Pic1) is empty.\n";
    Pic1kEmpty := true;
  end if;
end for;

if q eq 2 then
  vprintf Selmer, 2: "\n  Computing local image at real primes.\n";
  // code taken from Algaem/selmer.m
  for pl in [p: p in InfinitePlaces(k) | Type(p) eq Infty or IsReal(p)] do
    LC0R, LC1R := LocalImagesReals(pl);
    SelfakeJ := SelfakeJ meet LC0R;
    SelfakePic1 := IntersectCosets(SelfakePic1,LC1R);
  end for;
end if;

if Type(SelfakePic1) eq MonStgElt and MethodIsValid then
  SelfakePic1 := < SelfakeJ, {} >;
end if;
if Type(SelfakePic1) eq MonStgElt and not MethodIsValid then
  SelfakePic1 := < SelfakeJ, "?">;
end if;
//Ks,tt := AbsoluteAlgebra(A : Fields := { ext<QQ | f_i[1] > : f_i in factf } );
// Interpret data:

dimSel := NumberOfGenerators(SelfakeJ) + 1;
if Seltofakeinj then dimSel -:= 1; end if;
  vprintf Selmer, 1 : "\n\n%o-Selmer group has dimension %o.\n", q eq 2 select 2 else "phi", dimSel;
  if not flagphitorsglobal then
    vprintf Selmer, 1: "J(k)[%o] has dimension %o.\n", q eq 2 select 2 else "phi", ranktorsglobal;
  else
    vprintf Selmer, 1: "J(k)[%o] has dimension ge %o.\n", q eq 2 select 2 else "phi", ranktorsglobal;
  end if;
  if q eq 2 then
    // we get limited information on the 4 torsion
    vprintf Selmer, 2: "  Image of J(k)[%o] under the descent map has dimension ge %o.\n", q eq 2 select 2 else "phi", Ngens(muJktors);
    assert q eq 2;
    if ranktorsglobal - Ngens(muJktors) gt extratwotorsion then
      // there must be 4-torsion
      vprintf Selmer, 2: "    ==> J(k)[4] is nontrivial.\n";
    else
      if extratwotorsion eq 0 and ranktorsglobal eq Ngens(muJktors) then
        vprintf Selmer, 2: "    ==> 2J(k)[4] = 0.\n";
      end if;
    end if;
    if PrimeToqGlob or (g mod 2 eq 0 and CasGlob) then
      vprintf Selmer, 1: "Sel(Pic1) = Sel(J) = Sel_fake(J).\n";
      vprintf Selmer, 1: "    ==> Rank(J(k)) le %o.\n", dimSel-ranktorsglobal;
    else
      if Type(SelfakePic1[2]) eq Type({}) then
        vprintf Selmer, 1: "Sel(Pic1) is empty.\n";
        if MethodIsValid then
          //for this we need C to be ELS (which we check along the way).
          vprintf Selmer, 1: "    ==> Sha(J/k)[%o] has dimension ge 2.\n", q eq 2 select 2 else "phi";
          vprintf Selmer, 1: "    ==> Cassels kernel is trivial.\n";
          vprintf Selmer, 1: "    ==> Rank(J(k)) le %o.\n", dimSel-ranktorsglobal-2;
        end if;	
      else
        //Sel(Pic1) nonempty, Cassels kernel is nontrival
        vprintf Selmer, 1: "Sel(Pic1) nonempty and Cassels kernel is possibly nontrivial.\n";
	// e.g. if Pic1(k) nonempty then it is nontrivial
	vprintf Selmer, 1: "    ==> Rank(J(k)) le %o.\n", dimSel - ranktorsglobal;
      end if;
    end if;
  else
    if PrimeToqGlob or (g mod 2 eq 0 and CasGlob) then
      vprintf Selmer, 1: "Sel(Pic1) = Sel(J) = Sel_fake(J).\n";
      vprintf Selmer, 1: "    ==> Rank J(k(zeta_%o)) le %o.\n",q, (q-1)*( dimSel-ranktorsglobal);
      vprintf Selmer, 1: "    ==> Rank J(k) le %o.\n", (q-1)*( dimSel-ranktorsglobal)/(Degree(k)/Degree(k0));
    else
      if Type(SelfakePic1[2]) eq Type({}) then
        vprintf Selmer, 1: "Sel(Pic1) is empty.\n";
	if MethodIsValid then
	  //for this we need C to be ELS (which we check along the way).
          vprintf Selmer, 1: "    ==> Sha(J/k)[%o] has dimension ge 2.\n", q eq 2 select 2 else "phi";
          vprintf Selmer, 1: "    ==> Cassels kernel is trivial.\n";
          vprintf Selmer, 1: "    ==> Rank(J(k(zeta))) le %o.\n", (q-1)*( dimSel-ranktorsglobal-2);
          vprintf Selmer, 1: "    ==> Rank(J(k)) le %o.\n", (q-1)*( dimSel-ranktorsglobal-2)/(Degree(k)/Degree(k0));
        end if;	
     else
       //Sel(Pic1) nonempty, Cassels kernel is nontrival
       vprintf Selmer, 1: "Sel(Pic1) nonempty and Cassels kernel is possibly nontrivial.\n";
       // e.g. if Pic1(k) nonempty then it is nontrivial
       vprintf Selmer, 1: "    ==> Rank(J(k(zeta))) le %o.\n", (q-1)*( dimSel - ranktorsglobal);
       vprintf Selmer, 1: "    ==> Rank(J(k)) le %o.\n", (q-1)*( dimSel - ranktorsglobal)/(Degree(k)/Degree(k0));
     end if;
   end if;	
 end if;
 return dimSel, SelfakeJ, SelfakePic1, ranktorsglobal, ASqmodktoA, muJktors, toVec, FB ;

end intrinsic; //PicnDescents


intrinsic PhiSelmerGroup(f:: RngUPolElt, q :: RngIntElt : ReturnRawData := false) -> GrpAb, Map
{The (fake) phi-Selmer group of the Jacobian of the curve defined by y^q = f}
dimSel, SelfakeJ, SelfakePic1, ranktorsglobal, ASqmodktoA, muJktors, toVec, FB := PicnDescent(f,q);
if not ReturnRawData then
  return SelfakeJ, Inverse(ASqmodktoA);
else
  return SelfakeJ, Inverse(ASqmodktoA), toVec, FB, SelfakePic1[2];
end if;
end intrinsic;



/* For Testing:

intrinsic TestPicnDesc(N :: RngIntElt, q :: RngIntElt, d :: RngIntElt : ELS := false, sfty := 0) -> MonStgElt
{Tests PicnDescents on a random everywhere locally solvable hyperelliptic curve with coefficients le N.}
	
SetClassGroupBounds("GRH");

RandomHyp := function(N,d,q);
while true do
  coeffs := [ (-1)^Random(1)*Random(N) : i in [0..d-1] ];
  f := Polynomial(coeffs);
  f +:= Parent(f).1^d;
  f *:= (-1)^Random(1)*(Random(N)+1);
  ff := Factorization(f);
  if 2 in { a[2] : a in ff } then
  else
    break;
  end if;
end while;
return f;
end function;

f := PolynomialRing(Rationals())!  RandomHyp(N,d,q);

BP := BadPrimes(HyperellipticCurve(f)) cat [q];
pnels := [ p : p in BP | not HasIndexOne(f,q,p) ];

RR := RealField(100);
TestRealSolvability := function(f);  
  rts := [ r[1] : r in Roots(Polynomial([ RR! c : c in Coefficients(f)] ))];
  if #rts eq 0 then
    return Evaluate(f,0) ge 0;
  end if;
  return true;
end function;

if q eq 2 then
  tt := TestRealSolvability(f);
  if not tt then pnels cat:= [0]; end if;  
end if;

PIC1ELS := #pnels eq 0;
if #pnels mod 2 eq 1 and  q eq 2 and Genus(HyperellipticCurve(f)) mod 2 eq 0 then
  ShaIsOdd := true;
else
  ShaIsOdd := false;
end if;

PIC1ELS := PIC1ELS and TestRealSolvability(f);

//if XELS then
//  rp := RationalPoints(f,q : Bound := 1000);
//else
  rp := {};
//end if;
rr,SelJ,SelPic1,rtors := PicnDescent(f,q : Safety := sfty);
selrank := rr - rtors;

if PIC1ELS then
  if Type(SelPic1[2]) eq Type({}) then
    assert #rp eq 0;
    printf "SelPic1 is empty\n";
    selrank -:= 2;
  end if;
else
  printf "  X does not have index 1 everywhere locally.\n";
  assert Type(SelPic1[2]) eq Type({});
  if ShaIsOdd then
    "    J is odd.\n";
    selrank -:= 1;
  end if;
end if;

printf "selrank = %o.\n",selrank;

return rr,SelJ,SelPic1,rtors;
//determine algebraic rank?
end intrinsic;

*/








//
//
// selmer_aux.m
// brendan creutz
// Feb 2012 
//  
// Interface descent on Jacobians of cyclic covers with
// descent on Jacobians of hyperelliptic curves
//

// import "picndescent.m" : MonicModel;

declare attributes JacHyp: TwoSelmerSet;
// the 2-Selmer set of Pic^1(X)
declare attributes JacHyp: TwoSelmerRank;
// this is rank(J) + dim SHA(J)[2].
// Note: the 2-Selmer group has dimension equal to 
//       TwoSelmerRank + dim J(k)[2]


intrinsic TwoSelmerGroupNew(J::JacHyp : Raw := false, Fields := {}) -> GrpAb,Map
{Computes the 2-Selmer group of J}

if not assigned J`TwoSelmerGroup then
  J`TwoSelmerGroup := [**];
end if;
Data := [ d[1] : d in J`TwoSelmerGroup ];
Indx := Index(Data,"TwoSelmerGroupNew");
if Indx ne 0 then
  Sd := J`TwoSelmerGroup[Indx];
  if Raw then 
    return Sd[2],Sd[3],Sd[4],Sd[5];
  else
    return Sd[2],Sd[3];
  end if;
end if;


require BaseField(J) eq Rationals():
  "J must be defined over Q.";
X := Curve(J);

X := SimplifiedModel(X);
X := IntegralModel(X);
f := MonicModel(HyperellipticPolynomials(X),2);
vprintf Selmer, 1: " Model changed to y^2 = %o", f;

dimSel, SelFakeJ,SelFakePic1,ranktorsglobal,ASqmodktoA,muJktors,
  toVec, FB := PicnDescent(f,2 : Safety := 0, Fields := Fields);

AS2modk := Domain(ASqmodktoA);
AtoASqmodk := Inverse(ASqmodktoA);

J`TwoSelmerRank := dimSel - ranktorsglobal;

if dimSel gt Ngens(SelFakeJ) then 
  // Sel(J) --> Sel_fake(J) has kernel Z/2
  // (generated by PIC^1)
  Kerpr_1 := AbelianGroup([2]);
  Gb,m1,m2 := DirectSum(AS2modk,Kerpr_1);
  //Gb is the ambient of both Sel(J) and Sel(PIC1)
  SelJ := sub< Gb | [m1(g) : g in Generators(SelFakeJ) ] cat  [m2(Kerpr_1.1)] >;
  if Type(SelFakePic1[2]) ne SetEnum and Type(SelFakePic1[2]) ne MonStgElt then
    SelPIC := {m1(SelFakePic1[2])};
  else
    SelPIC := { };
  end if;
  // Sel(PIC) is the translate of SelJ by the element in SelPIC;
  // if SelPIC is empty, this means SelPIC is empty.
  AlgToGrp := AtoASqmodk*m1;

  cc := Components(ASqmodktoA);
  if #cc gt 1 then 
    //Degree(f) is even and we have modded out by scalars.
    //This means we need to deal with the Factor Basis slightly differently
    AS2modkToAS2 := Components(ASqmodktoA)[1];
    toVec2 := Inverse(m1)*AS2modkToAS2*toVec;
  else 
    toVec2 := Inverse(m1)*toVec;
  end if; //#cc gt 1

else // dimSel gt Ngens(SelFakeJ)
  // Sel(J) = Sel_fake
  SelJ := SelFakeJ;
  
  if Type(SelFakePic1[2]) ne SetEnum then
    SelPIC := {SelFakePic1[2]};
  else
    SelPIC :=  {};
  end if;

 // SelPIC := SelFakePic1[2];
  AlgToGrp := AtoASqmodk;
    cc := Components(ASqmodktoA);
  if #cc gt 1 then 
    //Degree(f) is even and we have modded out by scalars.
    //This means we need to deal with the Factor Basis slightly differently
    AS2modkToAS2 := Components(ASqmodktoA)[1];
    toVec2 := AS2modkToAS2*toVec;
  else 
    toVec2 := toVec;
  end if; //#cc gt 1

end if; // dimSel gt Ngens(SelFakeJ)

J`TwoSelmerSet := SelPIC;
Append(~J`TwoSelmerGroup, <"TwoSelmerGroupNew", SelJ, AlgToGrp, toVec2, FB> );

if Raw then 
  return SelJ,AlgToGrp,toVec2,FB;
else
  return SelJ,AlgToGrp;
end if;

end intrinsic;

