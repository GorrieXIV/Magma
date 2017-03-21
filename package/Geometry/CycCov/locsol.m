freeze;

////////////////////////////////////////////////////
// locsol.m                                       //
// Michael Mourao,                                //
// Nov. 2011                                      //
//                                                //
// intrinsics for testing local solubility of     //
// cyclic covers of P^1                           //
//                                                //
//                                                // 
//                                                //
////////////////////////////////////////////////////


// ++ Jan 2012 B.Creutz
// 
// added intrinsics for computing the index
// (i.e. checking if there are degree 1 divisors) 
// over local fields.
//
// ++ Feb 2012 B.Creutz
// ***EverywhereLocally now also checks over the Reals
// when q = 2.

import "localfieldsDB.m" : RelativeExtensionsOfQ_pzeta_p, 
  AbsoluteExtensionsOfQ_2, AbsoluteExtensionsOfQ_3,
  AbsoluteExtensionsOfQ_5;


HomogeneousEquation := function(f,q);
	K := BaseRing(Parent(f));
	R<X,Y,Z> := PolynomialRing(K,3);
	d := Degree(f);
	if d mod q eq 0 then 
		return Y^q - &+[ Z^(d-i)*X^(i)*Coefficient(f,i) : i in [0..d] ];
	else
		return Y^q - &+[ Z^(q*(d-i))*X^i*Coefficient(f,i) : i in [0..d] ];
	end if;
end function;

TestRealSolvability := function(f);
  RR := RealField();
  rts := [ r[1] : r in Roots(Polynomial([ RR! c : c in Coefficients(f)] ))];
  if #rts eq 0 then
    return Evaluate(f,0) ge 0;
  end if;
  return true;
end function;

zp_soluble:= function(reps,pi,FF,toFF,badprimes,K,q,coef,X,Y,X2,p,k)
   Kp,localmap:=Completion(K,p);
   RKp:=PolynomialRing(Kp);
   fp:=RKp![elt@localmap : elt in coef];
   /*if (((Integers()!Norm(p)-1) mod q) ne 0) and (not badprimes) then
      _,y0:=IsPower(Evaluate(fp,1),q);
      return true,[Kp!1,y0];
   else*/

      if (not badprimes) then	

         for x in X2 do
            x0:=x;
            fx0:=&+[coef[i]@toFF*x0^(i-1)  : i in [1..#coef]];
            ispower,y0:=IsPower(fx0,q);
            if ispower then
               return true,[x0@@toFF@localmap,y0@@toFF@localmap];
            end if;
         end for;
         return false,{};
      else
	      Rf:=PolynomialRing(Integers(K));
	      f:=Rf!coef;	
	      g:=Derivative(f);
         for x in X do
	         x0:=K!x;


            for y in Y do
               y0:=K!y;

               n:=Valuation((y0^q-Evaluate(f,x0)),p);
               m:=Min([Valuation(Evaluate(g,x0),p),Valuation((q*y0^(q-1)),p)]);

               if (k gt 0) and (n gt 2*m) and (k le (n-m)) then

                  return true,[x0@localmap,y0@localmap]; 
               else
                  if (k gt 0) and (n ge 500) then
	                  return true,[x0@localmap,y0@localmap];
                  else 
	                  if  (k eq 0) or ((n le 2*m) and (n ge 2*k)) then

                        lifts,lift:=$$(reps,pi,FF,toFF,badprimes,K,q,coef,[x0+a1*pi^k : a1 in reps],[y0+b1*pi^k : b1 in reps],X2,p,k+1);
			               if lifts then 
                           return true,lift;
			               end if;
	                  end if;
                  end if;
               end if;
            end for;
         end for;
	      return false,{};
      end if;
 //  end if;
	 return false, {};
					
end function;


local_solubility:=function(q,f,p)

   if Degree(f) mod q ne 0 then
     n := Integers()!( -(GF(q)!Degree(f))^-1 );
     c := LeadingCoefficient(f);
		 K := BaseRing(Parent(f));
		 Kp,ToKp:=Completion(K,p);
     return true, "", [ToKp(c)^n,ToKp(c)^(Integers()!( (Degree(f)*n+1)/q)),0];
   end if; //Degree(f) mod q ne 0


   if BaseRing(Parent(f)) eq Rationals() then
      K:=NumberField(PolynomialRing(Rationals()).1 -1 :DoLinearExtension:=true);
      R := PolynomialRing(K); x := R.1;
      f:=R!f;
      p:=ideal<Integers(K)|Generators(p)>;
   else
      R:=Parent(f);
      x:=R.1;
   end if; // BaseRing(Parent(f)) eq Rationals()
	 
   coef:=Eltseq(f);   
   K:=BaseRing(R);
   pi:=SafeUniformizer(p);

   badprimes:=(Valuation(q*Discriminant(f),p) ge 1);
   FF,toFF :=ResidueClassField(p);
   Kp,toKp := Completion(K,p);
   f_p := Polynomial([ toKp(c) : c in Coefficients(f) ]);
   Kp`DefaultPrecision +:= 10*Max([ Valuation(c) : c in Coefficients(f_p)]);
   

	
				
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
				
   Kp_stored_precision:= Kp`DefaultPrecision;
   while true do
    try
     ff:= [ g[1] : g in Factorization(f_p) ];
     no_error:=true;
    catch ERR
     if IsFactorizationPrecisionError(ERR) then
       no_error:=false;
     else
       error ERR;
     end if;
    end try;
    if no_error then
      break;
    end if;
    Kp`DefaultPrecision +:= 10;
    vprintf Selmer, 3: "    Finding roots for local solubility: increasing precision to %o", Kp`DefaultPrecision;
    if Kp`DefaultPrecision gt 5000 then
      error "Precision problems in factorization";
    end if;

  end while;
  Kp`DefaultPrecision:=Kp_stored_precision;

  lins := [ g : g in ff | Degree(g) eq 1 ];
  rts := [ Roots(g)[1][1] : g in lins ]; 

  if #rts gt 0 then
     return true, "", [ rts[1],Kp!0,Kp!1];
   end if;

	 // writing down reps takes way too long when p is big!
	 // we should find a better method...
        if Norm(p) gt 500 then
          // look for obvious random point
          tries := 0;
          while tries lt 30 do
            rd := toKp((-1)^Random(1)*Random(100)/(Random(100)+1));
            boo,y := IsPower(Evaluate(f_p,rd),q);
            if boo then
              return true, "(x,y)", [rd,y];
            end if;
            tries +:= 1;
          end while;
        end if;  

   reps:=[elt@@toFF : elt in FF];
   soluble,point:=zp_soluble(reps,pi,FF,toFF,badprimes,K,q,coef,reps,reps,FF,p,1);
   if soluble then
      return soluble,"(x,y)",point;
   end if;
   if (Degree(f) mod q) eq 0 then
      soluble,point:=zp_soluble(reps,pi,FF,toFF,badprimes,K,q,Reverse(coef),reps,reps,FF,p,1);
      if soluble then
         return soluble, "(z,y)",point;
      end if;
   else
      soluble,point:=zp_soluble(reps,pi,FF,toFF,badprimes,K,q,Reverse(Eltseq(Evaluate(f,x^q))),reps,reps,FF,p,1);
      if soluble then
         return soluble, "(z,y)",point;
      end if;
   end if; //(Degree(f) mod q) eq 
   return false, "", [];
   
   
end function;


intrinsic HasPoint(f :: RngUPolElt, q :: RngIntElt, v :: RngIntElt) -> BoolElt, SeqEnum
{Determines whether the cyclic cover defined by y^q = f(x) is locally solvable at the prime v}

error if not IsPrime(q), "Only implemented for cyclic covers of prime degree.";
error if not IsPrime(v), "v is not prime";

if q eq 2 then
  return IsLocallySolvable(HyperellipticCurve(f),v);
end if;

boo, str, pt := local_solubility(q,f,v);
if boo then
  if str eq "(x,y)" then
    return boo, pt cat [Universe(pt)!1];
  elif str eq "(z,y)" then 
    return boo, [Universe(pt)!1] cat Reverse(pt);
  elif str eq "" then
    return boo, pt;
  end if;
else
  return false, [];
end if;
end intrinsic;

intrinsic HasPoint(f :: RngUPolElt, q :: RngIntElt, v :: RngOrdIdl) -> BoolElt, SeqEnum
{}

error if not IsPrime(q), "Only implemented for cyclic covers of prime degree.";
error if not IsPrime(v), "v is not prime ideal of the integers of the base field.";

if q eq 2 then
  return IsLocallySolvable(HyperellipticCurve(f),v);
end if;

boo, str, pt := local_solubility(q,f,v);
if boo then
  if str eq "(x,y)" then
    return boo, pt cat [Universe(pt)!1];
  elif str eq "(z,y)" then 
    return boo, [Universe(pt)!1] cat Reverse(pt);
  elif str eq "" then
    return boo, pt;
  end if;
else
  return false, [];
end if;
end intrinsic;



intrinsic HasPointsEverywhereLocally(f :: RngUPolElt, q :: RngIntElt : PrimeBound := 0, BadPrimes := true) -> BoolElt, Set
{Determines whether the cyclic cover defined by y^q = f(x) is locally solvable at all primes of bad reduction and primes up to PrimeBound.}

for c in Coefficients(f) do
  error if not IsIntegral(c), "f must have integral coefficients.";
end for;

k := BaseRing(Parent(f));
if Type(k) eq FldRat then
  S := [ p[1] : p in Factorization(Integers()!(q*Discriminant(f))) ];
else
  O_k := Integers(k);
  S := Support(q*Discriminant(f)*O_k);
end if;

if q eq 2 then
  boo := TestRealSolvability(f);
  if not boo then
    return false;
  end if;
end if;

for v in S do
  vprintf Selmer, 2: "Testing local solubility at the prime v = %o.\n", v;
  boo, pt := HasPoint(f,q,v);
  if not boo then
    return false, {v};
  end if;
end for;

g := Degree(f) mod q eq 0 select Integers()!((Degree(f) - 2)*(q-1)/2) else Integers()!((Degree(f) - 1)*(q-1)/2);
if Type(k) eq FldRat then
  v := 2;
  while -2*g*v^(1/2)+1+v le 0 do
    if not v in S then
      vprintf Selmer, 2: "Testing local solubility at the prime v = %o.\n", v;
      boo, pt := HasPoint(f,q,v);
      if not boo then
        return false, {v};
      end if;
    end if;
    v := NextPrime(v);
  end while;
  return true,_;
else
  error if Type(BaseField(k)) ne FldRat, "f must be a polynomial over an absolute field.";
  p := 2;
  while -2*g*p^(1/2)+1+p le 0 do
  vs := [ Ideal(plc[1]) : plc in Decomposition(k,p) ];
  for v in vs do
    if -2*g*Norm(v)^(1/2)+1+Norm(v) le 0 and not v in S then
      vprintf Selmer, 2: "Testing local solubility at the prime v = %o.\n", v;
      boo, pt := HasPoint(f,q,v);
      if not boo then
        return false, {v};
      end if;
    end if; //-2*g*Norm(v)^(1/2)+1+Norm(v) le 0 and not v in S
  end for;// v in vs
  p := NextPrime(p);
  end while; //-2*g*p^(1/2)+1+p le 0
  return true, _;
end if; // Type(k) eq FldRat

end intrinsic;




//Functions for computing local index.

  TamelyRamifiedExts := function(k,v,d);
    kpol := PolynomialRing(k); x := kpol.1;
    //Computes polynomials (over k) which define all (at worst) tamely 
    //ramified extensions of k_v of degree d.
    //These will be plugged into TraceOfxminusT above

    // currently only for k_v = Q_p (though k may be of arbitrary degree),
    // or for d prime and k_v/Q_p unramified.
	
    polys := [  ];
    p := [ pp[1] : pp in Factorization(Norm(v))][1];
    if Degree(k) eq 1 then 
      id := 1;
      e_v := 1;
    else
      id := Degree(v);
      e_v := RamificationIndex(v);		
    end if;
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
        end if;
      end for;
      return polys;
    else
			
      error if not IsPrime(d), "Computation of tamely ramified extensions of k_v not implemented in this case: k_v/Q_p nontrivial and d composite.";
      F_v := FiniteField(p^id);
      k_v,tok_v := Completion(k,v);
      O_v := Integers(k_v);
      F_v,toF_v := ResidueClassField(O_v);
      O_k := Integers(k);
			
      // this leaves totally ramified and totally unramified cases
	
      unr := Polynomial([ O_k!(( k_v ! (c @@ toF_v)) @@ tok_v) :
         c in Coefficients(IrreduciblePolynomial(F_v,d))]);
      unr := Polynomial([ c mod v : c in Coefficients(unr) ]);
      polys cat:= [ unr ];
      // this takes care of the unramified case.

      if d mod p ne 0 then 
        //we have some tamely ramified extensions to compute
        zeta := PrimitiveElement(F_v)@@ toF_v;
        zeta := (O_k!( (k_v!zeta) @@ tok_v)) mod v;
        exps := GCD(d,p^d -1);
        for s in [1..exps] do
          polys cat:= [ kpol.1^d - zeta^s*p ];
        end for;
      end if;
      return polys;
		
    end if; // id eq 1
		
  end function; // TamelyRamifiedPolys


HasIndexOneAtv := function(f,q,v);
  
  genus := Integers() ! (Degree(f) - 2)*(q-1)/2;
  k := BaseRing(Parent(f));
  kpol := Parent(f);
  T := kpol.1;

  if not HasPoint(f,q,v) then
    vprintf CycCov, 2: "  Curve is not locally solvable at %o.\n  Checking extensions.\n", v;
    // check over extensions:
    if Degree(k) eq 1 then
      p := v;
    else
      p := [ pp[1] : pp in Factorization(Norm(v)) ][1];
    end if;
					 
    found := false;
    Exts := [];
    if p eq q and Degree(k) gt 1 then
      // v lies above q and k should be the q-th cyclotomic field.
      zeta_q := Roots(CyclotomicPolynomial(q),k)[1][1];
      Exts := RelativeExtensionsOfQ_pzeta_p(kpol,zeta_q);
    end if;
		
    if Degree(k) eq 1 and p eq 2 then
      Exts := AbsoluteExtensionsOfQ_2(kpol);
    end if;
 
    if Degree(k) eq 1 and p eq 3 then 
      Exts := AbsoluteExtensionsOfQ_3(k);
    end if;
		
    if Degree(k) eq 1 and p eq 5 then
      Exts := AbsoluteExtensionsOfQ_5(k);
    end if;
		 
    if #Exts eq 0 then
      Exts := [];
      for d in [ d : d in [1..((Integers()!(genus + 1) mod Integers()!q) eq 0
        select genus else genus+1)] | d mod q ne 0 ] do
        if IsPrime(d) then
          Exts cat:= TamelyRamifiedExts(k,v,d);
        end if;
      end for;
    end if; //#Exts eq 0

    for g in [ g : g in Exts | Degree(g) mod q ne 0 and Degree(g) le genus + 1] do
      vprintf CycCov, 2: "    Looking for points over extension dfined by %o.\n", g;
      L := ext<k | g>;
      Labs := AbsoluteField(L);
      abovev := { Ideal(pid[1]) : pid in Decomposition(Labs,p) };
      assert #abovev eq 1;
      if HasPoint(Polynomial([ Labs ! L ! c : c in Coefficients(f)]),q,Random(abovev)) then
        found := true;
        break;
      end if;
    end for; // g
		
    if not found then
      vprintf CycCov, 1: "No degree 1 divisors locally at %o.\n", v;
      return false;
    end if; 
  end if; // not HasPoint(f,q,v)
  return true;

end function; //HasIndexOneAtv



intrinsic HasIndexOne(f :: RngUPolElt, q :: RngIntElt, v :: RngIntElt) -> BoolElt
{}
  return HasIndexOneAtv(f,q,v);
end intrinsic;

intrinsic HasIndexOne(f :: RngUPolElt, q :: RngIntElt, v :: RngOrdIdl) -> BoolElt
{Determines whether the cyclic cover given by y^q = f(x) defined over number
field has a divisor of degree 1 over the completion at the prime v.}
  return HasIndexOneAtv(f,q,v);
end intrinsic;

intrinsic HasIndexOne(C :: CrvHyp, p :: RngOrdIdl) -> BoolElt
{}
  f := HyperellipticPolynomials(IntegralModel(SimplifiedModel(C)));
  return HasIndexOne(f,2,p);
end intrinsic;


intrinsic HasIndexOne(C :: CrvHyp, p :: RngIntElt) -> BoolElt
{Determines whether the curve C defined over a number field has a divisor 
of degree 1 defined over the completion at the prime p}
  f := HyperellipticPolynomials(IntegralModel(SimplifiedModel(C)));
  return HasIndexOne(f,2,p);
end intrinsic;


intrinsic HasIndexOneEverywhereLocally(f :: RngUPolElt, q :: RngIntElt) -> BoolElt
{Determines whether the cyclic cover given by y^q = f(x) defined over number
field has a divisor of degree over every nonarcimedian completion.}

  vprintf CycCov, 2: "Checking for divisors of degree 1 on the cyclic cover
  y^%o = %o \n  everywhere locally.\n",q,f; 

  k := BaseRing(Parent(f));
  // for now k = Q
  if Degree(f) mod q ne 0 then
    return true;
  end if;
  if exists{g : g in Factorization(f) | Degree(g[1]) mod q ne 0 } then
    return true;
  end if;

  if q eq 2 then 
    // check index over R
    boo := TestRealSolvability(f);
    if not boo then
      return false, 0;
    end if;
  end if;

  genus := Integers() ! (Degree(f) - 2)*(q-1)/2;

  if Degree(k) eq 1 then 
    BP := { p[1] : p in Factorization(Integers()!Discriminant(f)) } join {q};
  else
    BP := Support(q*Discriminant(f)*Integers(k));
  end if;

  vprintf CycCov, 2: " Set of primes ot be checked: %o.\n", BP;
  
    for v in BP do
      hasdiv := HasIndexOneAtv(f,q,v);
      if not hasdiv then
        return hasdiv;
      end if;
    end for;
    return true;

end intrinsic; //HasIndexOneEverywhereLocally
		  
intrinsic HasIndexOneEverywhereLocally(C :: CrvHyp) -> BoolElt
{Determines whether the curve C defined over a number field has 
rational divisors of degree 1 defined over every completion}
  f := HyperellipticPolynomials(IntegralModel(SimplifiedModel(C)));
  return HasIndexOneEverywhereLocally(f,2);
end intrinsic;
				 
