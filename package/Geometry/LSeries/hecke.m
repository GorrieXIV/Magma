
/* L-function of Hecke (grossen)characters */

freeze;

Z:=Integers();

function cyclo_comp(raw,P) C<i>:=ComplexField(P);
 if Type(Parent(raw)) eq RngInt then return 0; end if;
 m:=Modulus(Parent(raw)); r:=Integers()!raw;
  // zr:=r*(zm div m); return zetam^zr; probably Exp is just as fast
 return Exp(2*Pi(C)*i*(r/m)); end function;

function hecke_euler(psi,p : Precision:=GetPrecision(0.5),Integral:=false)
 deg:=Degree(Parent(psi)`NF); O:=Integers(Parent(psi)`NF);
 need:=2+Ilog(10,Floor(2^deg*p^(deg*0/2)));
 if Precision lt need then Precision:=need; end if;
 z := PolynomialRing(ComplexField(Precision)).1;
 res:=&*[1-cyclo_comp('@'(e[1],psi : Raw),Precision)*z^Degree(e[1]) :
	 e in Factorization(p*O)];
 if Integral then
  res:=Polynomial([Round(Real(x)) : x in Coefficients(res)]); end if;
 return res; end function;

function hecke_eulerK(psi,P : Precision:=GetPrecision(0.5),Integral:=false)
 z := PolynomialRing(ComplexField(Precision)).1;
 res:=1-cyclo_comp('@'(P,psi : Raw),Precision)*z^Degree(P);
 if Integral then
  res:=Polynomial([Round(Real(x)) : x in Coefficients(res)]); end if;
 return res; end function;

intrinsic EulerFactor
(psi::GrpHeckeElt,p::RngIntElt : Precision:=GetPrecision(0.5),Integral:=false)
-> RngUPolElt
{Given a Hecke character and a prime number, return the Euler factor}
 require IsPrime(p): "p must be prime";
 return hecke_euler(psi,p : Precision:=Precision,Integral:=Integral);
end intrinsic;

intrinsic EulerFactor
(psi::GrpHeckeElt,P::RngOrdIdl : Precision:=GetPrecision(0.5),Integral:=false)
-> RngUPolElt
{Given a Hecke character and a compatible prime ideal, return Euler factor}
 require IsPrime(P): "Ideal must be prime";
 require psi`Parent`NF eq FieldOfFractions(Order(P)):
 "Field for ideal and Hecke character must be the same";
 return hecke_eulerK(psi,P : Precision:=Precision,Integral:=Integral);
 end intrinsic;

intrinsic LSeries(psi::GrpHeckeElt : Precision:=0,Integral:=false) -> LSer
{ Returns the L-series for a Hecke character on ideals }
 require IsPrimitive(psi): "Hecke character must be primitive";
 H:=psi`Parent; K:=H`NF; C,ooC:=Conductor(psi); wt:=1; r,c:=Signature(K);
 if psi eq H.0 then return LSeries(K); end if;
 g:=[i in ooC select +1 else 0 : i in [1..r]] cat &cat[[0,1] : i in [1..c]];
 O:=IntegerRing(K); cond:=Norm(C)*Abs(Discriminant(O));
 prec:= Precision gt 0 select Precision else GetPrecision(0.5);
 if Order(psi) le 2 then Integral:=true; end if;
/*
  function f(p,d : Precision:=prec) deg:=Degree(Parent(psi)`NF);
   need:=2+Ilog(10,Floor(2^deg*p^(deg*0/2)));
   if Precision lt need then Precision:=need; end if;
   z := PolynomialRing(ComplexField(Precision)).1;
   res:=&*[1-cyclo_comp('@'(e[1],psi : Raw),Precision)*z^Degree(e[1]) :
	      e in Factorization(p*O)];
   if Integral then
    res:=Polynomial([Round(Real(x)) : x in Coefficients(res)]); end if;
   return res; end function;
*/
 function f(p,d : Precision:=prec)
  return hecke_euler(psi,p : Precision:=Precision,Integral:=Integral);
 end function;

 name:=<"L-function of Hecke character ",psi>;
 L:=LSeries(wt,g,cond,f : Name:=name,Parent:=psi,Precision:=prec);
 L`degreeK:=<1,K>; L`condK:=C;
 L`cffuncK:=
   function(P,d : Precision:=prec)
     z := PolynomialRing(ComplexField(Precision)).1;
     return 1-cyclo_comp('@'(P,psi : Raw),Precision)*z^Degree(P); end function;
 RP:=RealPlaces(K);
 L`hodgeK:=[<[0,0,i in g select 1 else 0],RP[i]> : i in [1..#RP]]
           cat [<[0,0,2],ip> : ip in InfinitePlaces(K) | not ip in RP];
 return L; end intrinsic;

intrinsic HodgeStructure(psi::GrpHeckeElt) -> HodgeStruc
{Given a Hecke character, return its Hodge structure (over Q)}
 r,c:=Signature(psi`Parent`NF); C,ooC:=Conductor(psi);
 g:=[i in ooC select +1 else 0 : i in [1..r]] cat &cat[[0,1] : i in [1..c]];
 return HodgeStructure(0,g); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(P1::GrossenChar,P2::GrossenChar)-> BoolElt
{Determines if the underlying data for two Grossencharacters is internally
 the same (could return false even when they are actually equivalent)}
 if Weight(P1) ne Weight(P2) then return false;end if;
 if P1`hecke ne P2`hecke then return false; end if;
 if P1`dirich ne P2`dirich then return false; end if;
 if Conductor(P1) ne Conductor(P2) then return false; end if;
 if P1`type ne P2`type then return false; end if; return true; end intrinsic;

function grossen_euler(GR,p : Precision:=GetPrecision(0.5),Integral:=false)
 K:=GR`hecke`Parent`NF; deg:=Degree(K); O:=IntegerRing(K);
 need:=2+Ilog(10,1+Floor(2^deg*p^(deg*Weight(GR)/2)));
 if Precision lt need then Precision:=need; end if;
 CPX := PolynomialRing(ComplexField(Precision)); z := CPX.1; res:=CPX!1;
 for e in Factorization(p*O) do ev:='@'(e[1],GR : Precision:=Precision);
  res*:=(1-ev*z^Degree(e[1])); end for;
 if Integral then
  res:=Polynomial([Round(Real(x)) : x in Coefficients(res)]); end if;
 return res; end function;

function grossen_eulerK(GR,P : Precision:=GetPrecision(0.5))
 C:=ComplexField(Precision); z := PolynomialRing(C).1;
 return 1-C!('@'(P,GR : Precision:=Precision))*z^Degree(P); end function;

intrinsic EulerFactor
(gr::GrossenChar,p::RngIntElt : Precision:=GetPrecision(0.5),Integral:=false)
-> RngUPolElt
{Given a Grossencharacter and a prime number, return the Euler factor}
 require IsPrime(p): "p must be prime";
 return grossen_euler(gr,p : Precision:=Precision,Integral:=Integral);
end intrinsic;

intrinsic EulerFactor
(gr::GrossenChar,P::RngOrdIdl : Precision:=GetPrecision(0.5)) -> RngUPolElt
{Given a Grossencharacter and a compatible prime ideal, return Euler factor}
 require IsPrime(P): "Ideal must be prime";
 require gr`hecke`Parent`NF eq FieldOfFractions(Order(P)):
 "Field for ideal and Grossencharacter must be the same";
 return grossen_eulerK(gr,P : Precision:=Precision); end intrinsic;

intrinsic LSeries(gr::GrossenChar : Precision:=0,Integral:=false) -> LSer
{ Returns the L-series for a Grossencharacter }
 b:=IsPrimitive(gr); require b: "Grossencharacter must be primitive";
 if not gr`field_is_cm then
  return Translate(LSeries(gr`hecke : Precision:=Precision),gr`wt); end if;
 G:=gr`hecke`Parent; K:=G`NF; C,ooC:=Conductor(gr);
 wt:=1+gr`wt; g:=[-Min(t[1],t[2]) : t in gr`type]; g cat:=[1+x : x in g];
 prec:= Precision gt 0 select Precision else GetPrecision(0.5);
 if &and[g[1] eq g[2] : g in gr`type] then
  return Translate(LSeries(gr`hecke*HeckeLift(gr`dirich) : Precision:=prec),
		   (wt-1)/2); end if;
 O:=IntegerRing(K); cond:=Norm(C)*Abs(Discriminant(O));
 if Order(gr`hecke) le 2 and Order(gr`dirich) le 2 and ClassNumber(K) eq 1
  and Min(&cat gr`type) ge 0 then b,u:=IsPrincipal(Modulus(gr`hecke));
  if b and IsCoercible(Integers(),u) then Integral:=true; end if; end if;  
 function f(p,d : Precision:=prec)
  return grossen_euler(gr,p : Precision:=Precision,Integral:=Integral);
 end function;
 nm:=<"L-function of ",gr>;
 L:=LSeries(wt,g,cond,f : Name:=nm,Parent:=gr,Precision:=prec);
 L`degreeK:=<1,K>; L`condK:=C;
 L`cffuncK:=
   function(P,d : Precision:=prec) C:=ComplexField(Precision);
    z := PolynomialRing(C).1;
    return 1-C!('@'(P,gr : Precision:=Precision))*z^Degree(P); end function;
 IP:=InfinitePlaces(K);
 L`hodgeK:=[<[gr`type[i][1],gr`type[i][2],2],IP[i]> : i in [1..#IP]];
 return L; end intrinsic;

intrinsic HodgeStructure(gr::GrossenChar) -> HodgeStruc
{Given a Grossencharacter, return its Hodge structure (over Q)}
 if not gr`field_is_cm then
  return TateTwist(HodgeStructure(gr`hecke),-gr`wt); end if;
 g:=[-Min(t[1],t[2]) : t in gr`type]; g cat:=[1+x : x in g];
 return HodgeStructure(gr`wt,g); end intrinsic;
