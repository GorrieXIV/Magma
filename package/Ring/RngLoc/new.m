freeze;

/////////////////////////////////////////////////////////////////////////////
// Automorphisms are in class_field.m now
/////////////////////////////////////////////////////////////////////////////
/*
*/
///////////////////////////////////////////////////////////////////////
// general functions
//////////////////////////////////////////////////////////////////////

intrinsic BaseRing(L::FldPad) -> FldPad
{The base field of L}
  return BaseField(L);
end intrinsic;


//---------------------------------------------------------------------
// FACTORIZATION
//---------------------------------------------------------------------

declare verbose RoundFour, 6;

///////////////////////////////////////////////////////////////////////
// some functions for polynomials that probably should be somewhere 
// else

intrinsic IsMonic(f::RngUPolElt) -> BoolElt
{Return true iff the polynomial f is monic}
    //return IsUnit(LeadingCoefficient(f));
    return not IsZero(f) and IsOne(LeadingCoefficient(f));
end intrinsic;

intrinsic ChineseRemainderTheorem(La::[RngUPolElt],Lm::[RngUPolElt]) -> RngUPolElt
{Computes a polynomial g such that g mod Lm[i] = La[i]}

  PR := Parent(Lm[1]);

  Mod := Lm[1];
  CR := La[1];

  for i := 2 to #Lm do
    g,c,d := XGCD(Mod,Lm[i]);
    assert g eq c*Mod + d*Lm[i];

    if g ne PR!1 then
      error "Error, ChineseRemainderTheorem: modules must be coprime.";
    end if;

    e2 := Mod*c;
    e1 := Lm[i]*d;

    Mod := Mod*Lm[i];
    CR := (e1*CR+e2*La[i]) mod Mod;
  end for;
  return CR;
end intrinsic;
//////////////////////////////////////////////////////
//

// Use C version!!
_gcd := function(f,g)
// only works for quotient rings.
//  if Degree(f) lt 0 or Degree(g) lt 0 then return Parent(f)!1,0; end if;
  ////////////////assert IsMonic(f) or IsMonic(g);
  
    return GcdWithLoss(f, g);
  PR := Parent(f);
  R := CoefficientRing(PR);
  pi := UniformizingElement(R);
  prec := Precision(R);
  S := SylvesterMatrix(f,g);
  H := EchelonForm(S); 
  L := Eltseq(H[Rank(H)]);
  h := PR!Reverse(L);
  loss := Integers()!Minimum([Valuation(a):a in Eltseq(h)]);
  h := (h div pi^loss);
  return h, loss;
end function;


///////////////////////////////////////////////////////

function is_squarefree(f) 

  if Degree(f) le 0 then
    return true, f, 0;
  end if;

  vprint RoundFour,4:" -- residue class field";
  _, mR := ResidueClassField(CoefficientRing(f));
  ff := Polynomial([mR(x) : x in Eltseq(f)]);
  if IsSquarefree(ff) then
    vprint RoundFour,3:" -- polynomial is squarefree over residue class field";
    return true, f, 0;
  end if;

  vprint RoundFour,4:" -- disc";
  vtime RoundFour,4:val :=  Valuation(Discriminant(f));
  if val lt Precision(BaseRing(Parent(f))) then
    vprint RoundFour,3:" -- polynomial is squarefree by discriminant";
    return true, f, 0;
  end if;

  df := Derivative(f);
  vprint  RoundFour,4: " -- gcd";
  vtime RoundFour,4: gcd, loss := _gcd(f,df);
  if Degree(gcd) lt 1 then
    vprint RoundFour,3:" -- polynomial is squarefree by gcd";
    return true, f, loss;  
  else
    return false, f div gcd, loss;
  end if;

end function;

//TODO ???
//intrinsic IsSquareFree(f::RngUPolElt[RngPadResExtElt])
//{return  
//  is_squarefree(f)

function build_coeff_seqs(coeffs)

    if Type(Universe(coeffs)) in {RngSerExt} then
	return [build_coeff_seqs(Eltseq(c)) : c in coeffs];
    end if;

    return [[0 : i in [1 .. Minimum(Valuation(c), Precision(Parent(c)))]] cat Eltseq(c) : c in coeffs];
end function;

function increase_precision(f, R)
// increase the precision of the coefficients of f so they have the full 
// precision of R and return as a polynomial over R
    if Type(R) in {RngPadRes, RngPadResExt, RngPad, FldPad} then
	return Polynomial(R, f);
    end if;

    coeffs := Coefficients(f);
    coeffs := build_coeff_seqs(coeffs);
    return Polynomial(R, ChangeUniverse(coeffs, R));
end function;

///////////////////////////////////////////////////////
// functions for handling polynomials with denominators

/////////////////////////////////////////////////////////////
// in the round four elements are represented by polynomials
// and the exponent of pi in the denomiantor
// we also store additional information in the structure

elt_reduce := procedure(~theta)
// 'cancels out' powers of the uniformizer pi in the polynomial
// and its denominator.
  if theta`elt eq 0 then
    theta`denval := 0;
  else
    minval := Integers()!Minimum([Valuation(a): a in Eltseq(theta`elt)]);
  //print minval;
    if minval gt 0 and theta`denval ge minval then 
      pi := UniformizingElement(CoefficientRing(Parent(theta`elt)));
      theta`elt := theta`elt div pi^minval;
      theta`denval := theta`denval - minval;
    end if;
  end if;
end procedure;

// constructor
elt := function(phi, denval)

    ELT :=    recformat
              <elt:RngUPolElt,       // the numerator of the element
               denval:RngIntElt,   // the denominator of elt is pi^den,
               chi:RngUPolElt,       // its characteristic polynomial
               passes_hensel_test,   // true if it passes the hensel test
               nu:RngUPolElt,        // irreducible factor of chi mod pi
               f:RngIntElt,         // deg(nu)
               res_fact,             // factorization of chi mod pi
               passes_newton_test,   // true if it passes the newton test
               v_star,               // v_star valuations of elt  
               e:RngIntElt          // numerator of vstar
              >;
    theta := rec<ELT|elt := phi, denval:= denval>;          
    elt_reduce(~theta); 
    return theta;
    
end function;

//////////////////////////////////////////////////

elt_inverse := function(theta, Phi)
// Find the inverse of some (invertible) element theta modulo Phi.
// the inverse is given as res/pi^denval
    pi := UniformizingElement(CoefficientRing(Parent(Phi)));        
    P := Parent(theta`elt);
    R := CoefficientRing(P);
    //print "inverse f g", f,g;
    M := SylvesterMatrix(theta`elt, Phi);
    //print "inverse M", M;
    E, T := EchelonForm(M);
    //print "inverse E T",E, T;
    //print "inverse",Eltseq(Submatrix(T, Nrows(T), 1,1,Degree(g)));
    res := (P ! Reverse(Eltseq(Submatrix(T, Nrows(T), 1,1,Degree(Phi))))) mod Phi;
    gcd := E[Nrows(E)][Ncols(E)];
    denval := Valuation(gcd);
    uni := gcd div pi^denval;
    //print "inverse gcd",gcd;
    res := res div uni;
    return elt(res,denval);
end function;

//////////////////////////////////////////////////

elt_add := function(theta, t2)
// Find the sum of some elements theta and t2
    pi := UniformizingElement(CoefficientRing(Parent(theta`elt)));        
    if theta`denval ne t2`denval then
      d := Maximum(theta`denval, t2`denval);
      s1 := d - theta`denval;
      s2 := d - t2`denval;
      s1 := pi^s1;
      s2 := pi^s2;
    else
      s1 := 1;
      s2 := 1;
      d := theta`denval;
    end if;
    return elt(theta`elt*s1 + t2`elt*s2, d);
end function;


//////////////////////////////////////////////////

v_star := function(f)
// compute the v_star valuation from a given characteristic polynomial f  
    assert IsMonic(f);
    coeffs := Reverse(Coefficients(f));
    //assert IsUnit(coeffs[1]);
    Remove(~coeffs, 1);
//"vstar",[Valuation(coeffs[i]) / i : i in [1..#coeffs]];
    res := Min(Min([Valuation(coeffs[i]) / i : i in [1..#coeffs]]), Precision(Universe(coeffs)));
//"vstar",res;
    return Rationals()!res;
end function;


////////////////////////////////////////////
// computation of characteristic polynomials

////////////////////////////////////////////////////////////////
// compute the characteristic polynomials using newton relations
// (cohen 1, p 161)
// the traces_from_poly of tyhe reference polynomials Phi are 
// precomputed and applied in th computation of char polys wrt
// Phi.        

traces_from_poly := function(Phi)
 
  n := Degree(Phi);
  R := CoefficientRing(Parent(Phi));
  
  // precision loss occurs in poly_from_traces by division
  if n gt 0 then
    inc := Maximum([Valuation(R!a):a in [1..n]]);
    inc := inc^2;
  else
    inc := 0;
  end if;
  //print "inc",inc;
  
  tmp_R := ChangePrecision(R,Precision(R)+inc);
  tmp_PR := PolynomialRing(tmp_R);
  tmp_Phi := tmp_PR!Phi;
  //tmp_Phi := increase_precision(Phi, tmp_R);
  
  t := function(i)
    if i lt 0 then
      return 0;
    else
      return Coefficient(tmp_Phi,i);
    end if;
  end function;
  
  S := [];

  for k := 1 to n do
    Sk := -k*t(n-k);
    for i := 1 to Minimum(n,k-1) do
      Sk := Sk - t(n-i)*S[k-i];
    end for;
    Append(~S,Sk);
  end for;
  return S;
end function;


poly_from_traces := function(S)

  n := #S;
  Tn := [];
  
  for k := 1 to n do
    Tnk := -S[k];
    for i := 1 to k-1 do
      Tnk := Tnk - Tn[i]*S[k-i];
    end for;
    //print Tnk;
    //print "mod", Tnk mod k;
    Tnk := Tnk div k;
    //print k,Tnk;
    Append(~Tn,Tnk);
  end for;
  Tn := Reverse(Tn);
  Append(~Tn,Parent(S[1])!1);
  return PolynomialRing(Parent(S[1]))!Tn;
  
end function;

oldchi := function(Phi,theta)
// The char poly of theta wrt Phi -- Kernel version
  PR := Parent(Phi);
  R := CoefficientRing(PR);
  //print "chi Phi", Phi;
  //print "chi theta",theta;
  
  if theta eq PR.1 then
    return Phi;
  end if;
 
  ML := [];
  seq := [ R!0 : a in [1..Degree(Phi)]];
  seq[1] := R!1;
  Append(~ML, seq);
  poly := theta mod Phi;


  for i in [1..Degree(Phi)] do
    //print i;
    if Degree(poly) lt Degree(Phi)-1 then
      seq := Eltseq(poly+PR.1^(Degree(Phi)-1));
      seq[Degree(Phi)] := seq[Degree(Phi)]-1;
    else  
      seq := Eltseq(poly);
    end if;
    seq := seq[1..Degree(Phi)];
    Append(~ML, seq);
    M := Matrix(Reverse(ML));
    //print "M",M;
    K := Kernel(M);
    //print "K",K;
    if #Basis(K) gt 0 then
      //print "K",K;
      res := PR![e : e in Reverse(Eltseq(Basis(K)[1]))];
      //print res;
      //print Degree(res);
      //print LeadingCoefficient(res);
      //print res;
      //if Degree(Phi) mod Degree(res) eq 0 then
         //print "res1",res;
        if IsUnit(LeadingCoefficient(res)) then
           res := res div LeadingCoefficient(res);
           //print "res2",res;
           //print "basislen",#Basis(K);
           //print K;
           //print "chi kernel",res;
           return res;
        end if;
      //end if;     
    end if;
    poly := poly*theta mod Phi;
  end for;
  error "chi";
end function;  


chi := function(Phi, traces_Phi, theta)
//"chi:theta",theta;

  n := Degree(Phi);
  assert n gt 0;

    if Characteristic(Universe(traces_Phi)) in [1 .. n] then
	return oldchi(Phi, theta);
    end if;

  tmp_PR := PolynomialRing(Universe(traces_Phi));
  tmp_theta := tmp_PR!theta;
  tmp_Phi := tmp_PR!Phi;

  S := [];

  pow := 1;
  for i := 1 to n do
    pow := pow*tmp_theta mod tmp_Phi;
    //print "pow",pow;
    Si := 0;
    Si := n*Coefficient(pow,0);
    for j := 1 to Degree(pow) do
      if Coefficient(pow,j) ne 0 then
        Si +:= traces_Phi[j]*Coefficient(pow,j);
      end if;
    end for;
    Append(~S,Si);
  end for;
  //print S;
  //return S;
  return Parent(Phi)!poly_from_traces(S);
end function;

elt_chi := function(Phi, traces_Phi, theta)
//{Find char poly of theta * pi^-theta_denval}
    vprint RoundFour,5:" -- char poly";
    vprint RoundFour,6:" -- of",theta`elt;
    vprint RoundFour,6:" -- with denominator pi ^",theta`denval;
    PR := Parent(Phi);
    R := CoefficientRing(Phi);
    tmp_R := ChangePrecision(R,Precision(R)+4*theta`denval*Degree(Phi));
    tmp_PR := PolynomialRing(tmp_R);
    vtime RoundFour,5: res := chi(Phi, traces_Phi, theta`elt);
    //"vstar",v_star(res);
    //"denval",theta`denval;
    if v_star(res) lt theta`denval then
      error "Factorization: Insufficient precision in characteristic polynomial computation";
    end if;
    res := tmp_PR!res;
    //res := increase_precision(res, tmp_R);
    pi := UniformizingElement(tmp_R);
    res := Evaluate(res, pi^theta`denval * tmp_PR.1);
    res div:= LeadingCoefficient(res);
    res := PR!res;
    assert IsMonic(res);
    return PR!res;
end function;

    
// compute invariants of elt
elt_invariants:= procedure(Phi, traces_Phi, ~phi)
  
  if not assigned phi`chi then
    phi`chi := elt_chi(Phi, traces_Phi, phi);
  end if;
  phi`v_star := v_star(phi`chi);
  phi`passes_newton_test := 
    phi`v_star eq Valuation(TrailingCoefficient(phi`chi)) / Degree(phi`chi);
  phi`e := Denominator(phi`v_star);
  if phi`passes_newton_test or phi`v_star eq 0 then
    if not true or not assigned phi`res_fact then
	K, m := ResidueClassField(CoefficientRing(Parent(phi`chi)));
	mm := hom<Parent(phi`chi) -> PolynomialRing(K) | m, PolynomialRing(K).1>;
	res_chi := mm(phi`chi);
	fact := Factorization(res_chi);
//phi`chi, res_chi, fact;
      phi`res_fact := fact;
    end if;
    phi`passes_hensel_test := #phi`res_fact eq 1;
    if phi`passes_hensel_test then
      phi`nu := Parent(phi`chi)!phi`res_fact[1][1];
      phi`f := Degree(phi`nu);
    end if;
  else 
    phi`passes_hensel_test := true;
  end if;

end procedure;

// ??? !!! TODO ft(k2,L[14][3]);

elt_evaluate := function(Phi, theta, tau)
// returns theta`elt(tau`elt/pi^tau`denval)/pi^theta`denval mod Phi
//"elt_evaluate";
//[<RelativePrecision(c), Valuation(c)> : c in Coefficients(Phi)];
  PR := Parent(Phi);
  R := CoefficientRing(PR);
  inc := Degree(theta`elt)*tau`denval;
  tmp_R := ChangePrecision(R,Precision(R)+inc);
  tmp_PR := PolynomialRing(tmp_R);
  pi := UniformizingElement(tmp_R);        
  tmp_Phi := tmp_PR!Phi;
  //tmp_Phi := increase_precision(Phi, tmp_R);
  tmp_theta := tmp_PR!theta`elt;
  //tmp_theta := increase_precision(theta`elt, tmp_R);
  tmp_tau := tmp_PR!tau`elt;
  //tmp_tau := increase_precision(tau`elt, tmp_R);
 
//print "theta", tmp_theta, theta`denval;
//print "tau",tmp_tau,tau`denval;
 
  res := tmp_theta*pi^inc;
  res := tmp_PR![Eltseq(res)[i] div pi^(tau`denval*(i-1))
                 : i in [1..(Degree(res)+1)]];
  res := Evaluate(res, tmp_tau) mod tmp_Phi;
  //print "res, res_denval",res, theta_denval+inc;
  res_denval := theta`denval+inc;
  //print "res",res,res_denval;
  return elt(PR!res, res_denval);
end function;


elt_evaluate_trans := function(Phi, traces_Phi, theta, tau)
// elt_evaluate
// and transfer invariants
// useful when changing reference polynomial
  res := elt_evaluate(Phi, theta, tau);
  if assigned theta`chi then
    res`chi := theta`chi;
  end if;
  if assigned theta`res_fact then
    res`res_fact := theta`res_fact;
  end if;
  elt_invariants(Phi, traces_Phi, ~res);
  return res;
end function;



//////////////////////////////////////////////////////////////////////////
//

calculate_exponents := function(pool, ceils, val, E)
// returns a list of exponents res such that
// v*(pi^res[1]*pool[1]^res[2]*...*pool[m]^res[m+1]) eq val
// where res[i]<ceils[i-1] (for i>=2) and 
// Denominator(val) | E
  res := [];
  rem_val := val;
  len := #pool;
  now := len;

  d := E;

  while now gt 0 do

    d := d/ceils[now];
    tmpval := rem_val * d;
    tmpool := pool[now] *d;
    mud := Denominator(tmpool);    
    rcr := ResidueClassRing(Integers()!mud);
    tmpval := tmpval * mud;
    tmpool := tmpool * mud;
    sol := Integers()!((rcr!tmpval)/(rcr!tmpool));

    rem_val := rem_val - sol * pool[now];    
    Append(~res, sol);

    now := now - 1;

  end while;

  Reverse(~res);
  Insert(~res,1,rem_val);
  
  //print "calculate_exponents: res",res;
  return res;
end function;


elt_with_v_star := function(Phi, P, P_v_star, S, E, vstar)
//{Returns an element poly, such that
// poly has v_star valuation vstar}
	exps := calculate_exponents(P_v_star, S, vstar, E);
        //print "exps",exps;
	poly_val := Integers() ! exps[1];
        //print "poly_val",poly_val;
	if #P ne 0 then
	    poly := &*[P[i] ^ exps[i + 1] : i in [1..#P]];
	else
	    poly := Parent(Phi)!1;
	end if;

        if poly_val gt 0 then 
          pi := UniformizingElement(CoefficientRing(Parent(Phi)));
          poly := poly*pi^poly_val;
          poly_val := 0;
        end if;
        return elt(poly, -poly_val);

end function;

//////////////////////////////////////////////////////////////////////////

hensel_lift_factorization_sub := function(Phi, theta)
// the denominator of theta is pi^theta`denval
// if theta`chi is not assigned or theta`denval gt 0 then chi_theta is computed

    PR := Parent(Phi);
    R := CoefficientRing(Parent(Phi));
    
//[RelativePrecision(c) : c in Coefficients(Phi)];
//theta`denval;
    tmp_R := ChangePrecision(R,Precision(R)+Degree(Phi)*(theta`denval));
    tmp_PR := PolynomialRing(tmp_R);
    K, m := ResidueClassField(tmp_R);
    P := PolynomialRing(K); x := P.1;
    pi := UniformizingElement(tmp_R);
    tmp_Phi := tmp_PR!Phi;
    //tmp_Phi := increase_precision(Phi, tmp_R);
    traces_tmp_Phi := traces_from_poly(tmp_Phi);
//elt_invariants(tmp_Phi, traces_tmp_Phi,~theta);   
//"theta",theta;    
    tmp_theta := theta;
//"tmp_theta",tmp_theta;
    if theta`denval ne 0 or not assigned theta`chi then
      tmp_theta`chi := elt_chi(tmp_Phi, traces_tmp_Phi, tmp_theta);
	if assigned theta`chi then
	    chi_diff := PR!tmp_theta`chi - theta`chi;
	    if chi_diff ne 0 and Min([Valuation(c) : c in Coefficients(chi_diff)]) le 0 then
	    error "Insufficient precision to calculate a reliable characteristic polynomial";
	    end if;
	end if;
    end if;
    if assigned theta`res_fact then
      tmp_theta`res_fact := theta`res_fact;
      //tmp_theta`res_fact := theta`res_fact;
    end if;
    elt_invariants(tmp_Phi, traces_tmp_Phi,~tmp_theta);
    facts := [tmp_PR!(P!a[1]^a[2]) : a in tmp_theta`res_fact];                     
    //print "facts",facts;
    mm := hom<Universe(facts) -> P | m, P.1>;
    facts := [mm(f) : f in facts];
//[RelativePrecision(c) : c in Coefficients(tmp_theta`chi)];
    lifted_facts := HenselLift(tmp_theta`chi, facts);
//print "lifted_facts",lifted_facts;
//print (&*lifted_facts),tmp_theta`chi;
    assert &and[RelativePrecision(c) eq 0: c in Coefficients((&*lifted_facts)-tmp_theta`chi)] or &and[RelativePrecision(c) eq 0: c in Coefficients(tmp_theta`chi - Polynomial(tmp_R, &*ChangeUniverse(lifted_facts, PolynomialRing(ChangePrecision(tmp_R, Infinity())))))]; 
    eval_facts := 
      [ elt_evaluate(tmp_Phi,elt(fact,0),tmp_theta) : fact in lifted_facts];
    //print ((&*eval_facts) mod tmp_Phi);// mod pi^Precision(R);
//print "eval_facts",[fact:fact in eval_facts];
    vprint  RoundFour,4: " -- gcd";
    vtime RoundFour,4: res := [_gcd(Phi,PR!fact`elt) : fact in eval_facts];
    return res; 
end function;


hensel_lift_factorization_chi2 := function(Phi, theta)
// the denominator of theta is pi^theta_denval
// if chi_theta eq 0 or theta_denval gt 0 then chi_theta is computed
 
    flag := 1;
 
    PR := Parent(Phi);
    R := CoefficientRing(Parent(Phi));

    original_Phi := Phi;
//"hensel_lift_factorization_chi2 before";
//[RelativePrecision(c) : c in Coefficients(Phi)];
//theta;
    
    vprint RoundFour,5:" == Hensel lifting to precision", Precision(R),"..."; 
    res := hensel_lift_factorization_sub (Phi, theta);
//"hensel_lift_factorization_chi2 after";
//[[RelativePrecision(c) : c in Coefficients(r)] : r in res];
    // if the precion was not sufficient, repeat this step with a higher 
    // precision.
    inc := 1; 
    while flag eq 1 and not 0 eq ((&*res)-PR!Phi) do
      //print inc;
      tmp_R := ChangePrecision(R,Precision(R)+4*Degree(Phi)*inc);
      vprint RoundFour,5:" == ... trying Hensel lift again, precision increased by",
                         4*Degree(Phi)*inc,"...";
      tmp_PR := PolynomialRing(tmp_R);    
      tmp_theta := elt(tmp_PR!theta`elt, theta`denval);
      //tmp_theta := elt(increase_precision(theta`elt, tmp_R), theta`denval);
	ete := Eltseq(theta`elt);
	eete := [tmp_R!Eltseq(c) : c in ete];
	eete := [(Valuation(ete[i]) eq Infinity() or RelativePrecision(ete[i]) eq 0) select 0 else tmp_R.1^(Valuation(ete[i]) - Valuation(eete[i]))*eete[i] : i in [1 .. #eete]];
	assert &and[(RelativePrecision(ete[i]) eq 0 and RelativePrecision(eete[i]) eq 0) or Valuation(ete[i]) eq Valuation(eete[i]) : i in [1 .. #ete]];
      tmp_theta := elt(tmp_PR!eete, theta`denval);
      if assigned theta`res_fact then
        tmp_theta`res_fact := theta`res_fact;
      end if;
      //res := [PR!poly : poly in hensel_lift_factorization_sub
             //(tmp_PR!Phi, tmp_theta)];
	ephi := Eltseq(Phi);
	eephi := [tmp_R!Eltseq(c) : c in ephi];
	eephi := [(Valuation(ephi[i]) eq Infinity() or RelativePrecision(ephi[i]) eq 0) select 0 else tmp_R.1^(Valuation(ephi[i]) - Valuation(eephi[i]))*eephi[i] : i in [1 .. #eephi]];
	assert &and[RelativePrecision(R!ephi[i] - R!eephi[i]) eq 0 : i in [1 .. #ephi]];

	Phi := tmp_PR!eephi;
      //Phi := tmp_PR![Valuation(c) eq Infinity() select 0 else tmp_R.1^(Valuation(c) - Valuation(Parent(c)!Eltseq(c)[1]))*tmp_R!Eltseq(c) : c in Eltseq(Phi)];
      res := [PR!poly : poly in hensel_lift_factorization_sub(Phi, tmp_theta)]; 
      inc +:= 1;
    end while;
    vtime RoundFour,4: res := [_gcd(original_Phi,fact) : fact in res];
    vprint RoundFour,5:" == ... done"; 
    return res; 
end function;


newton_lift_factorization_chi2 := function(Phi, theta)
  //print "newton theta",theta,theta_denval;
 
//"theta",theta;  
  if theta`v_star eq 0 and not theta`passes_hensel_test then
    //print "newton_lift_factorization_chi2 hensel";
    return hensel_lift_factorization_chi2(Phi, theta);
  end if;
  
  rs := theta`v_star;
  vprint RoundFour,5:" == flattening Newton polygon slope from",rs,"to 0"; 
  gamma := elt(Parent(Phi)!(theta`elt^Denominator(rs)) mod Phi,
               Numerator(rs)+theta`denval*Denominator(rs));
  return hensel_lift_factorization_chi2(Phi, gamma);

end function;

/////////////////////////////////////////////////////////////////////////////////

res_field_rep := function (Phi, traces_Phi, nu, gamma)
//{Find a polynomial delta with Degree(delta)<Degree(nu_phi) 
// and v_star(delta-gamma)>0}
// returns:
// true, delta, xxx  
//   if such an element delta has been found
// false, xxx, rho
//   if during the search for delta an element that fails the 
//   hensel test has occured.

   if Degree(gamma`nu) eq 1 then
     return true, -TrailingCoefficient(gamma`nu), 0;
   end if;    

   if gamma`denval eq 0 then
     return true, gamma mod nu, 0;
   end if; 
    
   pi := UniformizingElement(CoefficientRing(Parent(Phi)));
   K, m := ResidueClassField(CoefficientRing(Parent(Phi)));
   P := PolynomialRing(K); x := P.1;
   mm := hom<Parent(nu) -> P | m, x>;
   nur := mm(nu);
   F := ext<K|nur>;
   PF:= PolynomialRing(F);
   facts := Roots(PF!(mm(gamma`nu)));
   for fact in facts do  
     a := Eltseq(fact[1]);
     b := PF!a;
     delta := Parent(Phi)!b;
     rho := elt(gamma`elt-pi^gamma`denval*delta,gamma`denval);
     elt_invariants(Phi, traces_Phi, ~rho);
     if not rho`passes_hensel_test then
       return false, 0, rho;
     end if;
     if rho`v_star gt 0 then
       return true, delta, 0;
     end if;
   end for;
   error "Factorization: Round Four Panic, no representing element found.";
end function;
    

ff_composition_gen := function(Phi, x, F_x, gamma)
// x gives a residue class field extension of degree F_x
// gamma/pi^gamma_denval gives a residue class field extension of 
// degree F_gamma
// find a poltynomial that gives a residue class field extension of
// degree LCM(F_x,F_gamma)
  //print "kappa",kappa,"/",pi^kappa_denval;  
  
  if gamma`f eq LCM(F_x,gamma`f) then
    kappa := gamma;
    return kappa;
  end if;
  
  //print "gamma",gamma;
  PR := Parent(Phi);
  R := CoefficientRing(Parent(Phi));
  denval := gamma`denval*gamma`f;
  tmp_R := ChangePrecision(R,Precision(R)+denval);
  //tmp_R := pAdicQuotientRing(Prime(R),Precision(R)+denval);
  tmp_PR := PolynomialRing(tmp_R); x := tmp_PR.1;
  pi := UniformizingElement(tmp_R);        
  tmp_Phi := tmp_PR!Phi;
  //tmp_Phi := increase_precision(Phi, tmp_R);
  traces_tmp_Phi := traces_from_poly(tmp_Phi);
  tmp_gamma := tmp_PR!gamma`elt;
  //tmp_gamma := increase_precision(gamma`elt, tmp_R);

  K := ResidueClassField(tmp_R);
  
  F := LCM(F_x,gamma`f);
  
  pow := [ (pi^(denval)*x^(i-1)) mod (pi^denval*tmp_Phi): i in [1..F_x]];
  pow := pow cat [ pi^(denval-(gamma`denval*(i-1)))*tmp_gamma^(i-1) 
                    mod (pi^denval*tmp_Phi) : i in [1..gamma`f]];

  repeat
    coeff := [tmp_R!Random(K) : i in [1..#pow]];
    //"coeff",coeff;    
    kappa := elt((&+ [coeff[i]*pow[i] : i in [1..#pow]]) mod tmp_Phi,denval);
    elt_invariants(tmp_Phi, traces_tmp_Phi,~kappa);
  until assigned kappa`f and kappa`f eq F;
 
  kappa`elt := PR!kappa`elt;
  
  return kappa;

end function;


//////////////////////////////////////////////////////////////////////////

forward round_four;

further_factorization := function(factors, with_certificates)

  L := [];
  for fact in factors do
    for cert in round_four(fact, with_certificates) do
      Append(~L,cert);
    end for;
  end for;
  return L;
end function;

////////////////////////////////////////////////////////////////////////

    FACTOR := recformat 
              <factor:RngUPolElt, 
               multiplicity:RngIntElt, 
               F:RngIntElt,              // inertia deg
               Gamma:RngUPolElt,          // unramified
               Gamma_denval:RngIntElt,   // certificate
               E:RngIntElt,              // ram index
               Pi:RngUPolElt,             // ramified 
               Pi_denval:RngIntElt,      // certificate
               IdealGen1,                 // two element representation
               IdealGen2                  // of the prime ideal
              >;
 
//-------------------------
round_four := function(Phi, with_certificates)
//-------------------------
// the algorithm used is a hybrid between 
// pauli: factoring polynomials over local fields   
// and 
// ford-pauli-roblot: a fast algorithm for factoring polynomials over Qp
//  
// step g) [extend the ground field] in the pauli algorithm is replaced by 
// by the combination of step 12 in algorithm 5.1 and step 2,3 in 5.2 in 
// ford-pauli-roblot
//
// if certificates is false the information needed for the certificates is not
// computed

    vprint RoundFour,1:"R4: factoring Phi with deg(Phi) =",Degree(Phi);   
    vprint RoundFour,3:"R4: Phi =",Phi;   
    
    PR := Parent(Phi);
    K := CoefficientRing(PR);
    pi := UniformizingElement(K);
    
    vprint RoundFour,4:"R4: over",K;   
    
    if Degree(Phi) eq 0 then
	return [];
    end if;

    if Degree(Phi) eq 1 then
      //print "done";
      return [rec<FACTOR| factor := Phi, multiplicity := 1,
                         F:=1, Gamma := PR!1, Gamma_denval := 0,
                         E:=1, Pi := PR!pi, Pi_denval := 0>];
    end if;

    
    Phihat := Phi;
    traces_Phi := traces_from_poly(Phi);
    traces_Phihat := traces_Phi;
    //////////////////////////// RAMIFIED DATA
    P := [];                  // list of polynomials that allows 
                              // construction of polynomials with 
                              // v_star valuation with den up to E
    S := [];                  // list of maximal exponents to be used 
                              // for the polynomials in P
    P_v_star := [];           // list of v_star valuations of the elements 
                              // of P
    E := 1;                   // highest known ramification index
    phi_old_v_star := 0;      // old v* valuation of phi, used to check
                              // that valuation of phi increases
    ////////////////////////////
    BETA := elt(PR.1,0);      // we record the change of the reference 
                              // polynomial Phihat in BETA/pi^BETA_denval
    ////////////////////////////
    
    phi := elt(PR.1,0); phi`chi := Phihat; 
    elt_invariants(Phihat, traces_Phihat, ~phi);
    if not phi`passes_newton_test or not phi`passes_hensel_test then
        vprint RoundFour,1:"R4: x fails Newton or Hensel test -- factoring";
        return further_factorization(newton_lift_factorization_chi2
               (Phi, phi), with_certificates);
    end if;
    
    ///////////////////// UNRAMIFIED DATA
    F     := phi`f;    // highest known inertia degree
    kappa := phi;      // generator of the unramified extension of degree F 
    nu    := kappa`nu; // generating polynomial of the unramified 
    ///////////////////// extension of degree F
    
    phi   := elt(phi`nu,0); elt_invariants(Phihat, traces_Phihat,~phi);               
    
    vprint RoundFour,1:"R4: initializing E to",E,"and F to",F;
    vprint RoundFour,3:"R4: inertia element:",BETA`elt;
    
    if F eq Degree(Phi) then
      vprint RoundFour,1:"R4: F =",F,"= deg(Phi)  =>  Phi is irreducible";    
      //vprint RoundFour,1:"R4: computing 2 element certificate";
      return [rec<FACTOR| factor := Phi, multiplicity := 1, 
                         F:=F, Gamma := PR.1, Gamma_denval := 0,
                         E:=1, Pi := PR!pi, Pi_denval := 0>];
    end if;
    
    //print "nu_phi",nu_phi;

   
    // main loop
    while true do
        vprint RoundFour,2:"R4| phi =",phi`elt; 
        vprint RoundFour,1:"R4| deg(phi) =", Degree(phi`elt),"and v*(phi) =", phi`v_star;
        vprint RoundFour,2:"R4| E =",E,"and F =",F; 
        /* Step a ***************************************************************/
        if not phi`v_star gt phi_old_v_star then
          error "Factorization: Insufficient precision in Round Four main loop";
        end if;
        if not Degree(phi`elt) le E*F then
          error "Factorization: Degree of phi too large in Round Four main loop";
        end if;
	
        if not phi`passes_newton_test then
	    vprint RoundFour,1:"R4a phi fails Newton test -- factoring";
            theta := elt_evaluate_trans(Phi,traces_Phi,phi,BETA); 
	    return further_factorization(newton_lift_factorization_chi2
                              (Phi, theta),with_certificates);
	    vprint RoundFour,4:"R4a phi passes Newton test";
	end if;

	/* Step b [increase E] **************************************************/
        if E mod phi`e ne 0 then
	    Append(~P, phi`elt);
	    Append(~P_v_star, v_star(chi(Phihat, traces_Phihat, phi`elt)));
	    s := LCM(E, phi`e) div E;
	    Append(~S, s);
            vprint RoundFour,1:"R4b increasing E from",E,"to",s*E;
            vprint RoundFour,4:"R4b list of polynomials giving ramification",P;
            vprint RoundFour,4:"R4b with v* valuations",P_v_star;
            vprint RoundFour,4:"R4b and maximal exponents",S;
	    E := s * E;
	    
            if E*F eq Degree(Phihat) then // Phi is irreducible
              vprint RoundFour,1:"R4b E * F =",E,"*",F,"= deg(Phi) =",Degree(Phihat),
                                 "  =>   Phi is irreducible";    
              if with_certificates then
                vprint RoundFour,1:"R4b computing 2 element certificate";
                //vprint RoundFour,5:"R4b computing ramified certificate";
                Pi := elt_with_v_star(Phihat, P, P_v_star, S, E, 1/E);                
                Pi := elt_evaluate(Phi, Pi, BETA);
                elt_invariants(Phi, traces_Phi, ~Pi);
                if Pi`v_star ne 1/E then
                  error "Factorization: Insufficient precision in computation of ramified certificate";
                end if;
                //vprint RoundFour,5:"R4b computing unramified certificate";
                if F eq 1 then
                  Gamma := elt(Parent(Phi)!1,0);
                else
                  Gamma := BETA;
                end if;
                elt_invariants(Phi, traces_Phi, ~Gamma);
                //print "F",F;
                if Gamma`f ne F then
                  error "Factorization: Insufficient precision in computation of unramified certificate";
                end if;
                return [rec<FACTOR| factor := Phi, multiplicity := 1, 
                                   F:=F, Gamma := Gamma`elt, 
                                   Gamma_denval := Gamma`denval,
                                   E:=E, Pi := Pi`elt,
                                   Pi_denval := Pi`denval>];
              else // no certificates
                return [rec<FACTOR| factor := Phi, multiplicity := 1, F:=F, E:=E>];
              end if;
            
            else // continue in main loop
                 // increase valuation of phi, such that deg(phi)=E*F
              phis := elt(phi`elt^s,0); phis`v_star := s*phi`v_star;
              phi := phis;
              vprint RoundFour,2:"R4b phi =",phi`elt; 
              vprint RoundFour,1:"R4b deg(phi) =", Degree(phi`elt),
                                 "and v*(phi) =", phi`v_star;
            end if;
	end if;

	/* Step c **************************************************************/
        vprint RoundFour,5:"R4c find psi with v*(psi) = v*(phi) =",phi`v_star;
        poly := elt_with_v_star(Phi, P, P_v_star, S, E, phi`v_star);
        psi := poly`elt * pi^-poly`denval;
	
        /* Step d *************************************************************/
        vprint RoundFour,5:"R4d gamma := phi/psi";
        poly_inv := elt_inverse(poly, Phihat);
	
        gamma := elt((phi`elt * poly_inv`elt) mod Phihat, poly_inv`denval-poly`denval);
//gamma;
        gamma`elt := gamma`elt mod pi^(gamma`denval+1);
//gamma;
        elt_invariants(Phihat, traces_Phihat, ~gamma);
//gamma;
        
        if not gamma`v_star eq 0 then
          //print vstar_phi,old_vstar_phi;
          error "Factorization: Insufficient precision in Round Four main loop";
        end if;
	
        /* Step e *************************************************************/
	if not gamma`passes_hensel_test then
	    vprint RoundFour,1:"R4e gamma fails Hensel test -- factoring";
            theta := elt_evaluate_trans(Phi,traces_Phi,gamma,BETA); 
	    return further_factorization(hensel_lift_factorization_chi2
                                         (Phi, theta), with_certificates);
        else    
           vprint RoundFour,4:"R4e gamma passes Hensel test";
	end if;

	/* Step f ************************************************************/
        //vprint RoundFour,5:"R4f new inertia by gamma ?";
        if F mod gamma`f ne 0 then // increase F
          // change reference polynomial Phihat, such that
          //   F_x = LCM(F,F_gamma)
          // start the main loop again with  Step a
          kappa := ff_composition_gen(Phihat, PR.1, F, gamma);
          if E * LCM(F, gamma`f) eq Degree(Phihat) then // Phi is irreducible
             F := LCM(F, gamma`f);         
             vprint RoundFour,1:"R4f E * lcm(F,F_gamma) =",E,"*",F,"= deg(Phi) =",Degree(Phihat),
                             "  =>   Phi is irreducible";    
             if with_certificates then
		vprint RoundFour,1:"R4f computing 2 element certificate";
                Pi := elt_with_v_star(Phihat, P, P_v_star, S, E, 1/E);
                Pi := elt_evaluate(Phi, Pi, BETA);
                elt_invariants(Phi, traces_Phi, ~Pi);
                if Pi`v_star ne 1/E then
                  error "Factorization: Insufficient precision in computation of ramified certificate";
                end if;
                Gamma := elt_evaluate(Phi, kappa, BETA);
                elt_invariants(Phi, traces_Phi, ~Gamma);
                //print "F",F;
                if Gamma`f ne F then
                  error "Factorization: Insufficient precision in computation of unramified certificate";
                end if;
                return [rec<FACTOR| factor := Phi, multiplicity := 1, 
                            F:=F, Gamma := Gamma`elt, Gamma_denval := Gamma`denval,
                            E:=E, Pi := Pi`elt, Pi_denval := Pi`denval>];
             else
               return [rec<FACTOR| factor := Phi, multiplicity := 1,F:=F,E:=E>];
             end if;
	  /* Step g ************************************************************/
          else // find a new reference polynomial Phihat
            F := LCM(F, gamma`f);         
	    vprint RoundFour,1:"R4 increasing F from",F,"to", F, "and resetting E to 1";
//"kappa",kappa;            
            beta := kappa;
            //beta`elt := beta`elt+pi^(beta`denval+1)*PR.1;
            vprint RoundFour,5:"R4g searching beta with F_beta = F =",F,
                               "and chi_beta irreducible of Degree deg(Phi) =",Degree(Phi); 
            newPhi := elt_chi(Phihat, traces_Phihat, beta);
            //while not is_squarefree(newPhi) do
            if Discriminant(Phihat) ne 0 then
              // we can use the discriminant for testing whether newPhi is
              // squarefree
              while Discriminant(newPhi) eq 0 do
                // assure that the new reference polynomial is squarefree
                // then it generates the same extension as Phi
                vprint RoundFour,5:"R4g beta := beta + pi*x";
                beta`elt := beta`elt+pi^(beta`denval+1)*PR.1;
                newPhi := elt_chi(Phihat, traces_Phihat, beta);
              end while;
            else
              // better also use the gcd for testing whether newPhi is
              // squarefree as we have a precion problem with the discriminant
              // already
              while not is_squarefree(newPhi) do
                vprint RoundFour,5:"R4g beta := beta + pi*x";
                beta`elt := beta`elt+pi^(beta`denval+1)*PR.1;
                newPhi := elt_chi(Phihat, traces_Phihat, beta);
              end while;
            end if;
              
            Phihat := newPhi;
            traces_Phihat := traces_from_poly(Phihat);

            // reinitialize
            E := 1;
            P := [];
            S := [];
            P_v_star := [];
            phi_old_v_star := 0;
            
            BETA := elt_evaluate(Phi, beta, BETA);
            vprint RoundFour,4:"R4g new inertia element beta =",BETA`elt;
            vprint RoundFour,4:"R4g with denominator pi ^",BETA`denval;
            
            phi := elt(PR.1,0); phi`chi := Phihat;
            phi`chi := Phihat;
            elt_invariants(Phihat,traces_Phihat,~phi);
            if not phi`passes_newton_test or not phi`passes_hensel_test then
              vprint RoundFour,1:"R4g Newton test or Hensel test failed -- factoring";
              theta := elt_evaluate_trans(Phi,traces_Phi,phi,BETA); 
              return further_factorization(newton_lift_factorization_chi2
                       (Phi, theta), with_certificates);
            end if;
  
            nu := phi`nu;
            phi:= elt(phi`nu,0); elt_invariants(Phihat,traces_Phihat,~phi);
	  end if;
        else 
          // no increase of F
          // continue in main loop
        /* Step h *************************************************************/
          vprint RoundFour,5:
          "R4h find integral delta with chi(delta)=chi(gamma) mod (pi) and deg(delta)<F";
          rho_passes_hensel_test, delta, rho := 
            res_field_rep(Phihat,traces_Phihat,nu,gamma);
          if not rho_passes_hensel_test then
	    vprint RoundFour,1:"R4h rho fails Hensel test -- factoring";
            theta := elt_evaluate_trans(Phi,traces_Phi,rho,BETA); 
	    return further_factorization(hensel_lift_factorization_chi2
                   (Phi, theta),with_certificates);
          end if;
          vprint RoundFour,3:"R4h delta =",delta;
        /* Step i *************************************************************/
          vprint RoundFour,5:"R4i phi := phi - delta * psi";
	  deltapsi := delta * psi;
          //print "deg", Degree(deltapsi);
          phi_old_v_star := phi`v_star;
          phi := elt(phi`elt-deltapsi,0);  elt_invariants(Phihat,traces_Phihat,~phi);
        end if; // increase F
    end while;
end function;

////////////////////////////////////////////////////////
// auxilary functions for factorization.

make_monic_and_integral := function(f)
// return true, g, dival, uni, exp such that
// g := uni*pi^multval*f(pi^exp*x) has integral coefficients and is monic
// g is over the quotient ring !
// if because of insuffient precision such elements cannot be computed, return
// false, 0, 0, required precision, exp

  // if f is monic and integral do nothing
  //if IsMonic(f) and Minimum([Valuation(a) : a in Eltseq(f)]) ge 0 then
  //  
  //return

  PK := Parent(f);
  K  := CoefficientRing(PK);
  overfield := IsField(K);
  if overfield then 
    R := RingOfIntegers(K);
    PR := PolynomialRing(R);
    minval := Integers()!Minimum([Valuation(a) : a in Eltseq(f)]);
    divi := UniformizingElement(K)^(minval);
    g := PR!(f/divi);
    multval := -minval;
  else
    R := K;
    PR := PK;
    minval := Integers()!Minimum([Valuation(a) : a in Eltseq(f)]);
    divi := UniformizingElement(K)^(minval);
    g := PR!(f div divi);
    multval := -minval;
  end if;
  if IsZero(g) then
     return true, g, _, _, _;
  end if;
  //print g; 
  PR := PolynomialRing(R);
  pi := UniformizingElement(R);
  lead := LeadingCoefficient(g);
  vallead := Valuation(lead);
  seq := Eltseq(g);
  exp := -1;
  if not Degree(g) le 0 then
    repeat
      exp +:=1; 
      expmult := Degree(g)*exp-vallead;
      //print "expmult",expmult;
    until expmult ge 0 and
          Minimum([Valuation(seq[i])-exp*(i-1)+expmult:i in [2..#seq]]) ge 0;
    if vallead+expmult ge Precision(R) or exp*Degree(g) ge Precision(R) then
      return false, 0, 0, vallead+expmult+exp*Degree(g), exp;
    end if;
  else
    exp := 0;
    expmult := - vallead;
  end if;
  g := g * pi^expmult;
  //print "exp",exp;
  //print g;
  g := PR![Eltseq(g)[i] div pi^(exp*(i-1)) : i in [1..(Degree(g)+1)]];
  //print g;
  multval := multval+expmult;
  prec := Minimum([AbsolutePrecision(c) : c in Coefficients(g)]);
  if Type(R) eq RngSerPow and Precision(R) eq Infinity() then
    // ChangePrecision on an unbounded series ring just changes the
    // default precision
    QR := PowerSeriesRing(CoefficientRing(R), R`DefaultPrecision);
  elif Type(R) eq RngSerExt and Precision(R) eq Infinity() then 
    QR := ChangePrecision(R, R`DefaultPrecision);
  elif Type(R) eq RngPad then
    QR := quo<R|pi^R`DefaultPrecision>;
  else
    QR := R;
  end if;
  PQR := PolynomialRing(QR); x := PQR.1;
  g := PQR!g;
  uni := LeadingCoefficient(g);
  //print uni;
  g := g div uni;
  assert IsMonic(g);
  return true, g, uni, multval, exp;
end function;


undo_monic_and_integral := function(f,exp,h)
// make the reverse changes made to f by make_monic_and_integral to h
// actually only the exp part, the rest goes into the scalar returned
// with the polynomial factorization.

  g := h;//*uni;

  PK := Parent(f);
  K := CoefficientRing(PK);
  pi := UniformizingElement(K);
  
  g := PK!g;
  g := Evaluate(g,pi^exp*PK.1);

  return g;
end function;



/////////////////////////////////////////////////////////////////////

intrinsic SuggestedPrecision(f::RngUPolElt) -> RngIntElt
{For a polynomial f over a local ring or field return a precision at which
 the factorization of f as given by Factorization(f) will be Hensel liftable
 to the correct factorization.}
 
    require Type(CoefficientRing(Parent(f))) in {RngPad, FldPad} : "Coefficient ring must be a p-adic ring or field";

  // the trivial cases
  if Degree(f) eq 0 then 
    max := Maximum([2,Valuation(TrailingCoefficient(f))+1]);
    return max;
  elif Degree(f) eq -1 then
    return 1;
  end if;

  // monic and integral
  if ((IsUnit(LeadingCoefficient(f)) and 
       not IsField(CoefficientRing(Parent(f)))) or
      IsMonic(f)) and
      Minimum([Valuation(c) : c in Eltseq(f)]) ge 0 then
    // make sure it is also squarefree
    if Valuation(Discriminant(f)) lt 
      Precision(CoefficientRing(Parent(f))) 
      and Precision(CoefficientRing(Parent(f))) lt Infinity() then
      max := Maximum([2*RamificationIndex(CoefficientRing(Parent(f))),
                      2*Valuation(Discriminant(f))]);
      return max;
    end if;
  end if;
  tmp_R := CoefficientRing(Parent(f));
  if Type(tmp_R) eq RngPad then
    f := PolynomialRing(
	    quo<tmp_R|UniformizingElement(tmp_R)^(2*tmp_R`DefaultPrecision)>)!f;

  else
    /* 
    above doesn't work at all for fields, this might not always but only chance
    so far. Better than before!
    */
      f := PolynomialRing(ChangePrecision(tmp_R, (2*tmp_R`DefaultPrecision)))!f;
  end if;

  ok, h, uni, multval, exp := make_monic_and_integral(f);
  mmai_prec := Valuation(LeadingCoefficient(f))+multval+exp*Degree(f);
  if not ok then
    //print "increasing prec";
    mmai_prec := multval+exp*Degree(f);
    PK := PolynomialRing(ChangePrecision(CoefficientRing(Parent(f)),
                                         mmai_prec));
    good, h, uni, multval, exp := make_monic_and_integral(PK!f);
    if not good then
      error "I cannot suggest a precision.";
    end if;
  end if;

  require not IsZero(h) : "Argument 1 is not non-zero";
     
  PR := Parent(h);
  P := CoefficientRing(h);

  //print h;
  
    // correct the precision for the derivative
    seq := Eltseq(h);
    max := Maximum([Valuation(seq[i])+Valuation(P!(i-1)):i in [2..#seq]]);
    //print "precision increase derivative",max-Precision(P);
    newloss := Maximum([max-Precision(P),0]);
//RamificationIndex(P) eq 1 and InertiaDegree(P) eq 1 then
    repeat // loop for the valuation of the discriminant
       loss := 0;
       gcd := 0; 
       repeat
         old_P := P; 
         P := ChangePrecision(P,Precision(P)+(newloss));
         //print "precision",Precision(P);
         PK := PolynomialRing(ChangePrecision(CoefficientRing(Parent(f)),
                                         Precision(P)));
         good, h, uni, multval, exp := make_monic_and_integral(PK!f);
         //print "new h",h;
         if not good then
            error "I cannot suggest a precision.";
         end if;
         h := PolynomialRing(P)!h;
         dh := Derivative(h);
         old_gcd := gcd;
         //print "h",h;
         //print "dh",dh;
         vprint  RoundFour,4: "R4: gcd";
         gcd, newloss := _gcd(h,dh);
         //print "newloss",newloss;
         loss := loss + newloss;
         //print "gcd",gcd, newloss;
         //print "h mod gcd",h mod gcd;
         //print "h div gcd",h div gcd;
       until old_gcd eq PolynomialRing(old_P)!gcd and h mod gcd eq 0;
       hh := h div gcd;
       //print hh;
       if RamificationIndex(P) eq 1 and InertiaDegree(P) eq 1 then
         val := Valuation(Discriminant(PolynomialRing(Rationals())!hh),
                          Prime(P));
         done := val ne Infinity();
         //print val;
       else
         val := Valuation(Discriminant(PolynomialRing(P)!hh));
         done := val lt Precision(P);
       end if;
       //print "val",2*val,loss,mmai_prec;
    until done and newloss lt Precision(P); 
    max := Maximum([2*val+loss,mmai_prec+loss,2,Precision(P)]);    
    return max;

end intrinsic;

_IsSquarefree := IsSquarefree;

intrinsic LocalFactorization(f::RngUPolElt:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into irreducible 
 factors together with the appropriate scalar and certificates for the irreducibility of the 
 factors if requested }

 require not IsZero(f) : "Argument 1 is not non-zero";

    with_certificates := Certificates or Ideals or Extensions;

    C := CoefficientRing(Parent(f));
    require Type(C) in {RngPad, FldPad, RngSerExt} or (Type(C) in {RngSerPow, RngSerLaur} and Type(CoefficientRing(C)) eq FldFin) : "Coefficient ring must be a p-adic ring or field";
 
    if Precision(C) eq Infinity() and
       Extensions then
      error "Factorization: 'Extensions' can only be used over finite precision rings/fields";
    end if;

    //print "Factorization",f;
    ok, h, uni, multval, exp := make_monic_and_integral(f);  
    if not ok then
      error "Factorization: Insufficient precision";
    end if;
  require not IsZero(h) : "Argument 1 is not non-zero";
    assert IsMonic(h);
    //print h;
    PQR := Parent(h);
    QR := CoefficientRing(PQR);

    is_sq_free, sq_free_part, loss := is_squarefree(h);
    if is_sq_free then 
      RF, mR := ResidueClassField(QR);
      ff := Polynomial([mR(x) : x in Eltseq(sq_free_part)]);
      if _IsSquarefree(ff) and not with_certificates 
        and not ISA(Type(QR), RngSer) then // Hensel needs coercion to the
                 // residue class field - which is not set up for series rings
        l := Factorization(ff);
	if #l eq 0 then
	    r4 := [];
        elif #l eq 1 then
          r4 := [sq_free_part];
        else
	  m := hom<PQR -> PolynomialRing(RF) | mR, Polynomial(RF, [0, 1])>;
          r4 := HenselLift(sq_free_part, [m(x[1]) : x in l]);
        end if;
        r4 := [ rec<FACTOR| factor := x, multiplicity := 1> : x in r4];
      else
        r4 := round_four(h,with_certificates);
      end if;
      res := [<undo_monic_and_integral(f, exp, a`factor),1> : a in r4];
    else      
      g := sq_free_part;

//"h",h;
//"g",g;      
      r4 := round_four(g,with_certificates);
      res := [<a`factor, 0> : a in r4];
      //hh := h;
      for i := 1 to #res do
        hh := h;
        repeat
          //print "hh pre",hh;
          hh := hh div res[i][1];
          rem := hh mod res[i][1];
          res[i][2] +:= 1;
          //print "hh post",hh;
          zero := rem eq 0;
          done := false;
          if not zero then 
            done := Minimum([Valuation(a):a in Eltseq(rem)]) lt Precision(QR)-loss;
          end if;
        until done;
      end for;
      //print res;
//print "exp sum", &+[a[2]*Degree(a[1]) : a in res],"=?=",Degree(f);
      //print res;

      if &+[Integers() | a[2]*Degree(a[1]) : a in res] ne Degree(f) then
        //print res;
//"res",res;
//"f",f;
	require Characteristic(C) ne 0 : "Factorization: Insufficient precision in factorization of a non-squarefree polynomial.";
      end if;
      res := [<undo_monic_and_integral(f, exp, a[1]), a[2]> : a in res];
    //print res;    
    end if; // squarefee by gcd
//  end if;  // is_squarefree_easy
  
    procedure handle_inseparable_stuff(C, h, ~res, ~cert)
	//NEED TO DETECT THE INSEPARABLE FACTORS HERE WHICH HAVE FALLEN OUT OF THE
	//SQUAREFREE PART
	//divide out all factors to get the inseparable factors left over
	if Characteristic(C) gt 0 then
	    Pres := Parent(f);
	    insep := h;
	    for i := 1 to #res do
		for j := 1 to res[i][2] do
		    insep := insep div Parent(insep)!res[i][1];
		end for;
	    end for;
	    if Degree(insep) gt 0 then
		mult := 0;
		repeat 
		    bool, new_insep := IsPower(insep, Characteristic(C));
		    if bool then
			mult +:= 1;
			insep := new_insep;
		    end if;
		until not bool or Degree(insep) eq 1;
		//THIS IS NOT REALLY IT : NEED TO FACTOR insep
		//which is hopefully irreducible if it is still inseparable 

		//keep taking p-th roots extending the coefficient field
		//Make a map into another series ring mapping t -> t^p
		//so that p-th roots exist again
		//coefficients are finite field elements and all with have p-th 
		//roots
		//Derivative(insep) == 0 -> only have non zero coeffs of p-powers
		//in the polynomial terms
		p_mult := 0;
		tp_exp := 0;
		sep_insep := insep;
		while IsZero(Derivative(sep_insep)) do
		    //map t -> t^p
		    tp_exp +:= 1;
		    CC := PowerSeriesRing(CoefficientRing(C), Characteristic(C)*Precision(C));
		    ch := hom<CoefficientRing(sep_insep) -> CC | CC.1^Characteristic(C)>;
		    PCC := PolynomialRing(CC);
		    ph := hom<Parent(sep_insep) -> PCC | ch, PCC.1>;
		    sep_insep := ph(sep_insep);
		    //take as many p-th roots as we can before extending again
		    repeat 
			bool, new_insep := IsPower(sep_insep, Characteristic(C));
			if bool then
			    p_mult +:= 1;
			    sep_insep := new_insep;
			end if;
		    until not bool or Degree(sep_insep) eq 1;

		    /*
		    PCC := PolynomialRing(CoefficientRing(C));
		    poly_insep := Coefficients(insep);
		    poly_insep := [Valuation(c) eq Infinity() select 0 else PCC.1^Valuation(c)*PCC!Eltseq(c) : c in poly_insep];
		    poly_insep := Polynomial(PCC, poly_insep);
		    poly_insep_fact, sc := Factorization(poly_insep);
		    insep_fact := [<Polynomial(C, Eltseq(factor[1])), factor[2]> : factor in poly_insep_fact];
		    */
		end while;
		assert tp_exp le p_mult;
		mult +:= p_mult;
		mult := Characteristic(C)^mult;
		// any more inseparable bits will be handled in the recursion!
		insep_fact, sc, certs := Factorization(sep_insep : Certificates := Certificates, Ideals := Ideals, Extensions := Extensions);

		PSX := PuiseuxSeriesRing(CoefficientRing(C));
		H := hom<QR -> PSX | PSX.1^(1/Characteristic(C)^tp_exp)>;
		ph := hom<PQR -> PolynomialRing(PSX) | H, Polynomial([0, 1])>;
		assert IsWeaklyZero(sc - 1);
		for i := 1 to #insep_fact do
		    //take pth-powers to get back to the coeff ring
		    in_f := insep_fact[i][1];
		    //DIV is multiplicative!!
		    DIV := 1;
		    pin_f := ph(in_f);
		    
		    function is_almost_coercible(R, g)
			return IsCoercible(R, [Truncate(c) : c in Coefficients(g)]);
		    end function;
		    while not is_almost_coercible(Parent(h), pin_f) do
			pin_f := pin_f^Characteristic(C);
			//pin_f := ph(in_f);
			DIV *:= Characteristic(C);
			assert mult mod DIV eq 0;
			assert DIV le Characteristic(C)^tp_exp;
			assert DIV le Characteristic(C)^p_mult;
		    end while;
		    //is there any other multiplicity which needs to be considered?
		    //NEED to divide insep_fact[i][2] by Characteristic(C) each time we power!@!@!@!@!!@
		    bpin_f := Pres![Truncate(c) + (AbsolutePrecision(c) eq Infinity() select 0 else O(PSX.1^Floor(AbsolutePrecision(c)))) : c in Coefficients(pin_f)];
		    Append(~res, <bpin_f, mult*insep_fact[i][2] div DIV>);
		    //if the irreducible factor is inseparable then forget certs etc
		    //or a characteristic-th power
		    if with_certificates and not IsZero(Derivative(insep)) then
			//sort out the certificates
			Append(~cert, certs[i]);
		    else
			error if with_certificates, "Certificates etc can not be given when there is an inseparable irreducible factor";
		    end if;
		end for;
	    end if;
	end if;
    end procedure;

    PR := Parent(f);
    R := CoefficientRing(PR);
    pi := UniformizingElement(R);   
    
    if not IsField(R) then  // distribute the scalar factor 1/pi^multval
      for i := 1 to #res do // over the factors
        min :=  Integers()!Minimum([Valuation(a) : a in Eltseq(res[i][1])]);
        res[i][1] div:= pi^min;
        multval -:= res[i][2]*min;
      end for; 
      assert multval le 0;
    elif false then
	lc := 1;
	for i := 1 to #res do
	    lc *:= LeadingCoefficient(res[i][1])^res[i][2];
	    res[i][1] div:= LeadingCoefficient(res[i][1]);
	end for;
	multval -:= Valuation(lc);
	uni *:= lc/pi^Valuation(lc);
    end if;
    sca := (R!uni) * pi^(-multval);

    assert Characteristic(C) ne 0 or &+[Integers() | Degree(ff[1])*ff[2] : ff in res] eq Degree(f);
    
    //==========================================
    if with_certificates then
      CERT := recformat<F:RngIntElt,   // inertia deg
                        Rho:RngUPolElt, // unramified certificate
                        E:RngIntElt,   // ram index
                        Pi:RngUPolElt,  // ramified certificate
                        IdealGen1,      // 2 element representation of
                        IdealGen2:RngUPolElt,// the corresponding global ideal
                        Extension>;     // extension of R given by the
                                        // factor
                          
      if not IsField(R) then
        K := FieldOfFractions(R);
        PK := PolynomialRing(K);
      else
        K := R;
        PK := PR;
      end if;
      Kpi := UniformizingElement(K);
                        
//PQR, PK;
//r4[1]`Gamma, Eltseq(PK!(r4[1]`Gamma)), Kpi^r4[1]`Gamma_denval;
      cert := [rec<CERT| F:=fact`F,                
                         Rho:=PK!(fact`Gamma)/Kpi^fact`Gamma_denval,
                         E:=fact`E,
                         Pi:=PK!(fact`Pi)/Kpi^fact`Pi_denval> :
                         fact in r4];
      //-----------------------------------------
      if Ideals then
        for i := 1 to #res do
          cert[i]`IdealGen1 := pi;
          poly := PK!res[i][1];
          copoly := 1;
          for j := 1 to #res do
            if j ne i then
              copoly := copoly *PK!res[j][1];
            end if;
          end for;
          g,c,d := XGCD(poly,copoly);
          cert[i]`IdealGen2 := cert[i]`Pi*d*copoly+poly*c;
        end for;
      end if;
      //-----------------------------------------
      if Extensions then
        vprint RoundFour,1:" -- computing local extensions"; 
        for i := 1 to #res do
            Phi := r4[i]`factor;
            //print "Phi",Phi;
            traces_Phi := traces_from_poly(Phi);
            if cert[i]`F gt 1 then
              Rho := elt(r4[i]`Gamma, r4[i]`Gamma_denval); 
              elt_invariants(Phi, traces_Phi, ~Rho);
              //print "Gamma",r4[i]`Gamma, r4[i]`Gamma_denval;
              //print "chi_Rho",chi_Rho;
              if not Rho`passes_hensel_test then
                error "Factorization: something went wrong with the unramified certificate";
              end if;
              assert Rho`f eq cert[i]`F;
              U := UnramifiedExtension(R,Rho`nu);
            else
              U := R;
            end if;
            if cert[i]`E gt 1 then
              vprint RoundFour, 2:
                "Extension is (partly) ramified, searching for defining polynomial";
              Pi := elt(r4[i]`Pi, r4[i]`Pi_denval); 
              elt_invariants(Phi, traces_Phi, ~Pi);
              PU := PolynomialRing(U);
              if cert[i]`F gt 1 then
                // unfortunately the precison used to factor f is not
                // neccessarily sufficient for factoring chi_Pi
                // (See example of Nils B, example-1)
                // Actually, the problem seem to be that if Pi is actually
                // defined over the starting ring then obviously Pi`chi is
                // a pure power. Due to numerical errors in finding Pi`chi(?)
                // and definetely due to numerical problems in GCD/XGCD
                // this means that the factorisation is going to fail.
                // Thus we substitute Pi <- Pi+Rho to make Pi`chi
                // squarefree.
                tmp_U := U; 
                //tmp_U := ChangePrecision(U, 
                //    Maximum([2*Valuation(Discriminant(Pi`chi)),Precision(R)]));
                tmp_PU := PolynomialRing(tmp_U);
                if not true or 2*Valuation(Discriminant(Pi`chi)) gt Precision(R) then
                  vprint RoundFour, 2:
                    "char-poly of Pi probably not squarefree, shifting...";

		  function hensel_lift(f, a, m)
		    Pa := Parent(a);
		    a := quo<Pa | m>!a;
		    f_der := Derivative(f);

		    Kprec := Precision(K);

		    function change_precision(g, Kprec)
			return Parent(g)!Polynomial(
				[ChangePrecision(c, Kprec) : c in Coefficients(g)]
			       );
		    end function;

		    ev := Evaluate(f, a);
		    ev_d := Evaluate(f_der, a);

		    rep := RepresentationMatrix(ev_d)^-1;
		    ev_d := Parent(ev)!Polynomial(Eltseq(rep[1]));
		    ev_d := change_precision(ev_d, Kprec);
		    ev *:= ev_d;
		    ev := change_precision(ev, Kprec);
		    a := change_precision(a, Kprec);

		    two := 2;
		    while not IsWeaklyZero(ev) do
			a := a - ev;
			a := change_precision(a, Kprec);

			ev := Evaluate(f, a);
			if IsWeaklyZero(ev) then
			    break;
			end if;
			tmp := Evaluate(f_der, a);
			tmp2 := tmp * ev_d;
			tmp := two - tmp2;
			ev_d := ev_d * tmp;
			ev := ev * ev_d;
		    end while;

		    return Pa!a;

		  end function;
                
		  u := hensel_lift(Rho`nu, cert[i]`Rho, Phi);
		  denval := -Minimum([Valuation(c) : c in Eltseq(u)]);
		  u *:= Kpi^denval;
                  Pi_new := elt_add(Pi, elt(Parent(Rho`elt)!u, denval));
                  elt_invariants(Phi, traces_Phi, ~Pi_new);
                  assert 2*Valuation(Discriminant(Pi_new`chi)) lt Precision(R);

                  vprint RoundFour, 2:
                    "Factoring char-poly of Pi, shifted";
                  IndentPush();
                  vtime RoundFour, 3:              
                  fact := Factorization(tmp_PU!(PU!(PR!Pi_new`chi)));
                  IndentPop();
                  vprint RoundFour, 2:
                    "Shifting back...";
		  // tmp_U.1 is not the same as Rho!!!!!
		  // tmp_U.1 is a lift of Rho from precision 1
		  // How do we get Rho to be an element of U so that we can
		  // shift by it?
		  // Or do the shift above with tmp_U.1!!!!!!
		  //HenselLift(tmp_PU!PolynomialRing(Integers())!Rho`chi, tmp_U.1);
                  fact := 
                    [<Evaluate(x[1], Parent(x[1]).1+ tmp_U.1) mod res[i][1], x[2]> 
                            : x in fact];
                else
                  vprint RoundFour, 2:
                    "Factoring char-poly of Pi";
                  IndentPush();
                  vtime RoundFour, 3:              
                  fact := Factorization(tmp_PU!(PU!(PR!Pi`chi)));
                  IndentPop();
                end if;
                //"fact4",fact;
                assert &and[Degree(fact[j][1]) eq Degree(Phi) div cert[i]`F : j in [1 .. #fact]];

                /*CF: for ONE of the factors we should have
                  - move the factors (over U) to be over Qp by mapping U.1 to
                    Rho
                  - evalutate the NEW polynomial at Pi
                  one the the factors, precisely ONE should essentially
                  vanish.
                  So what we need(?) to do is
                    - lift Rho modulo r4[i]`factor as a root of
                      DefiningPolynomial(U)
                    - map the factors over to mod r4[i]`factor using the
                      lifted Rho. Then evalutate at Pi (mod r4`factor) and take
                      the UNIQUE factor that gives zero this way.  

		  MUST use polynomials from r4 as they are the monic integral
		  ones - the polynomials in res don't work well if they are not 		  monic and integral
                */

                vprint RoundFour, 2: "trying to identify the correct polynomial to define the ramified part...";

                no := function(x, f)
                  /* compute the norm of x in the extension given
                   * by f. Done as Determinant(RepMat(x))
                   */
                  m := Matrix([(Eltseq((x*(Parent(f).1)^i) mod f) 
                       cat [0 : i in [0..Degree(f)]])[1..Degree(f)]
                         : i in [0..Degree(f)-1]]);
                  v := Minimum([Valuation(x) : x in Eltseq(m)]);
                  m := Matrix(Integers(CoefficientRing(m)), m*UniformizingElement(CoefficientRing(m))^-v);
                  return Valuation(Determinant(m))+v*Nrows(m);
                end function;

                assert #fact gt 1;

                a := cert[i]`Rho;
                C := Parent(a);
                max_p := Precision(CoefficientRing(C));
                //we can't go further than the precision of the underlying
                //ring....
                cur_pr := 1;

                zf := DefiningPolynomial(U);
                zfs := Derivative(zf);
                w := 1/Evaluate(zfs, U.1);
                w := Evaluate(Polynomial(Eltseq(w)), cert[i]`Rho);
                vprint RoundFour, 2: "Starting lift of Rho";

                repeat
                  w := (w*((C!2)-w*Evaluate(zfs, a))) mod r4[i]`factor;
                  a := (a - Evaluate(zf, a)*w ) mod r4[i]`factor;

                  cur_pr *:= 2;
                  vprint RoundFour, 3: "lifting now at", 
                    cur_pr, (no(w*Evaluate(zfs, a) - 1, r4[i]`factor)),
                    no(Evaluate(zf, a), r4[i]`factor);
                  vals := [];
                  for z in fact do
                    zg := Polynomial([h(x) : x in Eltseq(z[1])]) where
                      h := map<U -> C | 
                        x:-> Evaluate(Polynomial(Eltseq(x)), a)>;
                    zzf := Evaluate(zg, cert[i]`Pi);
                    zzf := zzf mod r4[i]`factor;
                    Append(~vals, no(zzf, r4[i]`factor));
                  end for;  
                  vprint RoundFour, 2: "Factors produce valuations of", vals;
                  m, mp := Maximum(vals);
                  Sort(~vals);
                until cur_pr ge max_p or (m gt 2*vals[#vals-1] and m gt 0);
                if cur_pr ge max_p then
                  error "Could not find the correct factor";
                end if;
                vprint RoundFour, 2: "The ", mp, "factor is it!";
                z := mp;
                if (2*Valuation(Discriminant(fact[z][1]))+cert[i]`E)/cert[i]`E
                   gt Precision(U) then
                   error "Factorization: The Precision was not high enough",
                         "to assure that the ramified extension is unique";
                end if;
                T := TotallyRamifiedExtension(
				    U,increase_precision(PU!fact[z][1], U)
		     );
              else
                T := TotallyRamifiedExtension(
					U,increase_precision(PU!Pi`chi, U)
		     );
              end if;
            else
              T := U;
            end if;
            cert[i]`Extension := T;
        end for;
      end if;
      handle_inseparable_stuff(C, h, ~res, ~cert);
	assert (#res eq 0 and Degree(f) eq 0) or &+[Degree(ff[1])*ff[2] : ff in res] eq Degree(f);
      return res, sca, cert;
    //===========================================
    else   
      handle_inseparable_stuff(C, h, ~res, ~res);
      assert Degree(f) eq 0 and #res eq 0 or &+[Degree(ff[1])*ff[2] : ff in res] eq Degree(f);
      return res, sca, _;
    end if;
end intrinsic;




intrinsic IsIrreducible(f::RngUPolElt[RngPad]) -> BoolElt
{True iff f is irreducible}
    F := Factorization(f);
    return #F eq 1 and F[1][2] eq 1;
end intrinsic;

intrinsic IsIrreducible(f::RngUPolElt[FldPad]) -> BoolElt
{True iff f is irreducible}
    F := Factorization(f);
    return #F eq 1 and F[1][2] eq 1;
end intrinsic;

intrinsic Factorization(f::RngUPolElt[RngPad]:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into monic irreducible 
 factors together with the appropriate scalar and certifcates for the irreducibility of the 
 factors if requested }
    return LocalFactorization(
	f :
	Certificates := Certificates, IsSquarefree := IsSquarefree,
	Ideals := Ideals, Extensions := Extensions
    );
end intrinsic;


intrinsic Factorization(f::RngUPolElt[FldPad]:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into monic irreducible 
 factors together with the appropriate scalar and certifcates for the irreducibility of the 
 factors if requested }
    return LocalFactorization(
	f :
	Certificates := Certificates, IsSquarefree := IsSquarefree,
	Ideals := Ideals, Extensions := Extensions
    );
end intrinsic;

intrinsic Factorization(f::RngUPolElt[RngSerPow[FldFin]]:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into monic irreducible 
 factors together with the appropriate scalar and certifcates for the irreducibility of the 
 factors if requested }
    return LocalFactorization(
	f :
	Certificates := Certificates, IsSquarefree := IsSquarefree,
	Ideals := Ideals, Extensions := Extensions
    );
end intrinsic;

intrinsic Factorization(f::RngUPolElt[RngSerLaur[FldFin]]:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into monic irreducible 
 factors together with the appropriate scalar and certifcates for the irreducibility of the 
 factors if requested }
    return LocalFactorization(
	f :
	Certificates := Certificates, IsSquarefree := IsSquarefree,
	Ideals := Ideals, Extensions := Extensions
    );
end intrinsic;

intrinsic Factorization(f::RngUPolElt[RngSerExt]:Certificates:=false,
                                      IsSquarefree:=false,
                                      Ideals := false,
                                      Extensions := false) 
          -> SeqEnum, RngElt,.
{Factorization of a polynomial f over a local ring or a local field into monic irreducible 
 factors together with the appropriate scalar and certifcates for the irreducibility of the 
 factors if requested }
    return LocalFactorization(
	f :
	Certificates := Certificates, IsSquarefree := IsSquarefree,
	Ideals := Ideals, Extensions := Extensions
    );
end intrinsic;

function extension_from_irreducible_polynomial(f)

    fact, s, exts := Factorization(f : Extensions := true);
    if #fact ne 1 or fact[1][2] gt 1 then
	return false, _, _, _;
    end if;

    E := exts[1];
    _, h, _, _, exp := make_monic_and_integral(f);
    return true, E`Extension, Evaluate(E`Pi, UniformizingElement(CoefficientRing(f))^exp*Parent(E`Pi).1), E`Rho;

end function;

intrinsic InternalExtensionFromIrreduciblePolynomial(f::RngUPolElt[RngPad]) -> BoolElt, RngPad, RngUPolElt, RngUPolElt
{};
    return extension_from_irreducible_polynomial(f);
end intrinsic;

intrinsic InternalExtensionFromIrreduciblePolynomial(f::RngUPolElt[FldPad]) -> BoolElt, FldPad, RngUPolElt, RngUPolElt
{};
    return extension_from_irreducible_polynomial(f);
end intrinsic;


/*
  <example-1>
  //Nils Bruin
  f:=x^28 - 20*x^27 + 138*x^26 - 252*x^25 - 745*x^24 + 4864*x^23 - 
           10688*x^22 + 900*x^21 + 64119*x^20 - 195660*x^19 + 
           329802*x^18 - 432508*x^17 + 591807*x^16 - 901604*x^15 +
           1346326*x^14 - 1781540*x^13 + 1976578*x^12 - 1806388*x^11 +
           1366474*x^10 - 830284*x^9 + 341412*x^8 - 26204*x^7 - 
           71616*x^6 + 41744*x^5 - 1735*x^4 - 8216*x^3 + 4064*x^2 -
           832*x + 64;
  fs:=[c[1]:c in Factorisation(f)];
  Qp:=pAdicField(2,80);
  Factorisation(Polynomial(Qp,f):Extensions); 
  Qp:=pAdicField(2,1000);
  Factorisation(Polynomial(Qp,f):Extensions); 
  </example-1>


*/
