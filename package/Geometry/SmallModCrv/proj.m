freeze;
///////////////////////////////////////////////////////////////////
// Functions for projection maps between Small Modular Curves,   //
//       j-invariants and E2N,E4 & E6 forms                      //
//                                                               //
//             mch - 11/2011                                     //
///////////////////////////////////////////////////////////////////

import "../Crv/curve_autisos.m": DenomsOfDegree, RatFnNum, 
 ReduceMapDegree, FunctionFieldEvaluation, coerce_to_ff;
import "points.m": is_a_cusp_point, is_a_cusp_place;
import "auts.m": crv_iso_to_ff_map;
import "../Crv/gen_crv_auto_gp.m": gen_seq;
import "../CrvMod/elkies.m":ElkiesKernel; 

function MonicPolSqrt(p)
// p(x) := x^2n+.. is the square of a monic polynomial q(x) [char ne 2]
//  returns q
    R := Parent(p);
    n := Degree(p) div 2;
    if n eq 0 then return R!1; end if;
    as := Reverse(Prune(Coefficients(p)));
    bs := [as[1]/2];
    for j in [2..n] do
	Append(~bs,(as[j]-&+[bs[i]*bs[j-i] : i in [1..j-1]])/2);
    end for;
    q := R!(Reverse(bs) cat [1]);
    assert p eq q^2;
    return q;
end function;

function adjust_subscheme_poly(pol,E)
//pol is (x-c)*q(x)^2 where c is the x-coord of a 2-torsion pt and the
// subgroup scheme of E is defined by (x-c)*q(x)
    p2 := Parent(pol)!DivisionPolynomial(E,2);
    p2 := GCD(pol,p2);
    assert Degree(p2) eq 1;
    q := MonicPolSqrt(pol div p2);
    return p2*q;
end function;

function crv_mp_to_ff_map(phi)
    C1 := Domain(phi);
    C := Codomain(phi);
    FC := FunctionField(C);
    KC,mpC := AlgorithmicFunctionField(FC);
    Fgens := gen_seq(KC);
    FC1 := FunctionField(C1);
    KC1,mpC1 := AlgorithmicFunctionField(FC1);
    if Rank(CoordinateRing(Ambient(C))) eq 2 then //P^1
	booP1 := true;
	gen1 := KC1!(Fgens[1]);
	Remove(~Fgens,1);
    else
	booP1 := false;
    end if;

    Ca := AffinePatch(C, FFPatchIndex(C));
    C1a := AffinePatch(C1, FFPatchIndex(C1));
    rat_ff := [mpC1(FC1.i) : i in [1..Length(C1a)]];
    ff_rat := [Index(seq,s): s in [mpCi(f) : f in Fgens]] where
	mpCi is Inverse(mpC) where seq is [FC.i : i in [1..Length(Ca)]];
    assert &and[i gt 0 : i in ff_rat];

    // get corr. ff_map_ims using stripped down version of Pullback
    phi_aff := RestrictionToPatch(phi,FFPatchIndex(C1),FFPatchIndex(C));
    ff_map_ims := [coerce_to_ff(eqns[i],rat_ff) : i in ff_rat] where
			eqns is DefiningEquations(phi_aff);
    if booP1 then 
	ff_map_ims := [gen1] cat ff_map_ims cat [gen1];
    end if;    
    // and make AlFF morphism from it
    boo,mp,msg := HasMorphismFromImages(FunctionFieldCategory())
			(KC, KC1, ff_map_ims);
    assert boo;
    return mp;
end function;

function j_invt(X0Ndata)
// compute the rational function on X0(N) giving the j-invariant
   N := X0Ndata`N;
   C := X0Ndata`X0N;
   A := Ambient(C);
   if N eq 1 then
      return A.1,A.2;	
   end if;
   fs := Factorisation(N);
   p := fs[#fs][1];//fs[1][1];
   if N eq p then
	_,E4,E6 := Explode(X0Ndata`Es);
	E4 := E4[1]/E4[2];
	E6 := E6[1]/E6[2];
	j := (1728*E4^3)/(E4^3-E6^2);
	jn := Numerator(j); jd := Denominator(j);
   else
	j1n,j1d := j_invt(Create_SmallCrvMod_Structure(N div p));
	prj := [e[2] : e in (X0Ndata`prjs) | e[1] eq p][1];
	jn := Evaluate(j1n,prj); jd := Evaluate(j1d,prj);
   end if;
   typ := Type(C);
   if Rank(CoordinateRing(A)) eq 2 then
      if N eq p then
        return Homogenization(Evaluate(jn,[A.1]),A.2,p+1),Homogenization(Evaluate(jd,[A.1]),A.2,p+1);
      else
	g := GCD(jn,jd);
	return (jn div g),(jd div g);
      end if;    
   end if;
   //j := jn/jd;
   //jf := F!j;
   if ISA(typ,CrvEll) or ISA(typ,CrvHyp) then
      F := FunctionField(C);
      K,fmp := AlgorithmicFunctionField(F);
      jf := F!(jn/jd);
      jr := FunctionFieldEvaluation(fmp(jf),[A.1/A.3,A.2/(A.3^w)])
	where w is VariableWeights(CoordinateRing(A))[2];
      return Numerator(jr),Denominator(jr);
   end if;
   g := GCD(jn,jd);
   if TotalDegree(g) gt 0 then
      jn := jn div g; jd := jd div g;
   end if;
   l := LCM([Denominator(c) : c in Coefficients(jn)] cat [Denominator(c) : c in Coefficients(jd)]);
   if l gt 1 then
      jn := l*jn; jd := l*jd;
   else
      g := GCD([Integers()!c : c in Coefficients(jn)] cat [Integers()!c : c in Coefficients(jd)]);
      if g gt 1 then
	jn := jn/g; jd := jd/g;
      end if;
   end if;
   // homogenise in the prime case
   if N eq p then
      R := CoordinateRing(A);
      n := Rank(R);
      d := Max([TotalDegree(f) : f in [jn,jd]]);
      if assigned X0Ndata`dif then //non-subhyp case
	i := n+1-(X0Ndata`dif)[1];	
      else
	i := n;	
      end if;
      if i eq n then 
        jn,jd := Explode([Polynomial(Coefficients(f),[Monomial(R,es cat [d-&+es])
	  where es is Exponents(ms) : ms in Monomials(f)]) : f in [jn,jd]]);
      else
        jn,jd := Explode([Polynomial(Coefficients(f),[Monomial(R,es[1..i-1] cat [d-&+es] cat es[i..n-1])
	  where es is Exponents(ms) : ms in Monomials(f)]) : f in [jn,jd]]);
      end if; 
   end if;
   return jn,jd;
   /*d := 1;
   repeat
      dens := DenomsOfDegree(jf,C,d);
      d +:= 1;
   until #dens gt 0;
   den := dens[#dens];
   num := RatFnNum(j,den,Ideal(C));
   return num,den;*/ 
end function;

function j_invt_pt(pt,X0Ndata)
// j(pt) for pt non-cuspidal in X0N(K), pt not a singular point on the model
    N := X0Ndata`N;
    if N eq 1 then
      return Eltseq(pt)[1];	
    end if;
    K := Ring(Parent(pt));
    fs := Factorisation(N);
    p := fs[#fs][1];//fs[1][1];
    if N eq p then
	_,E4,E6 := Explode(X0Ndata`Es);
	//R := CoordinateRing(Ambient(Scheme(pt)));
	//n := Rank(R);
	//seq := Eltseq(pt);
        if assigned X0Ndata`dif then //non-subhyp case
	  i := (X0Ndata`dif)[1];	
        else
	  i := 1;	
        end if;
	CN := Scheme(pt);
	P1 := ProjectiveSpace(K,1);
        seq := InverseDefiningPolynomials(ProjectiveClosureMap(Ambient(AffinePatch(CN,i))));
	E4n,E4d,E6n,E6d := Explode([Evaluate(f,seq) : f in [E4[1],E4[2],E6[1],E6[2]]]);
	j_mp := map<CN->P1|[1728*u,u-E4d^3*E6n^2]> where u is E4n^3*E6d^2;
	jn,jd := Explode(DefiningPolynomials(j_mp));
	seq := Eltseq(pt);
	jd1 := Evaluate(jd,seq);
	if jd1 ne 0 then
	    return Evaluate(jn,seq)/jd1;
	else
	    _,pti := InternalCurveMapAtPoint(j_mp,pt);
	    return e[1]/e[2] where e is Eltseq(pti);
	end if;		
    else
	X0Md := Create_SmallCrvMod_Structure(N div p);
	CN := Scheme(pt);
	CM := (K cmpeq Rationals()) select X0Md`X0N else BaseChange(X0Md`X0N,K);
	eqns := [e[2] : e in (X0Ndata`prjs) | e[1] eq p][1];
	prj := map<CN->CM|[R!e : e in eqns] : Check:= false> where 
	   R is CoordinateRing(Ambient(CN));
	return j_invt_pt(prj(pt),X0Md);
    end if;    
end function;

function j_N_pt(pt,X0Ndata)
// j(N*pt) for pt non-cuspidal in X0N(K), pt not a singular point on the model
    wN_eqs := (X0Ndata`ALs)[#(X0Ndata`ALs)];
    CN := Scheme(pt);
    R := CoordinateRing(Ambient(CN));
    wN := iso<CN->CN|seq,seq : Check := false> where
	seq is [R!e : e in wN_eqs];
    pt1 := wN(pt);
    return j_invt_pt(pt1,X0Ndata);
end function;

function j_invt_pl(pl,X0Ndata)
// j(pl) for pl non-cuspidal place of X0N
    jn,jd := j_invt(X0Ndata);
    CN := Curve(pl);
    R := CoordinateRing(Ambient(CN));
    jn,jd := Explode([R!f : f in [jn,jd]]);
    F := FunctionField(CN);
    _,fmp := AlgorithmicFunctionField(F);
    j := F!(jn/jd);
    _,rmp := ResidueClassField(pl);
    return rmp(fmp(j));
end function;

function j_N_pl(pl,X0Ndata)
// j(Nz) evaluated at pl, non-cuspidal place of X0N
    jn,jd := j_invt(X0Ndata);
    CN := Curve(pl);
    R := CoordinateRing(Ambient(CN));
    jn,jd := Explode([R!f : f in [jn,jd]]);
    F := FunctionField(CN);
    _,fmp := AlgorithmicFunctionField(F);
    j := fmp(F!(jn/jd));
    wN := (X0Ndata`ALs)[#(X0Ndata`ALs)];
    wN := map<CN->CN|[R!e : e in wN] : Check := false>;
    wN := crv_iso_to_ff_map(CN,[wN])[1];
    _,rmp := ResidueClassField(pl);
    return rmp(wN(j));
end function;

function projection(X0Ndata,CN,M,CM)
// for M|N, CN and CM are base changes of XN and XM to the same field extension of Q.
//  returns the natural projection map CN->CM

    N := X0Ndata`N;
    //M := X0Mdata`N;
    K := BaseRing(CN);
    assert K eq BaseRing(CM);
    if M eq 1 then 
      jn,jd := j_invt(X0Ndata);
      return map<CN->CM|[R!jn,R!jd]> where R is CoordinateRing(Ambient(CN));
    end if;
    fs := Factorisation(N div M);
    ps := &cat[[f[1] : i in [1..f[2]]] : f in fs];
    Reverse(~ps);
    eqns := [e[2] : e in (X0Ndata`prjs) | e[1] eq ps[1]][1];
    N1 := N;
    for i in [2..#ps] do
	N1 := N1 div ps[i-1];
	rN := Create_SmallCrvMod_Structure(N1);
	eqns1 := [e[2] : e in (rN`prjs) | e[1] eq ps[i]][1];
	eqns := [Evaluate(e,eqns) : e in eqns1];
    end for;
    prj := map<CN->CM|[R!e : e in eqns] : Check := false> 
		where R is CoordinateRing(Ambient(CN));
    return prj;
end function;

function projection_r(X0Ndata,CN,X0Mdata,CM,r)
// for M|N, r|(N/M), CN and CM are base changes of XN and XM to the same field extension of Q.
//  returns the projection map CN->CM that corr to z -> rz

    N := X0Ndata`N;
    M := X0Mdata`N;
    K := BaseRing(CN);
    assert K eq BaseRing(CM);
    M1 := N div r;
    if M1 ne M then
	rM1 := Create_SmallCrvMod_Structure(M1);
	CM1 := rM1`X0N;
	if not K cmpeq Rationals() then
	  CM1 := BaseChange(CM1,K);
	end if;
    else
	CM1 := CM;
	rM1 := X0Mdata;
    end if;
    mp1 := map<CN->CN|[R!e : e in (X0Ndata`ALs)[#(X0Ndata`ALs)]] : Check := false>
	where R is CoordinateRing(Ambient(CN));
    mp2 := projection(X0Ndata,CN,M1,CM1);
    mp3 := map<CM1->CM1|[R!e : e in (rM1`ALs)[#(rM1`ALs)]] : Check := false>
	where R is CoordinateRing(Ambient(CM1));
    if M1 eq M then
	return mp1*mp2*mp3;
    else
	mp4 := projection(rM1,CM1,M,CM);
	return mp1*mp2*mp3*mp4;
    end if;
end function;

function E46frm(CN,X0Ndata,ks)
// returns f,w where f is a rational function on CN and w is a differential s.t.
// Ek is f*w^(k/2) as a (k/2)-differential where k is 4 or 6

    N := X0Ndata`N;
    if N eq 1 then
	Eks := [(X0Ndata`Es)[(k eq 4) select 2 else 3] : k in ks];
	Ra := CoordinateRing(Ambient(AffinePatch(CN,1)));
	F := FunctionField(CN);
	return [F!((Ra!(Ek[1]))/(Ra!(Ek[2]))) : Ek in Eks], -Differential(F.1);
    end if;
    fs := Factorisation(N);
    ps := &cat[[f[1] : i in [1..f[2]]] : f in fs];
    p := ps[#ps];
    if N ne p then
      Xdp := Create_SmallCrvMod_Structure(p);
      K := BaseRing(CN);
      Cp := (K cmpeq Rationals()) select Xdp`X0N else BaseChange(Xdp`X0N,K);
      prj := projection(X0Ndata,CN,p,Cp);
    else
      Xdp := X0Ndata;
      Cp := CN;
    end if;
    Eks := [(Xdp`Es)[(k eq 4) select 2 else 3] : k in ks];
    if assigned Xdp`dif then //non-subhyp case
      i := (Xdp`dif)[1];
      j := (Xdp`dif)[2];	
    else
      i := 1; j := 1;	
    end if;
    Cpa := AffinePatch(Cp,i);
    Ra := CoordinateRing(Ambient(Cpa));
    if assigned Xdp`dif then //non-subhyp case
      difr := (Ra!(d[3])/Ra!(d[4])) where d is Xdp`dif;	
    else
      if Rank(Ra) eq 1 then // genus 0
	difr := Ra!(-1);
      elif Type(Cp) eq CrvEll then
	difr := -1/(2*Ra.2+a[1]*Ra.1+a[3]) where a is aInvariants(Cp);
      else //Type(Cp) eq CrvHyp
	_,h := HyperellipticPolynomials(Cp);
	difr := -1/(2*Ra.2+Evaluate(h,Ra.1));
      end if;	
    end if;
    F := FunctionField(CN);
    if N ne p then
	CNa := AffinePatch(CN,FFPatchIndex(CN));
	eqns1 := DefiningPolynomials(ProjectiveClosureMap(Ambient(CNa)));
	eqns := [Evaluate(e,eqns1) : e in DefiningPolynomials(prj)];
	eqns := [Evaluate(e,eqns) : e in DefiningPolynomials(Inverse(
			ProjectiveClosureMap(Ambient(Cpa))))];
	Ekfs := [F!(Evaluate(Ek[1],eqns)/Evaluate(Ek[2],eqns)) : Ek in Eks];
	dif1 := F!(Evaluate(difr,eqns));//F!(Evaluate(Numerator(difr),eqns)/Evaluate(Denominator(difr),eqns));
	dif2 := F!(eqns[j]);	
    else
	Ekfs := [F!((Ra!(Ek[1]))/(Ra!(Ek[2]))) : Ek in Eks];
	dif1 := F!difr;
	dif2 := F!(Ra.j);
    end if;
    d := dif1*Differential(dif2);
    return Ekfs,d;
    
end function;

function E2prfrm(Cpr,X0prd,p,r,boow)
// auxiliary prime power function: returns a Alff differential w on Cpr (level p^r) s.t. w is equal to 
// the weight 2 form E2pr = p^rE2(p^rz)-E2(z) as a meromorphic differential on CN. boow is true iff
// the actual w_{p^r} (on the AlFF of Cpr) is needed as a return value

    K := BaseRing(Cpr);
    if r eq 1 then
	C := Cpr; X := X0prd;
    else
	X := Create_SmallCrvMod_Structure(p);
	C := ((K cmpeq Rationals()) select X`X0N else BaseChange(X`X0N,K));
    end if;
    F := FunctionField(C);	
    E2 := (X`Es)[1];
    if assigned X`dif then //non-subhyp case
      i := (X`dif)[1];
      j := (X`dif)[2];	
    else
      i := 1; j := 1;	
    end if;
    Ca := AffinePatch(C,i);
    Ra := CoordinateRing(Ambient(Ca));
    if assigned X`dif then //non-subhyp case
      difr := (Ra!(d[3])/Ra!(d[4])) where d is X`dif;	
    else
      if Rank(Ra) eq 1 then // genus 0
	difr := Ra!(-1);
      elif Type(C) eq CrvEll then
	difr := -1/(2*Ra.2+a[1]*Ra.1+a[3]) where a is aInvariants(C);
      else //Type(C) eq CrvHyp
	_,h := HyperellipticPolynomials(C);
	difr := -1/(2*Ra.2+Evaluate(h,Ra.1));
      end if;	
    end if;	
    E2 := F!((difr*(Ra!(E2[1])))/(Ra!(E2[2])));
    dif1 := Differential(F!((K!GCD(24,p-1))*Ra.j));
    u := FunctionFieldDifferential(E2*dif1);
    v := u;
    if boow or (r gt 1) then
      w := (X`ALs)[#(X`ALs)];
      w := map<C->C|[R!e : e in w] : Check := false> where 
			R is CoordinateRing(Ambient(C));
      w := crv_iso_to_ff_map(C,[w])[1];
    else
      w := 0;
    end if;

    // loop to go recursively from p to p^r
    for i in [2..r] do
	if i eq r then
	  X := X0prd; C1 := Cpr;
	else
	  X := Create_SmallCrvMod_Structure(p^i);
	  C1 := ((K cmpeq Rationals()) select X`X0N else BaseChange(X`X0N,K));
	end if;
        w1 := (X`ALs)[#(X`ALs)];
        w1 := map<C1->C1|[R!e : e in w1] : Check := false> where
			R is CoordinateRing(Ambient(C1));
        w1 := crv_iso_to_ff_map(C1,[w1])[1];
	prj := projection(X,C1,p^(i-1),C);
	prj := crv_mp_to_ff_map(prj);
	s := SeparatingElement(AlgorithmicFunctionField(FunctionField(C)));
	ds := Differential(s);
	u := prj(u/ds)*Differential(prj(s));
	v1 := (w1(prj(w(v/ds))))*Differential(w1(prj(w(s))));
	v := u+v1;
	C := C1; w := w1;
    end for;
    return v,w;
   
end function;
 
function E2Nfrm(CN,X0Ndata)
// returns a differential Alff w on CN s.t. w is equal to the weight 2 form E2N = NE2(Nz)-E2(z)
// as a meromorphic differential on CN

    N := X0Ndata`N;
    if N eq 1 then
	F := AlgorithmicFunctionField(FunctionField(CN));
	return Differential(F!0);
    end if;
    fs := Factorisation(N);
    if #fs eq 1 then
	d := E2prfrm(CN,X0Ndata,fs[1][1],fs[1][2],false);
	return d;
    end if;
    pdata := [**];
    K := BaseRing(CN);
    for pr in fs do
	p := pr[1]; r := pr[2];
	Xprd := Create_SmallCrvMod_Structure(p^r);
	Cpr := ((K cmpeq Rationals()) select Xprd`X0N else BaseChange(Xprd`X0N,K));
	d,w := E2prfrm(Cpr,Xprd,p,r,true);
	Append(~pdata,<p^r,Cpr,d,w>);
    end for;

    ob := pdata[1];
    C := ob[2]; u := ob[3];
    M := ob[1];
    Remove(~pdata,1);
    for ob in pdata do
	M1 := M*(ob[1]);
	if M1 eq N then
	  X := X0Ndata;
	  C1 := CN;
	else
	  X := Create_SmallCrvMod_Structure(M1);
	  C1 := ((K cmpeq Rationals()) select X`X0N else BaseChange(X`X0N,K));
	end if;
        w1 := (X`ALs)[#(X`ALs)];
        w1 := map<C1->C1|[R!e : e in w1] : Check := false> where
			R is CoordinateRing(Ambient(C1));
        w1 := crv_iso_to_ff_map(C1,[w1])[1];
	prj1 := projection(X,C1,M,C);
	prj1 := crv_mp_to_ff_map(prj1);
	prj2 := projection(X,C1,ob[1],ob[2]);
	prj2 := crv_mp_to_ff_map(prj2);
	s := SeparatingElement(AlgorithmicFunctionField(FunctionField(C)));
	ds := Differential(s);	
	u1 := prj1(u/ds)*Differential(prj1(s));
	s := SeparatingElement(AlgorithmicFunctionField(FunctionField(ob[2])));
	ds := Differential(s); wpr := ob[4];	
	v1 := w1(prj2(wpr(ob[3]/ds)))*Differential(w1(prj2(wpr(s))));
	u := u1+/*M**/v1;
	M := M1; C := C1;	
    end for;
    return u;

end function;

function get_Ei_p1_pl(p,X0Ndata)
// p is a non-cuspidal place on CN, a base change of X0(N). Returns E4(L),E6(L),p1(L),E4(L1),E6(L1)
// lying in the residue class field K of p. L,L1 are lattices s.t. all terms lie in K and
// C/L -> C/L1, z -> z,  is a cyclic N-isogeny in the I.M. class of p

    CN := Curve(p);
    e2 := E2Nfrm(CN,X0Ndata);
    e46,dif := E46frm(CN,X0Ndata,[4,6]);
    v := Valuation(dif,p);
    if v ne 0 then
	tp := UniformizingParameter(p);
	u := tp^v;
	dif := (1/u)*dif;
	e46 := [e46[i]*u^(i+1) : i in [1..2]];
    end if;
    if (Valuation(e46[1],p) ne 0) or (Valuation(e46[2],p) ne 0) then
	error "Sorry, can't handle the j=0 or 1728 cases yet";
    end if;    
    N := X0Ndata`N;
    wN := (X0Ndata`ALs)[#(X0Ndata`ALs)];
    wN := map<CN->CN|[R!e : e in wN] : Check := false> where
			R is CoordinateRing(Ambient(CN));
    wN := crv_iso_to_ff_map(CN,[wN])[1];
    K,rmp := ResidueClassField(p);
    AF,fmp := AlgorithmicFunctionField(FunctionField(CN));
    e4,e6 := Explode([fmp(e) : e in e46]);
    s := SeparatingElement(AF);
    dif1 := fmp(dif/Differential(Inverse(fmp)(s)));
    dif2 := Differential(s);   
    p1 := (N/12)*rmp((1/dif1)*(e2/dif2));
    e4f := rmp(e4);
    e6f := rmp(e6);
    dif1N := wN(dif1);
    dif2N := Differential(wN(s));
    fN := (dif1N/dif1)*(dif2N/dif2);
    e4Nf := N^2*rmp(wN(e4)*fN^2);
    e6Nf := N^3*rmp(wN(e6)*fN^3);
    return [p1,e4f,e6f,e4Nf,e6Nf];

end function;    

function get_Ei_p1_pl_with_E(p,X0Ndata,c4,c6)
// as above except twist the final values so that e4f=c4, e6f=c6. c4,c6 should be coercible
// into the residue field of p and be c4,c6 invariants of a curve with j-inv j(p)

    vs := get_Ei_p1_pl(p,X0Ndata);
    K := Universe(vs);
    c4 := K!c4; c6 := K!c6;
    u := (c6*vs[2])/(c4*vs[3]);
    assert c4 eq vs[2]*u^2;
    return [u*vs[1],c4,c6,u^2*vs[4],u^3*vs[5]];

end function;

function E_and_G_pl(p,X0Ndata)
// for p a non-cuspidal place on CN (a base change of X0(N) to char 0), get a corresponding elliptic
// curve E and N-cyclic subgroup G over the res fld of p that are in the p isomorphism class

    vs := get_Ei_p1_pl(p,X0Ndata);
    E1 := EllipticCurve([-3*vs[2],-2*vs[3]]);
    E2 := EllipticCurve([-3*vs[4],-2*vs[5]]);
    K := Universe(vs);
    N := X0Ndata`N;
    boo := IsEven(N);
    p1 := (boo select 12 else 6)*vs[1];
    if K cmpeq Rationals() then
      _,d := MinimalQuadraticTwist(E1);
      E1 := EllipticCurve([-3*d^2*vs[2],-2*d^3*vs[3]]);
      E2 := EllipticCurve([-3*d^2*vs[4],-2*d^3*vs[5]]);
      p1 := d*p1;
    end if;
    pol := ElkiesKernel(E1,E2,N,p1);
    if boo then
      pol := adjust_subscheme_poly(pol,E1);
    end if;
    if K cmpeq Rationals() then //use minimal model
	E,mp := MinimalModel(E1);
	r,_,_,u := Explode(IsomorphismData(mp));
	if (r ne 0) or (u^2 ne 1) then
	  pol := Evaluate(pol,(x-r)/u^2)*u^(2*Degree(pol)) where x is Parent(pol).1;
	end if;
	E1 := E;
    end if;
    return E1,SubgroupScheme(E1,pol);

end function;

function G_pl(p,X0Ndata,E)
// for p a non-cuspidal place on CN (a base change of X0(N) to char 0), E should be an elliptic
// curve E over a subfield of the res fld of p K with j(E)=j(p). Returns the N-cyclic subgroup
// G of the base change of E to K s.t. (E,G) is represented by p on X0(N)

    vs := get_Ei_p1_pl(p,X0Ndata);
    K := Universe(vs);
    KE := BaseField(E);
    boo := (KE cmpeq Rationals());
    if not boo then
      if not (K cmpeq Rationals()) then
	boo := IsSubfield(KE,K);
      end if;
    end if;	  
    error if not boo,"The basefield of the elliptic curve should be",
     "a subfield of the residue field of the place/point";
    if not (KE cmpeq K) then
	E := BaseChange(E,K);
    end if;
    c4,c6 := Explode(cInvariants(E));
    u := (c6*vs[2])/(c4*vs[3]);
    assert c4 eq vs[2]*u^2;
    vs := [u*vs[1],c4,c6,u^2*vs[4],u^3*vs[5]];
    E1 := EllipticCurve([-c4/48,-c6/864]);
    _,mp1 := IsIsomorphic(E,E1);
    E2 := EllipticCurve([-vs[4]/48,-vs[5]/864]);
    N := X0Ndata`N;
    boo := IsEven(N);
    p1 := boo select vs[1] else vs[1]/2;            
    pol := ElkiesKernel(E1,E2,N,p1);
    if boo then
      pol := adjust_subscheme_poly(pol,E1);
    end if;    
    r := IsomorphismData(mp1)[1]; // u^2 must be 1 here (j != 0,1728)
    if r ne K!0 then
      pol := Evaluate(pol,x+r) where x is Parent(pol).1;
    end if;    
    return SubgroupScheme(E,pol);

end function;

intrinsic ProjectionMap(CN::Crv, N::RngIntElt, CM::Crv, M::RngIntElt) -> MapSch
{ Returns the modular curve projection map CN -> CM corresponding to z -> z on the upper half-plane. 
  CN,CM should be base changes to a field extension of Q of the curves from the X0N small modular curve
  database of level N,M}

    require (N gt 0) and (M gt 0): "N and M should be positive integers";
    require IsDivisibleBy(N,M) : "Level M should divide level N";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      X0Mdata := Create_SmallCrvMod_Structure(M);
    catch e
      error e`Object;
    end try;
    require BaseRing(CN) eq BaseRing(CM):
	"The curve arguments should be defined over the same base field";
    if N eq M then
	return iso<CN->CM|seq,seq> where seq is [R.i : i in [1..Rank(R)]]
		where R is CoordinateRing(Ambient(CN));
    end if;
    return projection(X0Ndata,CN,M,CM);

end intrinsic;

intrinsic ProjectionMap(CN::Crv, N::RngIntElt, CM::Crv, M::RngIntElt, r::RngIntElt) -> MapSch
{ Returns the modular curve projection map CN -> CM corresponding to z -> rz on the upper half-plane 
  where 0 < r|(M/N). CN,CM should be base changes to a field extension of Q of the curves from the X0N small
  modular curve database of level N,M}

    require (N gt 0) and (M gt 0): "N and M should be positive integers";
    require IsDivisibleBy(N,M) : "Level M should divide level N";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      X0Mdata := Create_SmallCrvMod_Structure(M);
    catch e
      error e`Object;
    end try;
    require BaseRing(CN) eq BaseRing(CM):
	"The curve arguments should be defined over the same base field";
    require (r gt 0) and IsDivisibleBy(N div M,r) : 
	"r should be a positive divisor of the quotient of levels N/M";
    if N eq M then
	return iso<CN->CM|seq,seq> where seq is [R.i : i in [1..Rank(R)]]
		where R is CoordinateRing(Ambient(CN));
    end if;
    return projection_r(X0Ndata,CN,X0Mdata,CM,r);

end intrinsic;

intrinsic jInvariant(CN::Crv, N::RngIntElt) -> FldFunRatMElt
{ Returns the j-invariant of CN, a base change of the curve from the X0N small modular curve database
  of level N, as a rational function on its ambient }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    num,den := j_invt(X0Ndata);
    num,den := Explode([R!num,R!den]) where R is CoordinateRing(Ambient(CN));
    return num/den;

end intrinsic;

intrinsic jFunction(CN::Crv, N::RngIntElt) -> FldFunFracSchElt
{ Returns the j-invariant of CN, a base change of the curve from the X0N small modular curve database
  of level N, as a rational function in its function field }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    num,den := j_invt(X0Ndata);
    num,den := Explode([R!num,R!den]) where R is CoordinateRing(Ambient(CN));
    F := FunctionField(CN);
    return F!(num/den);

end intrinsic;

intrinsic jInvariant(p::Pt, N::RngIntElt) -> RngElt
{ p should be a non-cuspidal point on a base change of the curve from the X0N small modular curve database
  of level N. Returns the value of the j-invariant j(z) at p }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_point(p,X0Ndata);
      require not boo: "p should not be a cusp";
      return j_invt_pt(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;

end intrinsic;

intrinsic jNInvariant(p::Pt, N::RngIntElt) -> RngElt
{ p should be a non-cuspidal point on a base change of the curve from the X0N small modular curve database
  of level N. Returns the value of the j(Nz) function at p }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_point(p,X0Ndata);
      require not boo: "p should not be a cusp";
      return (N eq 1) select j_invt_pt(p,X0Ndata) else j_N_pt(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;

end intrinsic;

intrinsic jInvariant(p::PlcCrvElt, N::RngIntElt) -> RngElt
{ p should be a non-cuspidal place on a base change of the curve from the X0N small modular curve database
  of level N. Returns the value (in the residue field of p) of the j-invariant at p }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
      require not boo: "p should not be a cusp";
      return j_invt_pl(p,X0Ndata);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;

end intrinsic;

intrinsic jNInvariant(p::PlcCrvElt, N::RngIntElt) -> RngElt
{ p should be a non-cuspidal place on a base change of the curve from the X0N small modular curve database
  of level N. Returns the value (in the residue field of p) of the j(Nz) at p }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
      require not boo: "p should not be a cusp";
      return (N eq 1) select j_invt_pl(p,X0Ndata) else j_N_pl(p,X0Ndata);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;

end intrinsic;

intrinsic E2NForm(CN::Crv, N::RngIntElt) -> DiffCrvElt
{ Returns the differential form that corresponds to the weight 2 form NE2(Nz)-E2(z) on CN, a base
  change of the curve from the X0N small modular curve database of level N }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    dif := E2Nfrm(CN,X0Ndata);
    return CurveDifferential(CN,dif);

end intrinsic;

intrinsic E4Form(CN::Crv, N::RngIntElt) -> FldFunFracSchElt, DiffCrvElt
{ Returns a rational function f and a differential form w of CN, a base change of the curve from the X0N
  small modular curve database of level N, such that the E4 2-differential on CN is f*w^2 }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    Es,d := E46frm(CN,X0Ndata,[4]);
    return Es[1],d;

end intrinsic;

intrinsic E6Form(CN::Crv, N::RngIntElt) -> FldFunFracSchElt, DiffCrvElt
{ Returns a rational function f and a differential form w of CN, a base change of the curve from the X0N
  small modular curve database of level N, such that the E6 3-differential on CN is f*w^3 }

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    Es,d := E46frm(CN,X0Ndata,[6]);
    return Es[1],d;

end intrinsic;

intrinsic SubgroupScheme(p::Pt, N::RngIntElt) -> SchGrpEll, CrvEll
{ For p a non-singular, non-cuspidal point on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero, returns a pair G,E where E is an elliptic
  curve and G is a subgroup scheme giving a cyclic subgroup of order N, both defined over the
  field of p, such that (E,G) is in the isomorphism class represented by the moduli point p on X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    require IsNonSingular(p) : "p must be a non-singular point";
    try
      boo := is_a_cusp_point(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    K := Ring(Parent(p));
    CN := Scheme(p);
    if not (K cmpeq BaseRing(CN)) then
	CN := BaseChange(CN,K);
	p := CN!Eltseq(p);
    end if;
    pl := Place(p);
    E,G := E_and_G_pl(pl,X0Ndata);
    return G,E;
   
end intrinsic;

intrinsic SubgroupScheme(p::PlcCrvElt, N::RngIntElt) -> SchGrpEll, CrvEll
{ For p a non-cuspidal place on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero, returns a pair G,E where E is an elliptic
  curve and G is a subgroup scheme giving a cyclic subgroup of order N, both defined over the residue
  field of p, such that (E,G) is in the isomorphism class represented by the moduli place p of X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
      require not boo: "p should not be a cusp";
      E,G := E_and_G_pl(p,X0Ndata);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;
    return G,E;
   
end intrinsic;

intrinsic SubgroupScheme(p::Pt, N::RngIntElt, E::CrvEll) -> SchGrpEll
{ p should be a non-singular, non-cuspidal point on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero. E should be an elliptic curve defined over
  a subfield of the field K of p with j(E)=j(p)!=0,1728. Returns a subgroup scheme G of E (or the base change of E
  to K) such that G gives a cyclic subgroup of order N, and (E,G) is in the isomorphism class represented by
  the moduli point p on X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    require IsNonSingular(p) : "p must be a non-singular point";
    try
      boo := is_a_cusp_point(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    K := Ring(Parent(p));
    CN := Scheme(p);
    if not (K cmpeq BaseRing(CN)) then
	CN := BaseChange(CN,K);
	p := CN!Eltseq(p);
    end if;
    pl := Place(p);
    try
      G := G_pl(pl,X0Ndata,E);
    catch e
      error e`Object;
    end try;    
    return G;
   
end intrinsic;

intrinsic SubgroupScheme(p::PlcCrvElt, N::RngIntElt, E::CrvEll) -> SchGrpEll
{ p should be a non-cuspidal place on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero. E should be an elliptic curve defined over
  a subfield of the residue field K of p with j(E)=j(p)!=0,1728. Returns a subgroup scheme G of E (or the base
  change of E to K) such that G gives a cyclic subgroup of order N, and (E,G) is in the isomorphism class
  represented by the moduli place p of X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    try
      G := G_pl(p,X0Ndata,E);
    catch e
      error e`Object;
    end try;    
    return G;
   
end intrinsic;

intrinsic Isogeny(p::Pt, N::RngIntElt) -> MapSch
{ For p a non-singular, non-cuspidal point on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero, returns a cyclic N-isogeny between
  elliptic curves phi:E->F where E,F,phi are all defined over the field of p and such that
  the isomorphism class of [E,F,phi] is represented by the moduli point p on X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    require IsNonSingular(p) : "p must be a non-singular point";
    try
      boo := is_a_cusp_point(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    K := Ring(Parent(p));
    CN := Scheme(p);
    if not (K cmpeq BaseRing(CN)) then
	CN := BaseChange(CN,K);
	p := CN!Eltseq(p);
    end if;
    pl := Place(p);
    E,G := E_and_G_pl(pl,X0Ndata);
    _,phi := IsogenyFromKernel(G);
    return phi;
   
end intrinsic;

intrinsic Isogeny(p::PlcCrvElt, N::RngIntElt) -> MapSch
{ For p a non-cuspidal place on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero, returns a cyclic N-isogeny between
  elliptic curves phi:E->F where E,F,phi are all defined over the residue field of p and such that
  the isomorphism class of [E,F,phi] is represented by the moduli place p of X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
      require not boo: "p should not be a cusp";
      E,G := E_and_G_pl(p,X0Ndata);
      _,phi := IsogenyFromKernel(G);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;
    return phi;
   
end intrinsic;

intrinsic Isogeny(p::Pt, N::RngIntElt, E::CrvEll) -> MapSch
{ p should be a non-singular, non-cuspidal point on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero. E should be an elliptic curve defined over
  a subfield of the field K of p with j(E)=j(p)!=0,1728. Returns a cyclic N-isogeny between
  elliptic curves phi:E1->F where E1 is the base change of E to K, F and phi are defined over K and such that
  the isomorphism class of [E,F,phi] is represented by the moduli point p on X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    require IsNonSingular(p) : "p must be a non-singular point";
    try
      boo := is_a_cusp_point(p,X0Ndata);
    catch e
      error "p doesn't appear to be a point on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    K := Ring(Parent(p));
    CN := Scheme(p);
    if not (K cmpeq BaseRing(CN)) then
	CN := BaseChange(CN,K);
	p := CN!Eltseq(p);
    end if;
    pl := Place(p);
    try
      G := G_pl(pl,X0Ndata,E);
    catch e
      error e`Object;
    end try;
    _,phi := IsogenyFromKernel(G);
    return phi;   
   
end intrinsic;

intrinsic Isogeny(p::PlcCrvElt, N::RngIntElt, E::CrvEll) -> MapSch
{ p should be a non-cuspidal place on CN, a base change of the curve from the X0N small modular
  curve database of level N to a field of characteristic zero. E should be an elliptic curve defined over
  a subfield of the residue field K of p with j(E)=j(p)!=0,1728. Returns a cyclic N-isogeny between
  elliptic curves phi:E1->F where E1 is the base change of E to K, F and phi are defined over K and such that
  the isomorphism class of [E,F,phi] is represented by the moduli place p of X0(N)}

    require N gt 0: "N should be a positive integer";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    try
      boo := is_a_cusp_place(p,X0Ndata);
    catch e
      error "p doesn't appear to be a place on the small X0(",N,") model";
    end try;
    require not boo: "p should not be a cusp";
    try
      G := G_pl(p,X0Ndata,E);
    catch e
      error e`Object;
    end try;    
    _,phi := IsogenyFromKernel(G);
    return phi;   
   
end intrinsic;

