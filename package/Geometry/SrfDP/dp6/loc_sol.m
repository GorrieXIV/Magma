freeze;

/*
      Functions to determine local solubility at all places of
	simple and simultaneous norm equations arising from
	  the homogeneous spaces of 2-D tori over numberfields.
		mch - 05/06.
*/

function MyCompletion(K,p,prec)
/* 
  K is an absolute extension of Q and p a prime ideal of MaximalOrder(K).
  Function returns the p-Adic completion K_p AS A FINITE PRECISION
  pAdic ring, precision ep*max(Ceiling(prec/ep),2) where ep is the
  ramification index of p.
*/
    ep := RamificationIndex(p);
    prec1 := Max(Ceiling(prec/ep),2);
    Kp,mpK := Completion(K,p : Precision := ep*prec1);
    Qp := pAdicField(Prime(Kp),prec1);

    //special case where Kp = Qp - but usually described as an unramified
    // extension  of degree 1 of Qp!
    if Degree(Kp) eq 1 then
	el := (BaseField(Kp) eq Kp) select Qp!mpK(K.1) else
			Qp!(BaseField(Kp)!mpK(K.1));
	return Qp,hom<K->Qp|el>;
    end if;

    //get the sequence of subfields of Kp - should
    // be either 1 or 2 before reaching base padic field
    seq := [* Kp *];
    L := Kp;
    while Degree(L) gt 1 do
	L := BaseField(L);
	Append(~seq,L);
    end while;
    assert seq[#seq] eq BaseField(seq[#seq]);

    L := Qp;
    mp := map<seq[#seq]->Qp | x :-> Qp!x>;
    for i := #seq-1 to 1 by -1 do
	K1 := seq[i];
	assert HasDefiningMap(K1); //K1 should be an unbounded prec extn
	L1 := ext<L | PolynomialRing(L)!([mp(c) : c in Coefficients(
		DefiningPolynomial(K1))])>;
	mp1 := map<K1->L1 | x :-> &+[mp(c[i])*L1.1^(i-1) : i in [1..#c]]
			where c is Coefficients(x)>;
	L := L1; mp := mp1;
    end for;
    return L,hom<K->L|mp(mpK(K.1))>;

end function;

function reexpress(a,b)
// K/k a finite field extn K=k(b) and a in K. returns the
//  sequence of elts a_i s.t. a = a_1+a_2*b+..
    K := Parent(b);
    k := BaseField(K);
    n := Degree(K)-1;
    if a in k then 
	return [k!a] cat [k|0 : i in [1..n]];
    end if;
    M := Matrix([Eltseq(b^i) : i in [0..n]]);
    return Eltseq(Vector(Eltseq(a))*(M^-1));
end function;

function Deg6LocCheck(Kp,K_mp,pe,pf,a,b,Eram,Fram)

    Fp := ext<Kp|PolynomialRing(Kp)![K_mp(c) : c in
			Coefficients(MinimalPolynomial(pf))]>;
    F_mp := map<Parent(b)->Fp | x :-> K_mp(c[1])+K_mp(c[2])*Fp.1 where
		 	c is reexpress(x,pf)>;
    bp := F_mp(b);
  
    Ep := ext<Kp|PolynomialRing(Kp)![K_mp(c) : c in
			Coefficients(MinimalPolynomial(pe))]>;
    E_mp := map<Parent(a)->Ep | x :-> K_mp(c[1])+K_mp(c[2])*Ep.1+
		K_mp(c[3])*Ep.1^2 where c is reexpress(x,pe)>;
    ap := E_mp(a);

    if Eram and Fram then
	// uniformiser of Lp is pf/pe
	w,v,u := Explode(Coefficients(MinimalPolynomial(pe)));
	Lp := ext<Fp|PolynomialRing(Fp)!
		[F_mp(pf^3/w),F_mp((u/w)*pf^2),F_mp((v/w)*pf),1]>;
	typ := 1;
    elif Eram then
	Lp := ext<Fp|PolynomialRing(Fp)![F_mp(c) : c in
			Coefficients(MinimalPolynomial(pe))]>;
	typ := 2;
    else
	Lp := ext<Ep|PolynomialRing(Kp)![E_mp(c) : c in
			Coefficients(MinimalPolynomial(pf))]>;
	typ := 3;
    end if;
    UL, mUL := UnitGroup(Lp);
    UE, mUE := UnitGroup(Ep);
    UF, mUF := UnitGroup(Fp);

    case typ:

	when 1:
	NF := hom<UL->UF | [ Norm(UL.i@mUL, Fp)@@mUF : i in [1..Ngens(UL)]]>;
	f := Precision(Kp);
	pi := Ep!(ChangePrecision(Norm(Fp.1),f))/Ep.1^2;
	pi1 := pi*Ep.1;
	pf1 := Fp!Trace(Fp.1)-Fp.1;
	norm_E := function(x)
	    u,v,w := Explode(Eltseq(x));
	    tu := Trace(u);
	    tv := ChangePrecision(Trace(v/pf1),f);
	    tw := Trace(w/pf1^2);
	    return Norm(u)+Norm(v)*pi+Norm(w)*pi^2+
		(tu*tv-ChangePrecision(Trace(u*v/pf1),f))*pi1+
		(tu*tw-Trace(u*w/pf1^2))*pi1^2+
		(tv*tw-Trace(v*w/pf1^3))*pi1^3;
	end function;
	NE := hom<UL->UE | [ norm_E(UL.i@mUL)@@mUE : i in [1..Ngens(UL)]]>;
	delete norm_E;

        when 2:
	NF := hom<UL->UF | [ Norm(UL.i@mUL, Fp)@@mUF : i in [1..Ngens(UL)]]>;
	pi := Ep.1;
	norm_E := map<Lp->Ep | x :-> 
		Norm(u)+(tu*tv-Trace(u*v))*pi+(Norm(v)+tu*tw-Trace(u*w))*pi^2+
		(tv*tw-Trace(v*w))*pi^3+Norm(w)*pi^4  where tu is Trace(u)
		where tv is Trace(v) where tw is Trace(w) where
		u,v,w := Explode(Eltseq(x))>;
	NE := hom<UL->UE | [ norm_E(UL.i@mUL)@@mUE : i in [1..Ngens(UL)]]>;
	delete norm_E;
	
	when 3:
	NE := hom<UL->UE | [ Norm(UL.i@mUL, Ep)@@mUE : i in [1..Ngens(UL)]]>;
	pi := Fp.1;
	norm_F := function(x)
	    u,v := Explode(Eltseq(x));
	    if IsWeaklyZero(u) then
		return Fp!Norm(v)*pi^3;
	    elif IsWeaklyZero(v) then
		return Fp!Norm(u);
	    else
		nu := Norm(u); nv := Norm(v);
		return Fp!nu + Fp!(nu*Trace(v/u))*pi + Fp!(nv*Trace(u/v))*pi^2 +
			(Fp!nv)*pi^3;
	    end if;
	end function;
	NF := hom<UL->UF | [ norm_F(UL.i@mUL)@@mUF : i in [1..Ngens(UL)]]>;
	delete norm_F;

    end case;

    S, iS, pS := DirectSum([UE, UF]);
    N := hom<UL -> S |
	[ iS[1](NE(UF.i)) + iS[2](NF(UF.i)) : i in [1..Ngens(UF)]]>;

    r := iS[1](ap@@mUE) + iS[2](bp@@mUF);
    return r in Image(N);

end function;

function RamLocCheck(Kp,comp_map,pe,bp)
    Ep := ext<Kp|PolynomialRing(Kp)![comp_map(c) : 
			c in Coefficients(MinimalPolynomial(pe))]>;
    return NormEquation(Ep,comp_map(bp));
end function;

function QuadCase(E,a,pE,pol,f)
    valn := Valuation(a,pE);
    if valn ne 0 then
	a := a/(Coefficient(pol,0)^valn);
    end if;
    if f eq 1 then // non-char 2 case - simple check
        res_fls,mp := ResidueClassField(MaximalOrder(E),pE);
	return IsSquare(mp(a));
    else // char 2 case - use IsLocallySolvable code for a conic
	n,t,_ := Explode(Coefficients(pol));
	P<x,y,z> := ProjectiveSpace(E,2);
	X := Scheme(P,x^2-t*x*y+n*y^2-a*z^2);
	return IsLocallySolvable(X,pE : AssumeIrreducible := true,
			AssumeNonsingular :=true);
    end if;
end function;

function RealCheck(K,us,vs,boo)
// K is an absolute number field (or Q) with us,vs in [K*].
//  returns whether for all real embeddings of K with every 
//  u>0(boo true) or for one real embedding of K with every
//  u>0(boo false), all of the vs are also positive
    if K cmpeq Rationals() then
    	if &or[u le 0: u in us] or &and[v gt 0 : v in vs] then
	  return boo;
	end if;
	return (not boo);
    end if;
    r_rts := RealRoots(MinimalPolynomial(K.1),RealField(),0.1);
    if #r_rts gt 0 then
	M := Max([Ceiling(Abs(r)) : r in r_rts]);
	p1s := [PolynomialRing(Rationals())!Eltseq(u) : u in us];
	p2s := [PolynomialRing(Rationals())!Eltseq(v) : v in vs];
	seq := [&+[i*Abs(Coefficient(p,i))*M^(i-1) : i in [1..Degree(p)]]
	  	: p in p1s cat p2s | Degree(p) gt 0];
	prec := (#seq eq 0) select 1 else Max(seq);
	prec := (prec le 1) select 50 else Ceiling(Log(10,prec)+5);
	prec := Max(prec,50);
	r_rts := RealRoots(MinimalPolynomial(K.1),RealField(prec),0.0001);
	for r in r_rts do
	    if &or[Evaluate(p1,r) le 0 : p1 in p1s] then continue; end if;
	    v1s := [Evaluate(p2,r): p2 in p2s];
	    if boo then
	      if &or[v1 le 0: v1 in v1s] then
		return false;
	      end if;
	    else
	      if &and[v1 gt 0: v1 in v1s] then
		return true;
	      end if;
	    end if;
	end for;
    end if;
    return boo;
end function;

function SimLocSolEverywhere(L,a,b)
/* 
   L is a number field - base field K and K <= E,F <= L are intermediate
   fields with a in E, b in F s.t. L=E.F, N_(E/K)(a)=N_(F/K)(b) &
   [E:K]=3, [F:K]=2.
   This function determines whether the simultaneous norm equations
   N_(L/E)(x)=a,N_(L/F)(x)=b are LOCALLY soluble for all places of K
   ( ie as norm equations between separable algebras )
*/

    E := Parent(a);
    F := Parent(b);
    K := BaseField(L);

    assert (K cmpeq Rationals()) or (BaseField(K) cmpeq Rationals());
		//: "Basefield K must be Q or an absolute extension of Q"
    assert IsSubfield(E, L); //: "a must be in a subfield of L";
    assert IsSubfield(F, L); //: "b must be in a subfield of L";
    assert BaseField(E) eq K;
    assert BaseField(F) eq K;
    assert (Degree(L) eq 6) and (Degree(E) eq 3) and (Degree(F) eq 2);


    //First determine for which places p of k the check needs to be made
    // - If either E or F is locally trivial over p then solubility is
    // immediate. If not, but both E & F are unramified over p then
    // the only check necessary is on the valuations of e & f - when
    // they are units at p then again solubity is immediate.
    nm := Norm(b);
    assert nm eq Norm(a);
    
    // Check at real infinite places that split completely
    // in E and ramify in F - condition is that a is totally +ive.
    //  Simple check: if x^3-u*x^2+v*x-w is the min poly of a over K then
    //   condn <=> u,v,w,disc(poly)>0 under each real embedding of k.
    //  norm(a)=norm(b) => w >0 so only need check u,v (&disc(poly)).
    w := Norm(F.1)-Trace(F.1)^2; //-discriminant of F/K
    m := MinimalPolynomial(a);
    d := Discriminant(m);
    if (Degree(m) eq 3) and
     (not RealCheck(K,[w,d],[-Coefficient(m,2),Coefficient(m,1)],true)) then
	return false;
    end if;

    denoms := (b in K select [K|] else [Trace(b)]) cat
		(a in K select [K|] else [Trace(a),(1/2)*(Trace(a)^2-Trace(a^2))]);
    denoms := [den : den in denoms | den notin MaximalOrder(K)];
    dE := Discriminant(MaximalOrder(E));
    dF := Discriminant(MaximalOrder(F));
    if K cmpeq Rationals() then
	ramE := Seqset(PrimeDivisors(Integers()!dE));
        ramF := Seqset(PrimeDivisors(Integers()!dF));
	ab_pls := Seqset(PrimeDivisors(Numerator(nm))) join
			Seqset(PrimeDivisors(Denominator(nm)));
	if #denoms gt 0 then
	    ab_pls join:=
		&join[Seqset(PrimeDivisors(Denominator(den))) : den in denoms];
	end if;
    else
	ramE := Support(dE);
	ramF := Support(dF);
	ab_pls := Support(nm*MaximalOrder(K));
	if #denoms gt 0 then
	    ab_pls join:=
		&join[Support(GCD(K!1*O,den*O)) : den in denoms] where
			O is MaximalOrder(K);
	end if;
    end if;
    rams := ramE join ramF;
     
    // deal with unramified places first
    for p in ab_pls do
    /*
        if p is unramified in L then an analysis of cases & the
	global equality N_(E/K)(a)=N_(F/K)(b) show that we have local
        solvability of the equations automatically unless either
	1) p splits in F & remains prime in E - the condition is then
	   that the valuation of b is divisible by 3 at one (& hence
	   both) of the places of F over p.
	2) p splits completely in E & remains prime in F - the condition
	   is then that the valuation at a is even at any two (& hence
	   also the 3rd) of the places of E over p.
    */
	if p in rams then continue; end if;
	pF := DecompositionType(MaximalOrder(F),p);
	if #pF eq 2 then        // p splits in F
	    if #DecompositionType(MaximalOrder(E),p) eq 1 then
		if Valuation(b,Decomposition(MaximalOrder(F),p)[1][1]) mod 3 ne 0 then
		    return false;
		end if;
	    end if;
	else                   // p remains prime in F
	    pE := DecompositionType(MaximalOrder(E),p);
	    if #pE eq 3 then
		pE := Decomposition(MaximalOrder(E),p);
		if IsOdd(Valuation(a,pE[1][1])) or
		   IsOdd(Valuation(a,pE[2][1])) then
		    return false;
		end if;
	    end if;
	    delete pE;
	end if;
    end for;

    // now deal with the ramified places
    for p in rams do

	ap := a; bp := b;
	nm_p := (K cmpeq Rationals()) select p else NormAbs(p);
	over2,over3 := Explode([IsEven(nm_p),(nm_p mod 3) eq 0]);
	Epls := DecompositionType(MaximalOrder(E),p);
	Fpls := DecompositionType(MaximalOrder(F),p);
	rE := #[1 : q in Epls | q[2] gt 1] gt 0;
	rF := #[1 : q in Fpls | q[2] gt 1] gt 0;
	assert (rE or rF);
	if (#Epls eq 1) and (#Fpls eq 1) then
	  // one place, w, of L over K - must check sim. local norm eqn.
	  // can do this working at precision e*f in L_w (after replacing
	  // a & b by a/N(y), b/N(y) for suitable y in L so they are units
	  // at w) where e is the ramification index of w/p and f is the
	  // conductor of L_w/F_p ( smallest f>=1 st all units in F_p
	  // = 1 mod p^f are norms from L_w )
	    e := (rE select 1 else 3) * (rF select 1 else 2);
	    if over2 and rF then
		if rE then
		    f := 3*Valuation(dF,p)-2;
		else
		    f := Valuation(dE,p);
		end if;
	    elif over3 and rE then
		if rF then 
		    f := Valuation(dF,p)-1;
		else
		    f := Valuation(dF,p);
		    assert IsEven(f);
		    f div:= 2;
		end if;
	    else
		f := 1;
	    end if;
	    // build the base field K_pt to the correct precision
	    if K cmpeq Rationals() then
		K_p,comp_map := Completion(K,ideal<Integers()|p> :
			Precision := Max([2,f]));
	    else
		K_p,comp_map := MyCompletion(K,p,f);
	    end if;
            // find a uniformiser over p in L, normalise a & b
	    // to be units over p by norms
	    if rE and rF then // totally ramified case
		pE := Decomposition(MaximalOrder(E),p)[1][1];
		pF := Decomposition(MaximalOrder(F),p)[1][1];
		pe := E!UniformizingElement(pE);
		pf := F!UniformizingElement(pF);
		// Uniformizer in L will be L!pf/L!pe;
		valn := Valuation(b,pF);
		if valn ne 0 then
			bp := b * (F!Norm(pe)/pf^3)^valn;
			ap := a * (pe^2/E!Norm(pf))^valn;
		end if;
	    elif rE then // E/K tot ram and F/K degree 2 unramified
		pE := Decomposition(MaximalOrder(E),p)[1][1];
		pe := E!UniformizingElement(pE);
		// Uniformizer in L will be L!pe
		valn := Valuation(a,pE);
		assert IsEven(valn);
		if valn ne 0 then
			bp := b / (F!Norm(pe))^(valn div 2);
			ap := a / (pe^valn);
		end if;
		pF := Decomposition(MaximalOrder(F),p)[1][1];
		pf := F!Inverse(rm)(rf.1) where 
				rf,rm := ResidueClassField(pF);
	    else   // F/K tot ram and E/K degree 3 unramified
		pF := Decomposition(MaximalOrder(F),p)[1][1];
		pf := F!UniformizingElement(pF);
		// Uniformizer in L will be L!pf
		valn := Valuation(b,pF);
		assert (valn mod 3) eq 0;
		if valn ne 0 then
			bp := b / (pe^valn);
			ap := a / (E!Norm(pe)^(valn div 3));
		end if;
		pE := Decomposition(MaximalOrder(E),p)[1][1];
		pe := E!Inverse(rm)(rf.1) where 
				rf,rm := ResidueClassField(pE);
	    end if;
	    // now check local solubility.
	    if false then//not Deg6LocCheck(K_p,comp_map,pe,pf,ap,bp,rE,rF) then
		return false;
	    end if;
	elif rE and (#Epls eq 1) then
	  // p tot ram in E and splits in F.
	  //  here the check is that the single norm equation from
	  //  Ep to Kp N(x)=b1 is soluble where b1 is EITHER of the
	  //  images of b under the 2 K-embeddings F -> Kp.
	    if over3 then
		f := Valuation(dE,p);
		assert IsEven(f);
		f div:= 2;
	    else
		f := 1;
	    end if;
	    // build the base field K_pt to the correct precision
	    if K cmpeq Rationals() then
		K_p,comp_map := Completion(K,ideal<Integers()|p> :
			Precision := Max([2,f]));
	    else
		K_p,comp_map := MyCompletion(K,p,f);
	    end if;
	    pE := Decomposition(MaximalOrder(E),p)[1][1];
	    pe := E!UniformizingElement(pE);
	    pk := Norm(pe);
	    valn := Min([Valuation(b,pf[1]) : pf in 
			Decomposition(MaximalOrder(F),p)]);
	    if valn ne 0 then
		bp := b/F!(pk^valn);
	    end if;
	    rts := Roots(MinimalPolynomial(bp),K_p);
	    if #rts eq 1 then
		bp := rts[1][1];
	    else
		bp := [rt[1] : rt in rts | Valuation(rt[1]) eq 0][1];
	    end if;
	    // now check local solubility.
	    if not RamLocCheck(K_p,comp_map,pe,bp) then
		return false;
	    end if;
	elif rE then
	  // p=q^2*r in E
	  //  here, if p splits in F then local solubility is automatic.
	  //  if p ramifies or is inert in F loc sol <=> ap in Eq is a
	  //   norm from Eq.Fp - when Eq.Fp/Eq is unram, this is just equiv
	  //   to val(a,q) [ or val(a,r) ] = 0 mod 2
	  pE := [pr[1] : pr in Decomposition(MaximalOrder(E),p)|pr[2] eq 2][1];
	  if rF and over2 then // if not over2 then EqFp/Eq is unramified 
	    pol := PolynomialRing(E)!MinimalPolynomial(
		 F!UniformizingElement(Decomposition(MaximalOrder(F),p)[1][1]));
	    if not QuadCase(E,a,pE,pol,Valuation(dF,p)) then
		return false;
	    end if;
	  elif #Fpls eq 1 then
	    if IsOdd(Valuation(a,pE)) then
	      if not rF then return false; end if;
	      // if Fp ramified, must check if Eq.Fp/Eq is trivial or not.
	      //  if u is a uniformiser of q & v of p(F), min poly of v
	      //  factors as x^2+Bu^2x-Cu^2 over Eq for C a unit
	      //  and Eq=Fp iff C mod p(F) is a square.
	      pF := Decomposition(MaximalOrder(E),p)[1][1];
	      pol := PolynomialRing(E)!MinimalPolynomial(
		 				F!UniformizingElement(pF));
	      pe := E!UniformizingElement(pE);
	      _,rmp := ResidueClassField(pE);
	      if not IsSquare(rmp(-Coefficient(pol,0)/(pe^2))) then
		return false;
	      end if;
	    end if;
	  end if;
	else
	  // p unramified in E and ramified in F
	  //  1) p splits completely in E - loc sol <=> solubility of any TWO
	  //  of the single norm eqns N_(Fp/Kp)(x)=ai where a1,a2,a3 are the
	  //  three images of a under the embeddings E -> Kp
	  //  2) p=qr in E with deg(q/p)=2,deg(r/p)=1 - loc sol <=> ap in Eq
	  //  is a local norm from Fp.Eq
	    f := over2 select Valuation(dF,p) else 1;
	    pol := PolynomialRing(E)!MinimalPolynomial(
		 F!UniformizingElement(Decomposition(MaximalOrder(F),p)[1][1]));
	    if #Epls eq 3 then
		pEs := [pr[1] : pr in Decomposition(MaximalOrder(E),p)];
		boo := QuadCase(E,a,pEs[1],pol,f) and QuadCase(E,a,pEs[2],pol,f);
	    else
		assert #Epls eq 2;
		pE := [pr[1] : pr in Decomposition(MaximalOrder(E),p) | 
				Degree(pr[1]) gt 1][1];
		boo := QuadCase(E,a,pE,pol,f);
	    end if;
	    if not boo then return false; end if;
	end if;

    end for;

    return true;

end function; 

function LocSolEverywhereDeg2(L,a)
// L is a quadratic extension of K (both number fields) and a in K*
// determines whether a is locally a norm from L to K at all places

    K := Parent(a);
    assert (K eq Rationals()) or ISA(Type(K),FldNum);
    assert BaseField(L) eq K;
    assert Degree(L) eq 2;

    e := Trace(L.1);
    f := Norm(L.1);
    b := ((e/2)^2)-f;
    if K cmpeq Rationals() then
    // Use quaternion algebras over Q <-> Hilbert symbols
    //  x^2-ay^2=b has a soln <=> algebra (a,b) is split.
	b := Numerator(b)*Denominator(b);
	a := Numerator(a)*Denominator(a);
	ram := RamifiedPrimes(QuaternionAlgebra<K|b,a>);
	return (#ram eq 0);
    else
    // Over a numberfield, the same is true, but we use
    // Nils' local solubility code here [should switch to
    // quat algebra code over numflds at some point!] over
    // 2.
      //first check real places
	K1 := AbsoluteField(K);
	a1 := -K1!a; b1 := -K1!b;
	if RealCheck(K1,[a1],[b1],false) then
	    return false;
	end if;
      //then finite ones
	ab_places := Support(2*MaximalOrder(K)) join 
		Support(a*MaximalOrder(K)) join Support(b*MaximalOrder(K));
	for p in ab_places do
	    if IsEven(NormAbs(p)) then  // primes over 2
		u := a/(K!UniformizingElement(p))^Valuation(a,p);
		if not QuadCase(K,u,p,PolynomialRing(K)![f,e,1],2) then
		    return false;
		end if;
	    else
		vala := Valuation(a,p);
		valb := Valuation(b,p);
		if IsEven(valb) then
		    if IsOdd(vala) then
		      u := b/(K!UniformizingElement(p))^valb;
		    else
		      continue;
		    end if;
		else
		    pi_p := -b/(K!UniformizingElement(p))^(valb-1);
		    u := a/pi_p^vala;
		end if;
		k,mp := ResidueClassField(p);
		if not IsSquare(mp(u)) then
		    return false;
		end if;
	    end if;
	end for;
	return true;
    end if;

end function;

function LocSolEverywhereDeg3(L,a)
// L is a cubic extension of K (both number fields) and a in K*
// determines whether a is locally a norm from L to K at all places

  // no checks are necessary at the infinite places and the only
  // other non-trivial ones are at places ramified at L/K and those
  // dividing a. For the unramified places, the checks reduce to
  // simple valuation checks.
    K := Parent(a);
    assert (K cmpeq Rationals()) or ISA(Type(K),FldNum);
    assert BaseField(L) eq K;
    assert Degree(L) eq 3;

    dL := Discriminant(MaximalOrder(L));
    if K eq Rationals() then
        rams := Seqset(PrimeDivisors(Integers()!dL));
	a_pls := Seqset(PrimeDivisors(Numerator(a))) join
			Seqset(PrimeDivisors(Denominator(a)));
    else
	rams := Support(dL);
	a_pls := Support(a*MaximalOrder(K));
    end if;
    
    // deal with unramified places first
    for p in a_pls do
	if p in rams then continue; end if;
	pL := DecompositionType(MaximalOrder(L),p);
	if #pL eq 1 then        // p remains prime in F
	    //condition is that valn(a,p) = 0 mod 3
	    if (Valuation(a,p) mod 3) ne 0 then
		return false;
	    end if;
	end if;
    end for;

    // now deal with the ramified places
    for p in rams do
	nm_p := (K cmpeq Rationals()) select p else NormAbs(p);
	over2,over3 := Explode([IsEven(nm_p),(nm_p mod 3) eq 0]);
	f := Valuation(dL,p);
	// p factors as q1*q2^2 with q1,q2 deg 1 is trivial
	if (over2 and (f ge 3)) or (f eq 1) then
	    continue;
	end if;
	// tot ram case
	if over3 then
	    f -:=1; // max possible precision needed for check
	else
	    f := 1;
	end if;
	// build the base field K_pt to the correct precision
	if K cmpeq Rationals() then
	    K_p,comp_map := Completion(K,ideal<Integers()|p> :
			Precision := Max([2,f]));
	else
	    K_p,comp_map := MyCompletion(K,p,f);
	end if;
	pL := Decomposition(MaximalOrder(L),p)[1][1];
	pl := L!UniformizingElement(pL);
	pk := Norm(pl);
	ap := a/(pk^Valuation(a,p));
	// now check local solubility.
	if not RamLocCheck(K_p,comp_map,pl,ap) then
	    return false;
	end if;
    end for;
    return true;

end function;
