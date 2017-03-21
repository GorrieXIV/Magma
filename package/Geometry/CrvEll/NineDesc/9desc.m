freeze;

/*
9descent.m
Brendan Creutz
version June 2011


This contains the implementation of 3-descent on a plane cubic C 
when the action of Galois on the flex points of C is transitive. 
If the action is not transitive, then one can perform a second 
3-isogeny descent (also implemented).

*/

declare verbose NineDescent, 3;

import "Getell.m": ComputeL_TransitiveCase;
import "Getell.m": FlexPoints;
import "Getell.m": DescentMapForm;

QQ := Rationals();
ZZ := Integers();
GF3 := GF(3);

/*
The functions here are used to find a 'random' Qp-point on C (assuming that C in fact has Qp point. These have been replace by IsLocallySoluble()

FindFpPoint := function(f,p,nonzero);
// For a polynomial f in three variables, this finds a random solution to f = 0 mod p.
//If no solution exists, or the function fails to find one after 500 tries, then
//"Can't find any Fp points" is returned.
//if nonzero is set to true, then the solution of the form (0,0,0) is excluded from consideration.
ZZ<X,Y,Z> := PolynomialRing(ZZ,3);
GFp := GF(p);
FpPol := PolynomialRing(GFp,3);
f := ZZ! f;
fp := FpPol!f;
tries := 0;
while tries lt 500 do
	PT := [Random(GFp), Random(GFp)];
	evalf := Evaluate(fp,[FpPol.1,PT[1],PT[2]]);
	if evalf eq 0 then
		Pt := [ZZ!Random(GFp),ZZ!PT[1],ZZ!PT[2]];
		if nonzero then
			if Pt ne [0,0,0] then
				return Pt;
			end if;
		else
			return Pt;
		end if;
	else
		Fevalf := Factorization(evalf);
		for h in Fevalf do
			if Degree(h[1],1) eq 1 then
				root := -Coefficient(h[1],1,0);
				Pt := [ZZ!root,ZZ!PT[1],ZZ!PT[2]];
				if nonzero then
					if Pt ne [0,0,0] then
						return Pt;
					end if;
				else return Pt;
				end if;
			end if;
		end for;
	end if;
	tries +:=1;
end while;
return "can't find any Fp points";
end function;

LiftPoint:= function(p,f,Pt,prec);
//Given a solution Pt to f(Pt) = 0 mod p^prec, this function attempts to lift Pt to a solution to f = 0 mod p^(prec+1).  
//If we fail to find a lift after the number of tries specified in FindFpPoint, "can't lift" is returned.

if prec eq 0 then
	return FindFpPoint(f,p,true);
else
	R := PolynomialRing(QQ,3:Global);
	fnext := Evaluate(f,[(Pt[i]+p^prec*R.i) : i in [1..3]]);
	fnext := (1/p^prec)*fnext;
	fnextPoint := FindFpPoint(fnext,p,false);
	if Type(fnextPoint) eq MonStgElt then
		return "can't lift";
	else
		return [ p^prec*fnextPoint[i] + Pt[i] : i in [1..#Pt] ];
	end if;
end if;
end function;

HenselInfo := function(f,PT,p);
// This is just Hensels lemma.  The return value M is such that there exists a Qp solution P to f = 0, such that P 
//reduces to PT mod p^M.  If Hensel's lemma does not apply, then this number is 0.

Derivs := [Derivative(f,i) : i in [1..3]];
value := Evaluate(f,PT);
if PT ne [0,0,0] and value eq 0 then
	return "Is Rational";
else
if IsZero(value) then
  n := -1;
else
  n := Valuation(value,p);
end if;

k := Min({Valuation(Evaluate(g,PT),p) : g in Derivs});
if k lt 0 then
	return 0;
else
	return Max({0,n-k});
end if;
end if;
end function;

ApplyInfo := function(Pt,p,f)
//This just returns the reduction of Pt mod p^M where M is the number coming from Hensel's lemma above.
M := HenselInfo(f,Pt,p);
if Type(M) eq MonStgElt then
	return Pt, "is Rational";
end if;
return  [Pt[i] mod p^(M) : i in [1..#Pt] ], M;
end function;

FindQpPoint := function(f,p,Prec);
//This attempts to find a Qp solution to f = 0 up to precision Prec.
//1) Find Pt a solution mod p.
//2) Lift Pt to get solutions Ptn mod p^n for n = 2,3,...,N until
//	a) Hensel's lemma ensures that there is a Qp point reducing to PtN mod p^Prec, or
//	b) we can no longer lift.  In this apply Hensel's lemma to find m such that there is a Qp point reducing to PtN mod p^m.  Then we repeat 2) with Pt = Ptm.
if Type(f) ne RngMPolElt then
	f := DefiningEquation(f);
end if;
Pt := [0,0,0];
prec := 0;
M := 0;
while M le Prec do
	nM := HenselInfo(f,Pt,p);
	if  Type(nM) eq MonStgElt then
		return Pt;
	end if;
	nPt := LiftPoint(p,f,Pt,prec);
	if Type(nPt) eq MonStgElt then
		Pt, prec := ApplyInfo(Pt,p,f);
		M := HenselInfo(f,Pt,p);
	else
		prec +:= 1;
		Pt := nPt;
		M := nM;
	end if;
end while;
return Pt;
end function;
*/

QpPointOnRandomHyperplane := function(C,p : Precision := 100)
// Calls IsLocallySolvable - may result in error...
// Finds a 'random' Q_p-point on C (not deterministic)

eqs := DefiningEquations(C);
BP := AmbientSpace(C);
q := Dimension(BP)+1;
Zp2 := Integers(p^2);
LocPoint := false;
Z := Integers();

while not LocPoint do

Hyperplane := &+[ (ZZ!Random(Zp2))*BP.i : i in [1..q] ];
HypSlice := Scheme(BP, [ Evaluate(f,[BP.i : i in [1..q]]) : f in eqs] cat [Hyperplane]);

  if Dimension(HypSlice) eq 0 then
    try
      LocPoint, Pt := IsLocallySolvable(HypSlice,p);
    catch err
      LocPoint := false;
      vprintf NineDescent: "NineSelmerSet: error in IsLocallySolvable:\n%o\n", err`Object;
    end try;
  end if;

end while; //LocPoint

Qp := pAdicField(p,2*Precision);
Pt := C(Qp)!Pt;
Pt := LiftPoint(Pt,Precision);

Pt := [QQ!c : c in Eltseq(Pt)];
d := LCM([Denominator(co) : co in Pt]);
Pt := [ZZ!d*co : co in Pt];

return Pt;
end function;


NineD := function(C,Models,ExtraReduction);

E := Jacobian(C);
vprintf NineDescent, 1: "Doing 3-descent on %o.\n", C;

vprintf NineDescent, 2: "\nComputing algebras, constants and the descent map.\n";
Points, Fields := FlexPoints(C);
PT := Points[1];
error if #Points ne 1, "Galois does not act transitively on the flex points. Try calling pIsogDescent() instead.\n";
K := Fields[1];
O := MaximalOrder(K);
dO := Discriminant(O);
T,S_T,c := DescentMapForm(C,PT);
//Make integral and remove cubes from c.
den_c := Denominator(c);
for p in Factorization(den_c) do
  c *:= p[1]^(3*(p[2]+2 div 3));
end for;
for p in Factorization(ZZ!c) do
  c *:= p[1]^(-3*(p[2] div 3));
end for;
Cm := GenusOneModel(C);
S_C := {p[1] : p in Factorization(ZZ!Discriminant(Cm)) };
S_c := {p[1] : p in Factorization(ZZ!c)};
S_K := {p[1] : p in Factorization(ZZ! dO) | IsRamified(p[1],O) };
S := Setseq(S_T join S_c join S_C join S_K );
//Bad primes for the descent.
vprintf NineDescent, 1: "Flex algebra: K = %o.\nDiscriminant(O_K) = %o.\nConstant from norm condition: c = %o.\nBad primes: S = %o.\n", K,Discriminant(O),c,S;
f := DefiningEquation(C);
Kc,Mc,MoverKc,MoverLc,Lc,ell,N1,beta,ellInMoverK,Ntildez,genericZ := ComputeL_TransitiveCase(C,Points,Fields,<T>);
Np := map< K -> Lc | x :-> N1(<x>) >;
nL := NumberOfComponents(Lc);

error if nL ne NumberOfComponents(MoverLc), "M and L have different number of factors -Not yet implemented in this case.\n";

vprintf NineDescent, 2: "Lines algebra: L = %o.\n", Lc;
vprintf NineDescent, 3: "Constant from the second norm condition is beta = %o.\n", beta;
vprintf NineDescent, 3: "Lines and points algebra: M = %o.\n",Mc;
vprintf NineDescent, 3: "MoverK = %o.\nMoverL = %o.\n", MoverKc,MoverLc;
vprintf NineDescent, 1: "Now computing KS3/QS3.\n";

KS3c,KtoKS3, respFields, respGrps, KptoKpS3s :=  LocalGlobalSelmerDiagram(K,c,S,3);
/*
KtoKS3  is the map K to the abstract group K(S,3)/Q(S,3)
KptoKp3s are the maps K_p -> K_p* /Q_p*K_p*3
KS3c[1] is the norm defined on K(S,3)/Q(S,3).
KS3c[2] is an element of norm c mod Q*2
respFields are the maps K -> K \otimes K_p for the primes in S
respGrps are the corresponding maps K(S,3)/Q(S,3) to the local versions at p in S
*/
KS3 := Domain(KS3c[1]);
if #KS3c[2] eq 0 then
  vprintf NineDescent, 1: "Norm condition is not satisfied ==> Selmer set is empty.\n";
  return [];
end if;
alpha_c := Random(KS3c[2]) @@ KS3c[1];//elelment of norm c;
KS3toK := Inverse(KtoKS3);
KernelNorm := Kernel(KS3c[1]);
vprintf NineDescent, 1: "{ d in KS3/QS : N(d) = c Q*3 } has dimension %o.\n", #Generators(KernelNorm);

//Next step is to get our hands of L, N' and beta.

dimXp := function(p);
// Computes the dimension of the Q_p-rational flexes (as affine space for E[p]).
  decompp := Decomposition(K,p);
  size := #{ q : q in decompp | Degree(q[1])*q[2] eq 1 };
  if size eq 0 then return -1; end if;
  return Ilog(3,size);
end function;

dimLocalImage := function(p);
  // Computes the dimension of the local image of the (full) descent map.
  E3 := ThreeTorsionPoints(E);
  size := 1;
  for P in E3 do
    k := Ring(Parent(P));
    if k cmpeq QQ then
      size +:= 1;
    else
      decompp := Decomposition(k,p);
      size +:= #{ q : q in decompp | Degree(q[1])*q[2] eq 1 };
    end if;
  end for;
  if p eq 3 then return 1 + Ilog(3,size); end if;
  return Ilog(3,size);
end function;


PreimsOfLocalIms := <KernelNorm,alpha_c>;

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
    dif := hom< VW -> KS3 | [ -p1(VW.i) : i in [1..#Generators(V1)] ] cat [ p2(VW.i) : i in [#Generators(V1)+1..#Generators(VW)] ] >;
    if HasPreimage(v1-v2, dif) then
      alpha := v1 + p1((v1-v2) @@ dif);
      return <V1 meet V2,alpha>;
    else
      return "empty";
    end if;
  end function;

S_reallybad := <>;


vprintf NineDescent, 1: "\nComputing local images of fake descent map.\n";
//LocalImageFakeDescentMap := function(p);
for p in S do
  Method := "LocSol";
  vprintf NineDescent,1: "\nComputing local data at p = %o.\n", p;
  d1 := dimXp(p);
  dim := dimLocalImage(p);
  LocallyInjective := true; // this may change...
  if d1 lt 0 and dim ne 0 then
    LocallyInjective := false; // might need full descent map.
    // LocalSelmerGroup := function(K,p,q);
    vprintf NineDescent, 2: "  dim X(Q_p) = %o. dim E(Q_p)/3E(Q_p) = %o.\n    ==> may need full descent map.\n", d1,dim;
    q := 3;
    pids := [ pid[1] : pid in Factorization(p*O)];
  
    injs := [];
    ress := [];
    Dim := 0;
  
    for pid in pids do
      K_p, inj := Completion(K,pid);
      pr := (p in {2,3}) select 1000 else 300;
      SetPrecision(K_p,pr);
      G,m := pSelmerGroup(q,K_p);
      injs cat:= [inj];
      ress cat:= [m];
      Dim +:= #Generators(G);
    end for;
  
    A := FreeAbelianGroup(Dim);
    G := quo<A | [ q*A.i : i in [1..Dim]]>;
    dima := 0;
    lis := [];
    for i in [1..#injs] do
      G_i := Codomain(ress[i]);
      lis cat:= [hom< G_i -> G | [G.(i+dima) : i in [1..#Generators(G_i)]] >];
      dima +:= #Generators(G_i);
    end for;
  
    ModqthPowers := map< CartesianProduct([K_p : K_p in [ Domain(m) : m in ress]]) -> G | x :-> &+[ lis[i](ress[i](x[i])) : i in [1..#ress] ]>;
    KtoKp := map< K -> Domain(ModqthPowers) | x :-> < injs[i](x) : i in [1..#injs] > >;
    Kp := Codomain(KtoKp);
    pr := (p in {2,3}) select 500 else 300;
    // pr should be worked out rigoursly!
    Modcubes := ModqthPowers;
    Kpmodcubes := Codomain(Modcubes);
    // We need to mod out by the image of Qp* / Qp*q as well.
    H,mp := pSelmerGroup(3,Completion(QQ,p));
    GensQp := [ QQ!(g @@ mp) : g in Generators(H) ];
    Qpabs := AbelianGroup([3 : i in [1..#GensQp]]);
    imQp := hom< Qpabs -> Kpmodcubes | [Modcubes(KtoKp(GensQp[i])) : i in [1..#GensQp] ]>;
    Gp,mapa := quo<Kpmodcubes|Image(imQp)>;
    KptoGp := Modcubes*mapa;
    
    GetEquivalenceKp3 := function(d1,d2);
      // given d1, d2 in K* such that they have the same image in Kp* / Qp*Kp*3, we find a in Q and q in Kp such that d1 = d2*a*q^3
      D1 := Modcubes(KtoKp(d1));
      D2 := Modcubes(KtoKp(d2));
      a := (D1 - D2);
      if not a in Image(imQp) then
        return "","";
      end if;
      a := (D1 - D2) @@ imQp;
      a := &*[GensQp[i]^(Eltseq(a)[i]) : i in [1..#GensQp] ];
      q3 := d1/(d2*a);
      return a,q3;
    end function;

    FindCubeRootInKp := function(q3,K,p);
      /* We assume this is a cube in Kp, we want to find a cube root up to some precision.
      For any prime v | p the valuation of cube should be a multiple of 3.
      */
      q3 := KtoKp(q3);
      assert Parent(q3) eq Kp;
      val := 10;
      q := <>;
      for i in [1..NumberOfComponents(Kp)] do
        q3i := q3[i];
        kp := Kp[i];
        R := PolynomialRing(kp);
        qi := Roots(R.1^3-q3i);
        assert #qi gt 0;
        qi := qi[1][1];
        val := Max(val,Valuation(qi));
        Append(~q,qi);
      end for;
      return Kp!q;
    end function;

    
    GetIntegralParts := function(a,O,K);
      n := Degree(K);
      M := KMatrixSpace(K,n,n)!BasisMatrix(O);
      Kvsp, rep := KSpace(K,QQ);
      // Write a in terms of an integral basis:
      Ia := rep(a)*M^(-1);
      d := LCM([Denominator(b) : b in Eltseq(Ia)]);
      numa := O![d*b : b in Eltseq(Ia)];
      dena := O!d;
      return numa,dena;
    end function;

  
    WeakApprox := function(alpha,prec,INJS,pids);
      // alpha in < k_v : v in S > completions of k.
      // computes an element in k that is close (as specified by prec) to each alpha_v (assumed integral)
      kp := Parent(alpha);
      K := Domain(INJS[1]);
      numas := [];
      denas := [];
      pidns := [];
      for i in [1..#INJS] do
        alpha_v := alpha[i];
        res_v := INJS[i];
        k_v := kp[i];
        a_i := Inverse(res_v)(alpha_v);
        numa_i,dena_i := GetIntegralParts(a_i,O,K);
        numas cat:= [numa_i];
        denas cat:= [dena_i];
        prec +:= Valuation(res_v(K!dena_i));
        pidns cat:= [pids[i]^prec];
      end for;
      return K!CRT(numas,pidns)/ K!CRT(denas,pidns);
    end function;

    

    GetEta := function(de1,de2)
      /* Given P1,P2 in C which have the same image under the fake descent map 
      we have T(P1) = T(P2)aq^3, with a,q computed by the function above. 
      Since N'(T) = beta ell^3, there exists some eta in mu_3(L) st
      ell(P1) = eta*aN'(q)*ell(P2). Then T(P1) together with the class of eta
      determines the image of P2.
      */
      d1 := de1[1]; //in K
      d2 := de2[1]; //in K
      e1 := de1[2]; //in L
      e2 := de2[2]; //in L
      a,q3 := GetEquivalenceKp3(d1,d2);
      if Type(a) eq MonStgElt then
        return 1;
      end if;
      q := WeakApprox(FindCubeRootInKp(q3,K,p),pr,injs,pids);
      eta := < a*Np(q)[i]*e2[i]/e1[i] : i in [1..nL] >;
      return eta;
    end function;
    
    pidLcs := < [ f[1] : f in Factorization(p*MaximalOrder(Lc[i]))] : i in [1..nL] >;
    relevantpidLcs := <>;
    zetaLcpids := <>;
    resLcpids := <>;
    for i in [1..nL] do
      pidLs := pidLcs[i];
      relevantpidLs := [];
      zetaLpids := <>;
      resLpids := [];
      L := Lc[i];
      for pid in pidLs do
        Lpid,inj := Completion(L,pid);
        R := PolynomialRing(Lpid);
        rts := Roots(R.1^2+R.1+1);
        if #rts ge 1 then
          Append(~zetaLpids,rts[1,1]);
          resLpids cat:= [inj];
          relevantpidLs cat:= [pid];
        end if;
      end for;
      Append(~relevantpidLcs,relevantpidLs);
      Append(~zetaLcpids,zetaLpids);
      Append(~resLcpids,resLpids);
    end for;
    
    NpmuKp := [];
    for i in [1..#injs] do
      k_v := Codomain(injs[i]);
      R := PolynomialRing(k_v);
      rts := Roots(R.1^2+R.1+1);
      if #rts gt 0 then
        zeta_v := rts[1][1];
        zeta_vK := < 1 : j in [1..i-1] >;
        Append(~zeta_vK,zeta_v);
        for j in [i+1..#injs] do
          Append(~zeta_vK,1);
        end for;
        zeta_vK := WeakApprox(Kp!zeta_vK,100,injs,pids);
        NpmuKp cat:= [Np(zeta_vK)];
      end if;
    end for;
  
    muL := KSpace(GF3,&+[#zs : zs in zetaLcpids ]);
    
    ImEta1 := function(Eta);
      im := [];
      for i in [1..nL] do
        relevantpidLs := relevantpidLcs[i];
        resLpids := resLcpids[i];
        zetaLpids := zetaLcpids[i];
        eta := Eta[i];
        for j in [1..#relevantpidLs] do
          eta_v := resLpids[j](eta);
          vals := [Valuation(eta_v-1), Valuation(eta_v-zetaLpids[j]), Valuation(eta_v-zetaLpids[j]^2) ];
          assert #{v : v in vals | v gt 10 } eq 1;
          im cat:= [ GF3!a : a in [0..2] | vals[a+1] gt 10];
        end for;
      end for;
      return muL! im;
    end function;
    
    ImEta := map< Lc -> muL | x :-> ImEta1(x) >;
    NpmuKp := sub<muL|[ImEta(aa) : aa in NpmuKp]>;
    muLmodNp,mappa := quo<muL|NpmuKp>;
    if Dimension(muLmodNp) eq 0 then
      vprintf NineDescent, 2: "  dim mu(L)/N'(H^0(mu(Kbar)/mu)) = %o\n    ==> fake descent map injective.\n", Dimension(muLmodNp); 
      LocallyInjective := true;
    else
      vprintf NineDescent, 2: "  dim mu(L)/N'(H^0(mu(Kbar)/mu)) = %o\n    ==> may need full descent map.\n", Dimension(muLmodNp);  
    end if;
  end if; // d1 ne 0 and dim ne 0;


  if LocallyInjective then
    // fake descent map will be injective at p... we compute its image.
    vprintf NineDescent, 1: "  Computing image using fake descent map.\n";
    N := Index(S,p);
    KtoKp := respFields[N];
    mod_q := KptoKpS3s[N]; // K_p ---> K_p* / Q_p*K_p*q
    res_p := respGrps[N]; // K(S,q)/Q(S,q) --> K_p* / Q_p*K_p*q
    Gp := Codomain(res_p);
    pr := (p in {2,3}) select 500 else 300;
    // pr should be worked out rigoursly!
    vprintf NineDescent, 3: "  Searching for a Q_%o-point.\n",p;
    found := false;
    while not found do
      if Method eq "LocSol" then
        sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
        error if not sol, "C is not locally solvable at p = %o.\n";
      else
        R := QpPointOnRandomHyperplane(C,p : Precision := pr);
      end if;
	    R := [ QQ! R[i] : i in [1..3] ];
      if Valuation(Norm(Evaluate(T,R)),p) lt pr/4 then
	     found := true;
      end if;
    end while;
    TofR1 := mod_q(KtoKp(Evaluate(T,R)));
    vprintf NineDescent, 3: "  Found a Q_%o-point with image T_%o(R) = %o.\n",p, p, TofR1;
    LocalImage := < sub<Gp|0> , TofR1 >;
    tries := 0;
    while #Generators(LocalImage[1]) lt dim or tries lt 5 do
      found := false;
      if #Generators(LocalImage[1]) eq dim then
        vprintf NineDescent, 2: "  Local image found. Computing %o additional images to be safe.\n", 5-tries;
      end if;
      while not found do
        if Method eq "LocSol" then
          sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
          error if not sol, "C is not locally solvable at p = %o.\n";
        else
          R := QpPointOnRandomHyperplane(C,p : Precision := pr);
        end if;
        R := [ QQ! R[i] : i in [1..3] ];
        if Valuation(Norm(Evaluate(T,R)),p) lt pr/4 then
	        found := true;
        end if;
      end while;
      TofR := mod_q(KtoKp(Evaluate(T,R)));
      nim := sub<Gp| { TofR - LocalImage[2] + b : b in Generators(LocalImage[1]) join {LocalImage[1] ! 0} } >;
      if #Generators(nim) gt #Generators(LocalImage[1]) then
        vprintf NineDescent, 3: "  Found a Q_%o-point with image T_%o(R) = %o.\n",p, p, TofR;

        LocalImage := <nim,TofR1>;
        vprintf NineDescent, 3: "  Dimension of image found is now %o.\n", #Generators(nim);
        tries := 0;
      end if;
      tries +:= 1;
      if tries gt 5 and Method eq "LocSol" then
        // IsLocallySoluble is having trouble finding points, so we try the other method.
        Method := "RHyperplane";
        vprintf NineDescent, 3: "    Switching to random hyperplane method...\n";
      end if;
      if tries gt 100 then
        dim -:= 1;
        printf "\n***Warning***\nCould not find enough Q_%o-points!\n***********\n",p;
        tries := 0;
      end if;
      if #Generators(LocalImage[1]) gt dim then
        printf "***Warning***\nFinding spurious Q_%o-points!\n***********\n",p;
      end if;
    end while; //#Generators lt dim
    vprintf NineDescent, 1: "  Finished computing the local image.\n";
    if #Generators(LocalImage[1]) eq 0 then
      vprintf NineDescent, 3: "    T(C(Q_%o)) = %o.\n", p,LocalImage[2];
    else
      vprintf NineDescent, 3: "    T(C(Q_%o)) = Span(%o) + %o.\n", p, [Gp ! g : g in Generators(LocalImage[1])], LocalImage[2];
    end if;

    // Now compute preimage of T(C(Q_p)) in KS3.
    GpmodIm,modIm := quo<Gp|LocalImage[1]>;
    comp := hom<Domain(res_p) -> Codomain(modIm) | [ (res_p*modIm)(KS3.i) : i in [1..#Generators(KS3)] ] >;
    boo,preim := HasPreimage(modIm(LocalImage[2]-res_p(alpha_c)),comp);
    if boo then
      PI := < Kernel(comp),preim + alpha_c>;
      vprintf NineDescent, 3: "  res_%o^(-1)(T(C(Q_%o))) has dimension %o.\n",p,p,#Generators(PI[1]);
    else
      PI := "empty";
      vprintf NineDescent, 3: "  res_%o^(-1)(T(C(Q_%o))) is empty.\n", p,p;
    end if;

  else //LocallyInjective eq false, we should use full descent map.
    vprintf NineDescent, 1: "  Computing image using full descent map.\n";
    ClassOfEta := map< Lc -> muLmodNp | x :-> mappa(ImEta(x))>;
    // Given eta in L that is pid-adically close to a cube root of unity in Lp, this returns the class of eta in muLp/Np(muKp).

    res_p := hom< KS3 -> Gp | [ KptoGp(KtoKp(KS3toK(KS3.i))) : i in [1..#Generators(KS3)]] >;
    vprintf NineDescent, 3: "  Searching for a Q_%o-point.\n",p;
    found := false;
    while not found do
      if Method eq "LocSol" then
        sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
        error if not sol, "C is not locally solvable at p = %o.\n";
      else
        R := QpPointOnRandomHyperplane(C,p : Precision := pr);
      end if;
	    R := [ QQ! R[i] : i in [1..3] ];
      if Valuation(Norm(Evaluate(T,R)),p) lt pr/4 then
	     found := true;
      end if;
    end while;
    R1 := R;
    TofR1 := Evaluate(T,R1);
    TofR1im := KptoGp(KtoKp(Evaluate(T,R)));
    vprintf NineDescent, 3: "  Found a Q_%o-point with image T_%o(R) = %o.\n", p, p, TofR1im;
    FakeLocalImage := < sub<Gp|0> , TofR1im >;
    EpsSpace := sub<muLmodNp|0>;
    DelSpacePts := [R1];
    DelSpaceIms := [TofR1im];
    tries := 0;
    while #Generators(FakeLocalImage[1]) + #Generators(EpsSpace) lt dim or tries lt 5 do
      // find random Qp points and determine there images
      
      found := false;
      if #Generators(FakeLocalImage[1]) + #Generators(EpsSpace) eq dim then
        vprintf NineDescent, 2: "  Local image found. Computing %o additional images to be safe.\n", 5-tries;
      end if;
      while not found do
        if Method eq "LocSol" then
          sol,R := IsLocallySoluble(Cm,p : Random := true, Precision := pr);
          error if not sol, "C is not locally solvable at p = %o.\n";
        else
          R := QpPointOnRandomHyperplane(C,p : Precision := pr);
        end if;
        R := [ QQ! R[i] : i in [1..3] ];
        if Valuation(Norm(Evaluate(T,R)),p) lt pr/4 then
         found := true;
        end if;
      end while;
      TofR := Evaluate(T,R);
      TofRim := KptoGp(KtoKp(TofR));
      if TofRim in DelSpaceIms then
        // T(R) = T(R') for some R' already used.
        // check if ell(R) contributes to EpsSpace
        de1 := < TofR, <Evaluate(ell[i],Eltseq(R)) : i in [1..nL] > >;
        n := Index(DelSpaceIms,TofRim);
        
        de2 := < Evaluate(T,DelSpacePts[n]), < Evaluate(ell[i],DelSpacePts[n]) : i in [1..nL]> >;
        eta := GetEta(de1,de2);
        nEpsSpace := sub<muLmodNp| Generators(EpsSpace) join {ClassOfEta(eta)}>;
        if Dimension(nEpsSpace) gt Dimension(EpsSpace) then
          vprintf NineDescent, 3: "  Found a Q_%o-point with image T_%o(R) = %o and nontrivial image in EpsSpace.\n ", p, p, TofRim;
          vprintf NineDescent, 3: "  Dimension of EpsSpace is now %o.\n",Dimension(nEpsSpace);
          EpsSpace := nEpsSpace;
          tries := 0;
        end if;
      else
        nim := sub<Gp| { TofRim - TofR1im + b : b in Generators(FakeLocalImage[1]) join {FakeLocalImage[1] ! 0} } >;
        if #Generators(nim) gt #Generators(FakeLocalImage[1]) then
          vprintf NineDescent, 3: "  Found a Q_%o-point with image T_%o(R) = %o.\n", p, p, TofRim;
          DelSpacePts cat:= [R];
          DelSpaceIms cat:= [TofRim];
          FakeLocalImage := <nim,TofR1im>;
          vprintf NineDescent, 3: "  Dimension of image found is now %o.\n", #Generators(nim) + Dimension(EpsSpace);
          tries := 0;
        end if;
      end if;
      
      tries +:= 1;
      if tries gt 5 and Method eq "LocSol" then
          //IsLocallySoluble is having trouble finding independent points, we try the alternative.
          Method := "RHyperplane";
          vprintf NineDescent, 3: "    Switching to random hyperplane method...\n";
        end if;
        if tries gt 100 then
          dim -:= 1;
          printf "\n***Warning***\nCould not find enough Q_%o-points!\n***********\n",p;
          tries := 0;
        end if;
        if #Generators(FakeLocalImage[1]) gt dim then
          printf "***Warning***\nFinding spurious Q_%o-points!\n***********\n",p;
      end if;

    end while; //#Generators lt dim
    vprintf NineDescent, 1: "  Finished computing the local image.\n";
    if #Generators(FakeLocalImage[1]) eq 0 then
      vprintf NineDescent, 3: "    T(C(Q_%o)) = %o.\n", p,FakeLocalImage[2];
    else
      vprintf NineDescent, 3: "    T(C(Q_%o)) = Span(%o) + %o.\n", p, [Gp!g : g in Generators(FakeLocalImage[1])], FakeLocalImage[2];
    end if;
      
    // compute preimage of T(C(Q_p)) in KS3.
    GpmodIm,modIm := quo<Gp|FakeLocalImage[1]>;
    comp := hom<Domain(res_p) -> Codomain(modIm) | [ (res_p*modIm)(KS3.i) : i in [1..#Generators(KS3)] ] >;
    boo,preim := HasPreimage(modIm(FakeLocalImage[2]-res_p(alpha_c)),comp);
    if boo then
      PI := < Kernel(comp),preim + alpha_c>;
      vprintf NineDescent, 3: "  res_%o^(-1)(T(C(Q_%o))) has dimension %o.\n",p,p,#Generators(PI[1]);
    else
      PI := "empty";
      vprintf NineDescent, 3: "  res_%o^(-1)(T(C(Q_%o))) is empty.\n", p,p;
    end if;

    //Store local data for later use:
    Append(~S_reallybad,<p,res_p,FakeLocalImage,DelSpaceIms,DelSpacePts,GetEta,ClassOfEta,EpsSpace>);
        /*
        Stored local data
        p := LD[1];
        res_p := LD[2];
        Gp := Codomain(res_p);
        FakeLocalImage := LD[3];
        DelSpaceIms := LD[4];
        DelSpacePts := LD[5];
        GetEta := LD[6];
        ClassOfEta := LD[7];
        EpsSpace := LD[8];
        */
  end if; //LocallyInjective

  // Now we have computed the preimages in KS3 of the image of the fake descent map.
  // We intersect this with the space already found.
  if Type(PI) eq MonStgElt then
    vprintf NineDescent, 1: "\nLocal data ==> Selmer set is empty.\n";
    return [];
  else
    PreimsOfLocalIms := IntersectCosets(PreimsOfLocalIms,PI);
  end if;

end for; // p in S

// PreimsOfLocalIms now corresponds to all deltas in KS3 satisfying:
  // 1) res_p(delta) in local image of fake descent map
  // 2) N(delta) = c mod Q*3

  // For each we need to compute epsilon in L* satisfying 
  // N(delta) = beta*epsilon^3
if Type(PreimsOfLocalIms) eq MonStgElt then
  vprintf NineDescent,1: "\nLocal data ==> Selmer set is empty.\n";
  return [],[* *];
end if;
  
vprintf NineDescent, 1: "\nLocal data ==> bound on dimension of fake Selmer set is %o.\n", Ilog(3,#PreimsOfLocalIms[1]);

vprintf NineDescent, 1: "Checking the condition N'(delta)/beta = epsilon^3 and computing epsilons...\n";
DelEps := [];
computedInd := false;
for d in PreimsOfLocalIms[1] do
  flag := false;
  
  d_old := d;
  del_old := KS3toK(d+PreimsOfLocalIms[2]);
  del := NiceRepresentativeModuloPowers(del_old,3);
  eps := <>;
  for i in [1..nL] do
    Lpol := PolynomialRing(Lc[i]);
    rts := Roots(Lpol.1^3 - Np(del)[i]/beta[i]);
    if #rts gt 0 then 
      Append(~eps, < r[1] : r in rts > );
    else
      flag := true;
      vprintf NineDescent, 3: "  delta = %o excluded", del;
      break;
    end if;
  end for;
  if not flag then
    if not computedInd then
      Indis := CartesianProduct( [ Integers(#eps[i]) : i in [1..#eps] ]);
      if #Indis gt 1 then
        vprintf NineDescent, 2: "  mu_3(L) has dimension %o ==> extra epsilons.\n", Ilog(3,#Indis);
      end if;
      computedInd := true;
    end if;
    for ind in Indis do
      DelEps cat:= [< del , Lc! < eps[j][(ZZ!ind[j])+1] : j in [1..nL] > > ];
    end for;
  end if;
end for;
if #DelEps gt 0 then
  vprintf NineDescent, 1: "\nFake Selmer set has dimension %o.\n", Ilog(3,#DelEps) - Ilog(3,#Indis);
else
  vprintf NineDescent, 1: "\nSelmer set is empty.\n";
  return [],[* *];
end if;

vprintf NineDescent, 1: "\nIntersecting with full local images at the primes in S_reallybad = %o.\n",{ p[1] : p in S_reallybad};

/*
  For each (delta,epsilon) and each p in S_reallybad we need to 
  check if there is some P in C(Q_p) such that
  res_p(delta) = T(P) and res_p(epsilon) = ell(P)
*/  


for LD in S_reallybad do
  //Stored local data
  p := LD[1];
  res_p := LD[2];
  Gp := Codomain(res_p);
  FakeLocalImage := LD[3];
  DelSpaceIms := LD[4];
  DelSpacePts := LD[5];
  GetEta := LD[6];
  ClassOfEta := LD[7];
  EpsSpace := LD[8];
  vprintf NineDescent, 2: "  Working at p = %o.\n   Local image of fake descent map has dimension %o.\n   Local image of full descent map has dimension %o.\n",p,#Generators(FakeLocalImage[1]),Dimension(EpsSpace)+#Generators(FakeLocalImage[1]);
  DelEpsp := Set(DelEps);
  r := Ilog(3,#DelEpsp);
  LI1 := AbelianGroup([3 : i in [1..#DelSpaceIms -1]]);
  bchange := Inverse(iso< LI1 -> FakeLocalImage[1] | [ DelSpaceIms[i+1]-DelSpaceIms[1] : i in [1..#DelSpaceIms-1] ]>);
  for deleps in DelEps do
    d := deleps[1];
    e := deleps[2];
  
    imd := res_p(KtoKS3(d)) - DelSpaceIms[1];
    imd2 := Eltseq(bchange(imd));
    TR1 := Evaluate(T,DelSpacePts[1]);
    ellR1 := < Evaluate(ell[j],DelSpacePts[1]) : j in [1..nL] >;
    if #imd2 eq 0 then
      d2 := TR1;
      e2 := ellR1;
    else
      d2 := TR1*(&*[ Evaluate(T,DelSpacePts[i+1])^imd2[i]*TR1^(-imd2[i]) : i in [1..#imd2]]);
      e2 := < ellR1[j]*(&*[ Evaluate(ell[j],DelSpacePts[i+1])^imd2[i]*ellR1[j]^(-imd2[i]) : i in [1..#imd2]]) : j in [1..nL] >;
    end if;
    
    // d2 = T(R1) * prod T(Ri)^imd2[i]/T(R1)^imd2[i]
    // e2 = ell(R1) * prod ell(Ri)^imd2[i]/ell(R1)^imd2[i]
    // d and d2 have the same image in Gp.
    // Check the corresponding eta in EpsSpace.

    eta := GetEta(<d,e>,<d2,e2>);
    if ClassOfEta(eta) in EpsSpace then
      // <d,e> is in the local image of the full descent mappa
    else
      // <d,e> is not in the local image of the full descent map.
      DelEpsp := DelEpsp diff {deleps};
      r2 := Ilog(3,#DelEpsp);
      if r2 lt r then
        
        vprintf NineDescent, 2:"   Bound on dimension of Selmer set is now %o.\n", r2;
        vprintf NineDescent, 3:"   At least %o more (delta,epsilon)'s must be excluded by local conditions.\n", 3^r - 3^r2 -1;
        r := r2;
      end if;
    end if;
  end for;
  DelEps := Setseq(DelEpsp);
  vprintf NineDescent, 2: "  Finished computing local image.\n";

end for;

assert #DelEps mod 3 eq 0 or #DelEps eq 1;

if #DelEps eq 0 then
  vprintf NineDescent, 1: "\nSelmer set is empty.\n";
  return [],[* *];
else
  vprintf NineDescent, 1: "\nSelmer set has dimension %o.\n",Ilog(3,#DelEps);
end if;

if not Models then
  return DelEps;
end if;

K_12Pol<U,V,W,Z1,Z2,Z3,Z4,Z5,Z6,Z7,Z8,Z9> := PolynomialRing(K,12);
_,swapK12 := SwapExtension(K_12Pol);
K_9Pol<Y1,Y2,Y3,Y4,Y5,Y6,Y7,Y8,Y9> := PolynomialRing(K,9);
_,swapK9 := SwapExtension(K_9Pol);
Q_9Pol<y1,y2,y3,y4,y5,y6,y7,y8,y9> := PolynomialRing(QQ,9);

vprintf NineDescent, 2: "Writing down models for the coverings.\n";
P8<[z]> := ProjectiveSpace(QQ,8);
Models := <>;

zsquared := Evaluate(genericZ, [K_12Pol.s : s in [4..12] ])^2;
zcubed := Evaluate(genericZ, [K_12Pol.s : s in [4..12] ])*zsquared;

for deleps in DelEps do

  del := deleps[1];
  eps := deleps[2];
	for j in [1..#ell] do
		assert Np(del)[j]/beta[j] eq eps[j]^3;
	end for;
  EqsK := [ Evaluate(T,[U,V,W]) - del*zsquared ];
  // the equation t = delta*z^2

  for j in [1..#ell] do
    epsInMoverK := MoverKc[j]!eps[j];    
    flagMj := false;
    if DefiningPolynomial(MoverKc[j]) eq DefiningPolynomial(K) then
      // M_j = K_j is not really an extension
      R := K_12Pol;
    else
      flagMj := true;
      R := PolynomialRing(MoverKc[j],12);
      _,Rswap := SwapExtension(R);
    end if;
  	ell_Eq := Evaluate(ellInMoverK[j],[R.s : s in [1..3] ]) - epsInMoverK*Evaluate(Ntildez[j], [R.s : s in [4..12] ]);
  	// the equations ell_j = eps_j*Ntilde_j(z) in M_j
  	if flagMj then
      EqsK cat:= [ Evaluate(f,[K_12Pol.s : s in [1..12] ]) : f in Eltseq(Rswap(ell_Eq)) ];
    else
      EqsK cat:= [ell_Eq];
    end if;
  end for; // j in [1..#ell]

  // EqsK should have 5 equations over K over the form 
	//     linear(U,V,W) = quadratic(Z1,...,Z9)
	// solving for U,V,W leaves 3 equations over K of the form:
	//     quadratic(Z1,...,Z9) = 0.
	// Writing these in a basis for K over Q gives the 27 quadrics we are after.

	rEqsK := Reduce(EqsK);
  CoverMapIndices := { j : j in [1..#rEqsK] | 1 in { Derivative(rEqsK[j],s) : s in [1..3] } };
  Comp := { j : j in [1..#rEqsK] } diff CoverMapIndices;
  QuadricsOverK := [ K_9Pol! Evaluate(rEqsK[i],[0,0,0,Y1,Y2,Y3,Y4,Y5,Y6,Y7,Y8,Y9]) : i in Comp ];
  QuadricsOverQ := [];
  for quadric in QuadricsOverK do
    seq := Eltseq(swapK9(quadric));
    QuadricsOverQ cat:= [ Evaluate(seq[i],[y1,y2,y3,y4,y5,y6,y7,y8,y9]) : i in [1..#seq] ];
  end for;
  QuadricsOverQ := Reduce(QuadricsOverQ);
  D := Curve(P8,QuadricsOverQ);
  
  // We also want to get the covering maps pi_i : D_i -> C.
  Teqdelcube := Evaluate(T,[U,V,W]) - del*Evaluate(genericZ, [K_12Pol.s : s in [4..12] ])^3;
  reducedOverQ := Reduce(Eltseq(swapK12(Teqdelcube)));
  // This should give 3 equations over Q
  //  x_i = cubic(z_1,...,z_9) for i = 1,2,3
  // and 6 equations cubic(z_1,...,z_9) = 0.
  // the first three define the covering map,
  // the other 6 are already in the ideal generated by the 27 quadrics.
  Q12 := Parent(reducedOverQ[1]);
  Pi := [ Evaluate(Q12.i - reducedOverQ[i],[0,0,0,y1,y2,y3,y4,y5,y6,y7,y8,y9]) : i in [1..3] ];
  Pi := map<D -> C | Pi>;
  Append(~Models, <D,Pi>);
  
end for; //deleps in DelEps


// The elements in AllEqs are tuples of 27 quadrics, each of which defines a g1nmlCrv of degree 9.
// Now we need to run minimization and reduction.

PZ := PolynomialRing(ZZ,9);
PQ := PolynomialRing(QQ,9);
d := 9; // = Rank(PZ);
MakeIntegral := func< qq | [ PZ ! q : q in qq ] >;
MakeRational := func< qq | [ PQ ! q : q in qq ] >;

ClearDenoms := function(qq);
  nq := [];
  for q in qq do
    m := LCM([Denominator(Coefficients(q)[i]):i in [1..#Coefficients(q)]]);
    q2 := q*m;
    r := GCD([ZZ!Coefficients(q2)[i]: i in [1..#Coefficients(q)]]);
    q3 := PZ ! (q2/r);
    nq cat:= [q3];
  end for;
  return nq;
end function;

/* Ad hoc reduction */
matsize := func<mat | &+[c^2 : c in Eltseq(mat)]>;
polsize := func<pol | &+[c^2 : c in Coefficients(pol)]>;
matssize := func<mats | &+[matsize(m) : m in mats]>;
polssize := func<pols | &+[polsize(p) : p in pols]>;
mons2 := MonomialsOfDegree(PZ, 2);

function PL(pols)
  mat := Matrix([[MonomialCoefficient(e, m) : m in mons2] : e in pols]);
  gain := &*ElementaryDivisors(mat);
  mat1 := BasisMatrix(PureLattice(Lattice(mat)));
  return [&+[mat1[i,j]*mons2[j] : j in [1..#mons2]] : i in [1..#pols]], gain;
end function;

function Upper(M)
// Given a symmetric nondegenerate matrix ovre Q, this returns a positive definite
// matrix over Q bounding the quadratic form.
  D, T := OrthogonalizeGram(M);
  Ti := ChangeRing(T, QQ)^-1;
  D1 := DiagonalMatrix(QQ, [Abs(D[i,i]) : i in [1..NumberOfRows(D)]]);
  return Ti*D1*Transpose(Ti);
end function;

function QFormToMatrix(F)
// Gives the symmetric matrix representing the quadratic form F.
  P := Parent(F);
  // require IsHomogeneous(F) and TotalDegree(F) eq 2:
  //         "The polynomial must be a quadratic form (homogeneous of degree 2).";
  return Matrix([[(i eq j select 2 else 1)*MonomialCoefficient(F, P.i*P.j)
                    : j in [1..d]] : i in [1..d]]);
end function;

function MatrixToQForm(M,P)
// Gives the quadratic form in the polynomial ring represented by the matrix.
  // require IsSymmetric(M): "Matrix must be symmetric.";
  // require NumberOfRows(M) eq Rank(P): "Polynomial Ring must have as many variables "*
  //                             "as the matrix has rows.";
  d := Rank(P);
  return &+[M[i,i]*P.i^2 : i in [1..d]]
          + 2*&+[M[i,j]*P.i*P.j : j in [i+1..d], i in [1..d-1]];
end function;

function REDUCE(qq,N)
  Tr := IdentityMatrix(QQ,d);
  mats := [QFormToMatrix(e) : e in qq];
  siz := matssize(mats);
  vprintf NineDescent, 2: "  Size before reduction: %o\n", RealField(5)!Log(10,siz);
  count := 0;
  count2 := 0;
  repeat
    oldsiz := siz;
    U := &+[Upper(m) : m in mats];
    _, T := LLLGram(U);
    Tr := T*Tr;
    mats1 := [T*m*Transpose(T) : m in mats];
    mats1 := [Matrix(9, Eltseq(b)) : b in Basis(LLL(Lattice(Matrix([Eltseq(m) : m in mats1]))))];
    sizA := matssize(mats1);
    qq1 := ClearDenoms(MakeRational( PL([MatrixToQForm(m, PZ) : m in mats1]) ));
    mats2 := [QFormToMatrix(e) : e in qq1];
    sizB := matssize(mats2);
    vprintf Reduce, 2: "  Size after reduction now: %o\n  size after PureLattice: %o\n", RealField(5)! Log(10,sizA), RealField(5)! Log(10,sizB);
    if sizA ge oldsiz and sizB ge oldsiz then
      count +:= 1;
      count2 +:= 1;
      if count2 eq 10
        then N -:= 1;
        count2 := 0;
      end if;
    else
      count := 0;
    end if;
    if sizA ge sizB then
      mats := mats2;
    else
      mats := mats1;
    end if;
    siz := matssize(mats);
    vprintf Reduce, 2: "  Current size: %o\n", RealField(5)! Log(10,siz);
  until count ge N;
  vprintf NineDescent, 1: "  Size after reduction: %o.\n", RealField(5)! Log(10,siz);
  return [ MatrixToQForm(m,PQ) : m in mats ],Tr;
end function; //REDUCE

function BetterModel(DPi,S);
  N := ExtraReduction;
  D := DPi[1];
  PP := Ambient(D);
  Pi := DPi[2];
  qq := ClearDenoms(MakeRational(DefiningEquations(D)));
  qq := MakeRational(PL(MakeIntegral(qq)));
  M := MinimisationMatrix(qq,S);
  mats := [ Transpose(M)*QFormToMatrix(q)*M : q in MakeIntegral(qq) ];
  qq := [ PZ !MatrixToQForm(m,PQ) : m in mats ];
  nq,T := REDUCE(MakeIntegral(ClearDenoms(MakeRational(qq))),N);
  Dnew := Curve(PP,nq);
  rm := map<Dnew -> D | [ &+[(T*Transpose(M))[i,j]*PP.i : i in [1..d] ] : j in [1..d] ] >;
  pi := rm * DPi[2];
  return <Dnew, pi>;
end function;

GoodModels := [];
GoodMaps := [* *];
vprintf NineDescent, 1: "\nRunning minimization and reduction...\n";
s := 1;
for DPi in Models do
  vprintf NineDescent, 2: "\n  working on %o-th model.\n",s;
  s +:= 1;
  goodDPi := BetterModel(DPi,S);
  D := goodDPi[1];
  Pi := goodDPi[2];
  D`Nonsingular := true;
  D`Irreducible := true;
  D`GeometricallyIrreducible := true;
  GoodModels cat:= [D];
  Append(~GoodMaps,Pi);
end for;
return GoodModels,GoodMaps;

end function; //NineD


intrinsic NineDescent(C::Crv : ExtraReduction := 10) -> SeqEnum, List
{Computes a sequence of genus one curves of degree 9 in P8 and a tuple of maps
 giving these the structure of 3-coverings of C.}
Ds,Pis := NineD(C,true,ExtraReduction);
return Ds,Pis;
end intrinsic;

intrinsic NineSelmerSet(C::Crv) -> Tup
{Computes the 3-Selmer set of C as a set of pairs (delta,eps) in the product
of the Flex and Line algebras associated to C.}
DelEps := NineD(C,false,0);
return DelEps;
end intrinsic;

