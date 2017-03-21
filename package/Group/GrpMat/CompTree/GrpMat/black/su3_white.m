freeze;
import "white-prelims.m": ImageInLtilde, norm, 
                          trace, form, 
                          CommutatorSpace, IsPowerOfTwo, 
                          IsOrderMoreThanThree, IsMersenne, 
                          IsFermat, Isppdhash, 
                          MyChangeOfBasisMatrix, 
                          ElementHavingPrescribedTrace, 
                          ElementHavingPrescribedNorm, formRest, 
                          OrthogonalComplement, FindHyperbolicPair, 
                          GetVector, GetFpBasisVectors;

ConstructL := function(G, p, k, P, F, delta, limit)
    //First find tau
    
    Ggens := [G.i : i in [1..Ngens(G)]];
    q := p^k;
    i := 1;
    if k mod 2 eq 1 then
        repeat
            t, w := Random(P);
            a := t^(2*(q-1));
            i +:= 1;
            flag := true;
            ot := Order(t);
            if IsMersenne(q) or IsFermat(q) then
                flag := (ot mod 16) eq 0;
            end if;
            e1 := exists(z1){e : e in Eigenvalues(a) | e[2] eq 1};
            if e1 then
	        evalue1 := z1[1];
                espace1 := Eigenspace(a, evalue1);
            end if;
            e2 := exists(z2){e : e in Eigenvalues(a) | e[2] eq 2};
            e3 := false;
            if e1 and e2 then
	        evalue2 := z2[1];
                espace2 := Eigenspace(a, evalue2);
                e3 := Dimension(espace1) eq 1 and Dimension(espace2) eq 2;
            end if;
            e4 := false;
            if k eq 1 and (p eq 23 or p eq 47) then
                e4 := ot mod 16 eq 0;
            else
                e4 := true;
            end if;
            isgood := (flag and Isppdhash(ot, p, 2*k) and Isppdhash(ot, p, k) 
                      and IsOrderMoreThanThree(a) and e3 and e4); 
        until isgood or i eq limit+1;
        if not isgood then
	    return false, _, _, _, _, _, _, _, _;
        end if;
    else
        repeat
	    t, w := Random(P);
            a := t^(2*(q-1));
            i +:= 1;
            ot := Order(t);
            isgood := (Isppdhash(ot, p, 2*k) and Isppdhash(ot, p, k) and 
                       Isppdhash(ot, p, k div 2) and IsOrderMoreThanThree(a));
        until isgood or i eq limit+1;
        if not isgood then
            return false, _, _, _, _, _, _, _, _;
        end if;
    end if;
    worda := w^(2*(q-1));

    //Now construct L
    Limit := 10;
    j := 1;
    repeat
        g, w := Random(P); 
        b := a^g; 
        A := sub<Generic(G) | [a, b]>;
        L, wL := DerivedGroupMonteCarlo(A);
        S := Generators(L);
        SisEmpty := #S eq 0;
        f := false;
        if not(SisEmpty) then
           comL := CommutatorSpace(F, S);
           assert Dimension(comL) eq 2;
           V := GModule(L);
           U := sub<V|comL>;
           Ltildegens := [GL(2, q^2)!ActionGenerator(U, i) : i in [1..Ngens(L)]];
           LL := MatrixGroup<2, F | [ActionGenerator(U, i) : i in [1..Ngens(L)]]>;
           flag := RecognizeClassical(LL : Case := "unitary");
           f := false;
           if flag then
	      ff, Ltilde := IsOverSmallerField(LL , k);
              if not ff then
	         Ltilde := LL;
              else
	         reducedimage := map< Generic(LL) -> Generic(Ltilde) | 
                                  x :-> SmallerFieldImage(LL, x)>;
                 subLtilde := sub<Generic(Ltilde) | 
                            [(LL.i @ reducedimage) : i in [1..Ngens(LL)]]>;
                 Ltilde := subLtilde;
              end if;
              f, aa, bb, cc, dd := RecognizeSL2(Ltilde, q);
              if ff then
	         // aaa := aa; bbb := bb; ccc := cc; ddd := dd;
                 aa := hom<Generic(LL) -> Generic(SL(2, q)) | 
                           x:-> ((x @ reducedimage) @ aa)>;
                 bb := hom<Generic(SL(2, q)) -> Generic(LL) | 
                           x:-> Evaluate((( x @ bb) @ cc), Ggens)>;
                 cc := hom<Generic(LL) -> Codomain(cc) | 
                           x:-> ((x @ reducedimage) @ cc)>;
                 dd := hom<Domain(dd) -> Generic(LL) | 
                           x:-> Evaluate(x, Ggens)>;
              end if;
           end if;
           j +:= 1;
        end if;
    until f or j gt Limit;
    if not f then
        return false, _, _, _, _, _, _, _, _;
    end if;    
    wordb := worda^w;
    wordL := [Evaluate(wL[i], [worda, wordb]) : i in [1..Ngens(L)]];
    return true, U, V, comL, wordL, aa, bb, cc, dd;
end function;

GetTransvectionWord := function(t, Tgens, delta)
    E := BaseRing(Parent(t));
    p := Characteristic(E);
    k := Degree(E) div 2;
    q := p^k;
    G2 := GL(2, q^2);
    W := SLPGroup(#Tgens);
    E := GF(q);
    F := GF(p);
    V, f := VectorSpace(E, F);
    alpha := PrimitiveElement(E);
    if t[2, 1] ne 0 then
        vTgens := [Tgens[i][2, 1]/delta : i in [1..#Tgens]];
        vt := t[2, 1]/delta;
    else
        vTgens := [Tgens[i][1, 2]*delta : i in [1..#Tgens]];
        vt := t[1, 2]*delta;
    end if;
    vTgens := [ (vTgens[i] @ f) : i in [1..#Tgens]];
    vt := vt @ f;
    RREF := EchelonForm(Transpose(Matrix(vTgens cat [vt])));
    vt := Transpose(RREF)[#Tgens +1];
    vt := [Integers()! vt[i] : i in [1..Ncols(vt)]];
    wt := &*[W.i^(vt[i]) : i in [1..#vt]];
    return wt;
end function;

Findh := function(Lgens, r, g)
    E := BaseRing(Parent(g));
    p := Characteristic(E);
    k := Degree(E) div 2;
    q := p^k;
    G2 := GL(2, q^2);
    W := SLPGroup(#Lgens);
    Tgens := [Lgens[i] : i in [1..k]];
    Sgens := [Lgens[i] : i in [k+1..2*k]];
    F := GF(q);
    alpha := PrimitiveElement(F);
    comL := CommutatorSpace(E, Lgens);
    Ltildegens := [G2!(ImageInLtilde(Lgens[i], comL)) : i in [1..#Lgens]];
    newbas := [BasisElement(comL, 1), BasisElement(comL, 1)*r*g ];
    B := StandardHermitianForm(3, E);
    beta := form(newbas[2], newbas[1], B, k);
    newbas[2] := newbas[2]/beta;
    assert form(newbas[1], newbas[2], B, k) eq 1;
    CB := MyChangeOfBasisMatrix(comL, newbas);
    Ltildegens := Ltildegens^(CB^-1);
    Ttildegens := [Ltildegens[i] : i in [1..k]];
    Stildegens := [Ltildegens[i] : i in [k+1..2*k]];
    delta := Tgens[1][3, 1];

    //we construct z := [    alpha           0           ]
    //                  [    0               alpha^-1    ]

    x1 := delta;
    t1 := G2![1, 0, x1, 1];
    x2 := (alpha - 1)/ delta;
    t2 := G2![1, x2, 0, 1];
    wt2 := GetTransvectionWord(t2, Stildegens, delta);
    assert Evaluate(wt2, Stildegens) eq t2;
    x3 := -delta/alpha;
    t3 := G2![1, 0, x3, 1];
    wt3 := GetTransvectionWord(t3, Ttildegens, delta);
    assert Evaluate(wt3, Ttildegens) eq t3;
    x4 := -alpha*x2;
    t4 := G2![1, x4, 0, 1];
    wt4 := GetTransvectionWord(t4, Stildegens, delta);
    assert Evaluate(wt4, Stildegens) eq t4;
    // note the relation t4*t3*t2*t1 = z.
    h := Evaluate(wt4, Sgens) * Evaluate(wt3, Tgens) * Evaluate(wt2, Sgens) * Tgens[1];
    wTgens := [W.i : i in [1..#Tgens]];
    wSgens := [W.i : i in [#Tgens+1..#Lgens]];
    wh := Evaluate(wt4, wSgens) * Evaluate(wt3, wTgens) * Evaluate(wt2, wSgens) * wTgens[1];
   return h, wh;
end function;

FindGens_SU3 := function(G, p, k)
    //limit parameters
    limit1 := 10;      // how many times do we attempt construct L?
    limit2 := 2;       // how many times do we attempt to construct L_i? 
    limit3 := 10;      // how many times do we attempt to construct TQ?

    // some checks that G, p, k are sensible.
    assert IsProbablyPerfect(G);
    assert RecognizeClassical(G: Case := "unitary");
    assert p eq Characteristic(BaseRing(G)); 
    assert k eq (Degree(BaseRing(G.1)) div 2);
    q := p^k; 
    F := GF(q^2); 
    F0 := sub< F | F.1^(q+1)>;    // isomorphic to GF(q)
    P := RandomProcessWithWords(G); 
    delta := ElementHavingPrescribedTrace(F, 0);
    counter := 0;
    repeat
        f, U, V, comL, wordL, aa, bb, cc, dd := ConstructL(G, p, k, P, F, delta, limit1);
        counter +:= 1;
    until counter eq limit1 or f;
    if not f then return false; end if;

//========================================
//	Some Elements of L. Section 6.3.3.
//========================================

    B := ClassicalForms(G)`sesquilinearForm;
    //find a hyperbolic basis st e and f are in [V, L].
    e, f := FindHyperbolicPair(F0, F, U, B, k, V); 
    e := V!e;
    f := V!f;
    Uperp := (OrthogonalComplement(U, V, B, k));
    assert Dimension(Uperp) eq 1;
    v := V!(Uperp.1);
    alpha := ElementHavingPrescribedNorm(1/form(v, v, B, k), F0, F, q); 
    v := alpha*v;
    //make sure we have a hyperbolic basis
    assert form(e, f, B, k) eq 1 
       and form(e, e, B, k) eq 0 
       and form(f, f, B, k) eq 0 
       and form(v, e, B, k) eq 0 
       and form(v, f, B, k) eq 0 
       and form(v, v, B, k) eq 1;
    VV := VectorSpace(V);
    basis := [Vector(e), Vector(v), Vector(f)];
    //a change of basis matrix that converts between new and old basis.
    CB := MyChangeOfBasisMatrix(VV, basis);
    gen := Generic(G);
    CB := gen!CB;
    //Original generators of G in new basis.
    gens := [(Generic(G)!G.i)^(CB^-1) : i in [1..Ngens(G)]];
    //construct h, r, t_i defined in Section 6.3.3.
    zeta := F.1^(q+1);
    h := gen![zeta, 0, 0, 0, 1, 0, 0, 0, 1/(zeta)];
    htilde := ImageInLtilde(h^CB, comL);
    wordh := Evaluate ((htilde @ cc) , wordL);
    r := gen![0, 0, Frobenius(delta, F0), 0, 1, 0, 1/delta, 0, 0];
    rtilde := ImageInLtilde(r^CB, comL);
    wordr := Evaluate ((rtilde @ cc) , wordL);

    tList := [(gen![1, 0, 0, 0, 1, 0, (zeta)^(i-1)*delta, 0, 1]) : i in [1..k]];
    wordtList := [ (Evaluate(ImageInLtilde((tList[i])^CB, comL) @ cc, wordL)) 
                             : i in [1..#tList]];

    //=================================
    //	The subgroup Q. Section 6.3.4. 
    //=================================

    BB := StandardHermitianForm(3, F);
    counter := 0;
    repeat
        trys1 := 0;
        repeat
	    g1, wordg1 := Random(P);			 
            g1 := gen!g1;
	    g1 := g1^(CB^-1);
	    ConjugatedtList1 := tList^(r*g1);
	    gens1 := tList cat ConjugatedtList1;
	    comL1 := CommutatorSpace(F, gens1);
	    v11 := BasisElement(comL1, 1); 
	    v12 := v11*r*g1;
	    assert v12 in comL1;
	    form1 := form(v11, v12, BB, k);
	    f1 := form1 ne 0;
	    trys1 +:= 1;
        until f1 or trys1 eq limit2;
        if not f1 then return false; end if;

        trys2 := 0;
        repeat
	    g2, wordg2 := Random(P);	
	    g2 := gen!g2;
	    g2 := g2^(CB^-1);
            ConjugatedtList2 := tList^(r*g2);
            gens2 := tList cat ConjugatedtList2;
	    comL2 := CommutatorSpace(F, gens2);
	    v21 := BasisElement(comL2, 1);
	    v22 := v21*r*g2;		  
	    assert v22 in comL2;
	    form2 := form(v21, v22, BB, k);
	    f2 := form2 ne 0;
	    trys2 +:= 1;
        until (f2 and comL2 ne comL1) or trys2 eq limit2;
        if not (f2 and comL2 ne comL1) then
            return false;
        end if;
        //finding conjugatedtList1 and conjugatedtList2 as SLPs in gens
        wordConjugatedtList1 := [wordtList[i]^(wordr*wordg1) : i in [1..#tList]];
        wordConjugatedtList2 := [wordtList[i]^(wordr*wordg2) : i in [1..#tList]];
        wordgens1 := wordtList cat wordConjugatedtList1;
        wordgens2 := wordtList cat wordConjugatedtList2;
        // constructing hi as defined in 6.3.4.
        h1, wordh1 := Findh(gens1, r, g1);
        h2, wordh2 := Findh(gens2, r, g2);
        wordh1 := Evaluate(wordh1, wordgens1);
        wordh2 := Evaluate(wordh2, wordgens2);
        TQ := [(h, h1)^(h^(j-1)) : j in [1..k]] cat [(h, h2)^(h^(j-1)) 
               : j in [1..k]] cat tList;
        wordTQ := [(wordh, wordh1)^(wordh^(j-1)) : j in [1..k]] cat
                [(wordh, wordh2)^(wordh^(j-1)) : j in [1..k]] cat wordtList;
        //Check that TQ generates Q(x)
        FpBas := GetFpBasisVectors(TQ);
        myflag := IsIndependent(FpBas);
        counter +:= 1;
    until myflag or counter eq limit3;
    if not myflag then return false; end if;

    // The sets T, TQ^r defined in Section 6.3.6.
    wordTQr := [(wordTQ[j])^(wordr) : j in [1..#wordTQ]];
    T := TQ cat (TQ)^r;
    wordT := wordTQ cat wordTQr;
    PetersGens := T^CB;
    LGOimages := ClassicalStandardGenerators("SU", 3, q);
    conjugatingmatrix := Generic(G) ! [1, 0, 0, 0, 0, 1, 0, 1, 0];
    LGOimages := LGOimages^conjugatingmatrix;
    Mygens := (T cat [r]);
    wMygens := (wordT cat [wordr]);
    /* Assembling data structure for G   */ 
    rf := recformat < Mygens, wMygens, LGOGenerators, LGOimages, LGOWords, 
      PetersGenerators, wPetersGenerators, CB, classicalform, oldgensnewbasis>;
    data := rec< rf | Mygens := Mygens, wMygens := wMygens, 
                      LGOimages := LGOimages, 
                 PetersGenerators := PetersGens, wPetersGenerators := wordT, 
                     CB := CB, classicalform := B, oldgensnewbasis := gens>;
    G`SU3DataStructure := data;

    return true;
end function; 

//=================================================
//      Algorithmic properties of Q. Section 6.3.5.
//=================================================

GetTVector := function(Tgens , t)
	  delta := Tgens[1][3, 1];
	  E := BaseRing(Parent(t));
          k := Degree(E) div 2;
          p := Characteristic(E);
	  FF := GF(p^k);
          F := GF(p);
          V, f := VectorSpace(FF, F);
	  tt := (t[3, 1]/delta);
	  if not(tt in FF) then Tgens; tt; end if;
          v := (tt @ f);
          return v;
end function;

//Lemma 6.1.
/*
Input: (1) The generating set TQ, described in section 6.3.4.
           We require that TQ is ordered so that the tranvections, tj, 
           are the last entries of TQ.
       (2) an element u of Q
Output: An SLP from TQ to u.
*/

writeQSLP := function(TQ, u)
	  W := SLPGroup(#TQ);
	  E := BaseRing(Parent(u));
	  k := Degree(E) div 2;
	  assert #TQ eq 3*k;
	  p := Characteristic(E);	
	  F := GF(p);
	  q := p^k;
	  //The following is a basis for T/Q as a v.s. over Fp.
	  FpBasis := [TQ[i] : i in [1..2*k]];
	  vFpBasis := [GetVector(TQ, FpBasis[i]) : i in [1..#FpBasis]];
	  Tgens := [TQ[i] : i in [2*k+1..3*k]];
	  vutilde := GetVector(TQ, u);
	  //now express vutilde as a combination of vFpBasis
          RREF := EchelonForm(Transpose(Matrix(vFpBasis cat [vutilde])));
          vutilde := Transpose(RREF)[#FpBasis+1];
	  vutilde := [Integers()!vutilde[i]: i in [1..Ncols(vutilde)]];
	  //sigma is a word in TQ that evaluates to utilde, which is in the coset uT.
	  sigma := &*[W.i^(vutilde[i]) : i in [1..#vutilde]];
	  utilde := Evaluate(sigma, TQ);
	  //t in T(x), transvection group.
	  t := u*utilde^-1;
	  if t ne Identity(Parent(t)) then 
	     //Use linear algebra to find a word for t in Tgens
	     vTgens := [ GetTVector(Tgens, Tgens[i]) : i in [1..#Tgens]];
             vt := GetTVector(Tgens, t);
	     RREF := EchelonForm(Transpose(Matrix(vTgens cat [vt])));
	     vt := Transpose(RREF)[#Tgens+1];
	     vt := [Integers()!vt[i]  : i in [1..Ncols(vt)]];
	     tau := &*[ W.(i + 2*k)^(vt[i]) : i in [1..k]];
	     //Note that Evaluate(tau, TQ) = t.
 	  else tau := Identity(W);
	  end if;
	  return sigma*tau;
end function;

//===========================================
//      Straightline programs. Section 6.3.6
//===========================================

/* 
Input: (1) Brooksbanks standard generators for SU3, T.
       (2) A list of SLPs (in default generators of SU3) for each entry of T.
       (3) r, defined in section 6.3.3.
       (4) An SLP (in default gens) for r.
       (5) Any element g in SU3.

Output:  An SLP (in default gens) for g. 
*/
		     
writeSLP := function(T, wT, r, wr, g)
   gen := Generic(Parent(g));
   F := BaseRing(Parent(g));
   k := Degree(F) div 2;
   p := Characteristic(F);
   q := p^k;
   F0 := sub<F | F.1^((p^k) + 1)>;
   V := VectorSpace(F, 3);
   numQgens := #T div 2;
   Qgens := [T[i] : i in [1..numQgens]];
   wQgens := [wT[i] : i in [1..numQgens]];
   Qgensr := [T[i] : i in [numQgens+1..#T]];
   wQgensr := [wT[i] : i in [numQgens+1..#T]];
   x := sub<V | V.1>; x1 := V.1;
   y := sub<V | V.3>; y1 := V.3;
   tracker1 := false;
   tracker2 := false;
   if g eq r then 
      return wr;
   end if;
   multrx := false;
   multry := false;
   if x*g ne x then
      if x*g eq y then
         g := g*r;
         multrx := true;
      end if;
      z := x1*g;
      z := (z[1])^-1*z; a := z[1]; b := z[2]; c := z[3];
      lambda := b*a^-1;
      nu := c*a^-1;
      beta := -lambda^q;
      winv := gen![1, lambda, nu, 0, 1, beta, 0, 0, 1];
      assert lambda*(-beta) +nu + Frobenius(nu, k) eq 0;
      w := winv^-1;
      //constructing sigma1
      ww := winv^(r^-1);
      assert (ww[2, 1])*(-ww[3, 2]) + (ww[3, 1]) + (ww[3, 1])^q eq 0;
      wordww := writeQSLP(Qgens, ww);
      wordww := Evaluate(wordww, wQgens);
      wordwinv := wordww^wr;
      //sigma1inv is a SLP (in default gens) to winv=w^-1.
      sigma1inv := wordwinv;
      if multrx then
         sigma1inv := wr^-1*wordwinv;
      end if;
      g := g*w;
      tracker1 := true;
   end if;
   if y*g ne y then
      z := y1*g;
      z := (z[3])^-1*z; a := z[1]; b := z[2]; c := z[3];
      lambda := b*c^-1;
      nu := a*c^-1;
      beta := -Frobenius(lambda, k);
      //beta := -lambda^-1*(-nu + - nu^q);
      uinv := gen![1, 0, 0, beta, 1, 0, nu, lambda, 1];
      u := uinv^-1;
      worduinv := writeQSLP(Qgens, uinv);
      worduinv := Evaluate(worduinv, wQgens);
      //sigma2inv is a SLP (in default gens) to u^-1
      sigma2inv := worduinv;
      g := g*u;
      tracker2 := true;
   end if;
   //now g in G_{x, y} so g = diag matrix.
   lambda := g[1, 1]; 
   delta := r[3, 1]^-1;   
   gamma := lambda*delta;
   gammainv := gamma^-1;
   eta := ElementHavingPrescribedNorm(-gamma+-gamma^q, F0, F, q);
   //note u1 in Q
   lambda := eta*gammainv;
   nu := gammainv^q;
   beta := -Frobenius(lambda, k);
   u1 := gen![1, 0, 0, lambda, 1, 0, nu, beta, 1];
   //note u2 in Q^r
   lambda := eta^q;
   nu := gamma;
   beta := -Frobenius(lambda, k);
   u2 := gen![1, lambda, nu, 0, 1, beta, 0, 0, 1];
   //u3 in Q
   lambda := eta*gammainv^q;
   nu := gammainv^q;
   beta := -Frobenius(lambda, k);
   u3 := gen![1, 0, 0, lambda, 1, 0, nu, beta, 1];
   //note that g = u1*u2*u3*r
   //find words for u's
   wu1 := writeQSLP(Qgens, u1);
   wu1 := Evaluate(wu1, wQgens);
   u2rinv := u2^(r^-1);
   wu2rinv := writeQSLP(Qgens, u2rinv);
   wu2rinv := Evaluate(wu2rinv, wQgens);
   wu2 := wu2rinv^wr;
   wu3 := writeQSLP(Qgens, u3);
   wu3 := Evaluate(wu3, wQgens);
   sigma := wu1*wu2*wu3*wr;
   if not (tracker1) then
      sigma1inv := Identity(Parent(sigma));
   end if;
   if not (tracker2) then
      sigma2inv := Identity(Parent(sigma));
   end if;
   return sigma*sigma2inv*sigma1inv;
end function;	    

GetSLP := function(X, wX, CB, g)
   r := X[#X];
   wr := wX[#X];
   T := [ X[i] : i in [1..#X-1]];
   wT := [wX[i] : i in [1..#X-1]];
   gg := g^(CB^-1);
   word := writeSLP(T, wT, r, wr , gg);
   return word;
end function;

// Constructively recognise a natural copy of SU(3, q) 
RecogniseSU3White := function (G, q) 

    if assigned(G`RecognitionMaps) then
        maps := G`Recognitionmaps;
        return true, maps[1], maps[2], maps[3], maps[4];
    end if;

    limit := 5;  //how many times do we to attempt to find gens?
    _, p, k := IsPrimePower(q);
    i := 0;
    repeat
        flag := FindGens_SU3(G, p, k);
        i +:= 1;
    until (i eq limit) or flag;
    if not flag then return false; end if;

    rec := G`SU3DataStructure;
    X := rec`Mygens;
    wX := rec`wMygens;
    CB := rec`CB;     
    S := rec`LGOimages;
    E := S^CB;
    wE := [GetSLP(X, wX, CB, E[i]) : i in [1..#E]];
    gen := Generic(G);
    gens := [G.i : i in [1..Ngens(G)]];
    W := WordGroup(G);
    //recognition maps
    phi := hom<gen -> GL(3, q^2) | x:-> x^(CB^-1)>;
    tau := hom<GL(3, q^2) -> gen | x:-> x^CB>; 
    gamma := hom<gen -> W | x:-> GetSLP(X, wX, CB, x)>;
    delta := hom<W -> gen | x:-> Evaluate(x, gens)>;

    G`RecognitionMaps := <phi, tau, gamma, delta>;
    G`SU3DataStructure`LGOGenerators := E;
    G`SU3DataStructure`LGOWords := wE;

    return true, phi, tau, gamma, delta;
end function;
