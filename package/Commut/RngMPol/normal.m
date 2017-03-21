freeze;

//////////////////////////////////////////////////////////////////
//    Functions to compute the integral closure of reduced      //
//     affine rings by generic or function field methods.       //
//              Mike Harrison. 05/2004                          //
//////////////////////////////////////////////////////////////////

declare verbose IntCl, 1;

////////////  Function Field methods. ////////////////////////////
//// Currently used for two-variable affine rings.       /////////
 
function Convert(M)

   nc := NumberOfColumns(M);
   m_deg := Max([Degree(M[i,j]) : i in [1..NumberOfRows(M)],
                          j in [1..nc]]);
   elts := Eltseq(M);
   Ms := [Matrix(nc,[Coefficient(a,i) : a in elts]) : i in [0..m_deg]];
   return HorizontalJoin(Ms);

end function;

function ConvertVec(seq,mdeg)

   return Vector(&cat[[Coefficient(a,i) : a in seq] : i in [0..mdeg]]);

end function;

//  Function to find a (usually) minimal number of k-algebra generators
// for the maximal finite order O of alg fn field F = K(y), K := k(x).
// 1,Bs[2],..Bs[n] is a k[x]-basis of O and Bs[1]=x.
// If Support(Denominator(Divisor(x))) = {P1,..Ps} and
// D = P1+..+Ps, then the computation uses the fact that O is
// precisely the elts in F with no poles outside D and that the
// k-fin-dim Riemann-Roch spaces L(D)<=L(2*D)<=... gives an
// increasing filtration of O. We find genarators in the
// "new" part of the small L(r*D)s.
// NOTE: another approach would be to just find a multiple of D
//   which is very ample (eg Degree(r*D)>2*genus), find the
//   PROJECTIVE embedding of this divisor and take the appropriate
//   affine patch. This only involves 1 R-R space computation but
//   involves computing the image and will probably have more
//   generators.
// Returns an array of the generators (as elts of O) and an array
// of k-polynomials expressing the Bs[i] in terms of these gens.
function FindMinimalGenerators(F,K,Bs)

    O := Universe(Bs);
    n := #Bs;

    R1 := IntegerRing(K);

    Divs := DivisorGroup(F);
    D1 := Denominator(Divisor(F!Bs[1]));
    Ps := Support(D1);
    m := #Ps;
    D := &+[Divs!P : P in Ps];
    val_bs := [Max([-Valuation(Bs[i],P) : P in Ps] cat [0]) : i in [1..n]];
    d := Max(val_bs);

    Q := PolynomialRing(BaseRing(R1),n);
    gens_wtd := [[O|]]; //array of new generators in L((r-1)*D)
    news := [[O!1]];    //array of k-bases of the "new" part of
                        //L((r-1)*D) - ie not in L(i_1*D)*..L(i_m*D)
                        //with i_j >= 0, i_1 + .. + i_m=(r-1)
    pols := [[Q!1]];    //array of polys expressing the elements of
                        //news in terms of the generators
    b_pols := [Q!0 : i in [1..n]];
              //array of polys (eventually) expressing the elements of
              //Bs in terms of the generators.
    ngens := 0;
    N := 1;        // dimension of current L(k*D)

    for k in [1..d] do
        V,h := RiemannRochSpace(k*D);
        if Dimension(V) eq N then // no new elements
            Append(~gens_wtd,[O|]);
            Append(~news,[O|]);
            Append(~pols,[Q|]);
            continue;
        end if;
        mat := Convert(Matrix(R1,[Eltseq(O!(h(v))) : v in Basis(V)]));
        mdeg := (NumberOfColumns(mat) div n)-1;
        old := [];
        for j in [1..k], t in news[j] do
           Append(~old,ConvertVec(ChangeUniverse(Eltseq(t),R1),mdeg));
        end for;
        newpols := [];
        poss_new := [O|];
        for j := (k div 2)+1 to 2 by -1 do // best to work backwards!
            s1 := gens_wtd[j];
            s2 := news[k+2-j];
            if (#s1 gt 0) and (#s2 gt 0) then
              gen_os := &+[#gens_wtd[i] : i in [1..j-1]];
              for i1 in [1..#s1] do
                for i2 in [1..#s2] do
                  prod := s1[i1] * s2[i2];
                  Append(~poss_new,prod);
                  Append(~old,ConvertVec(
                     ChangeUniverse(Eltseq(prod),R1),mdeg));
                  Append(~newpols,pols[k+2-j][i2]*Q.(gen_os+i1));
                end for;
              end for;
            end if;
        end for;
        N1 := #old;
        new_bs := [i : i in [1..n] | val_bs[i] eq k];
        for j in new_bs do
           Append(~old,ConvertVec(ChangeUniverse(Eltseq(Bs[j]),R1),mdeg));
        end for;
        old := Solution(mat,old);
        V1 := Parent(old[1]); //KSpace rather than KModule!
        W := sub<V1|[old[j] : j in [1..N]]>;
        new_inds := [IntegerRing()|];
        for j in [N+1..N1] do
            if old[j] notin W then
                Append(~new_inds,j-N);
                W := sub<V1|W,old[j]>;
                if Dimension(V) eq Dimension(W) then break; end if;
            end if;
        end for;
        if Dimension(V) gt Dimension(W) then //new generators!
            comp := Complement(V1,W);
        else
            comp := sub<V1|>;
        end if;
        if ngens+Dimension(comp) ge n then
            // failed to find less generators!
            return [Q.i : i in [1..n]],Bs;
        end if;
        Append(~gens_wtd,[O!(h(V!v)) : v in Basis(comp)]);
        Append(~news, gens_wtd[k+1] cat [poss_new[j] : j in new_inds]);
        Append(~pols, [Q.(ngens+j) : j in [1..Dimension(comp)]] cat
                         [newpols[j] : j in new_inds]);
        if #new_bs ne 0 then
            all_pols := &cat[p : p in pols];
            V_b := VectorSpaceWithBasis( [W.i : i in [1..N]]
                                     cat Basis(comp) cat
                             [W.i : i in [N+1..Dimension(W)]]);
            for j in [1..#new_bs] do
                b_pols[new_bs[j]] :=
                   &+[coords[i]*all_pols[i] : i in [1..Dimension(V)]]
                    where coords is Coordinates(V_b,old[N1+j]);
            end for;
        end if;
        N := Dimension(V);
        ngens +:= Dimension(comp);
    end for;
    Q := PolynomialRing(BaseRing(R1),ngens);
    mp := hom<Universe(b_pols)->Q | [Q.i : i in [1..ngens]] cat
                                      [Q!0 : i in [ngens+1..n]] >;
    return [mp(b): b in b_pols],&cat[g : g in gens_wtd];

end function;

// Here f in k[x,y] is irreducible and separable over k(x) as
// a polynomial in y. The function uses the corresponding fn-fld
// and converts its maximal finite order given as a free k[x]-module 
// to k-algebra form. If bMinimise is true then it uses the above
// function to find a minimal(ish) set of generators of this k-alg.
function FFNormalisePrime(f,bMinimise)

    R := Generic(Parent(f));
    fld := BaseRing(R);
    K := RationalFunctionField(fld);
    P := PolynomialRing(K);
    mp := hom<R->P | [K.1,P.1]>;
    F := FunctionField( mp(f) : Check := false);

    O := MaximalOrderFinite(F);
    Bs := Basis(O);
    assert Bs[1] eq F!1;
    Bs[1] := F!(K.1);
    Bs := ChangeUniverse(Bs,O);
    n := #Bs;

    R1 := IntegerRing(K);
    P := PolynomialRing(fld,n);
    mp1 := hom<R1->P | [P.1]>;
    mp := hom<R->P | [P.1,&+[P|mp1(v[i])*P.i : i in [2..n]] + mp1(v[1])]>
               where v is Eltseq(O!(F.1));

    if n eq 1 then
        return ideal<P| >,mp;
    end if;
    // here n >1. Build relation matrix.
    M := RowSubmatrixRange(RepresentationMatrix(O!Bs[2]),2,n);
    for i in [3..n] do
      M := VerticalJoin(M,RowSubmatrixRange(RepresentationMatrix(O!Bs[i]),i,n));
    end for;

    I := ideal<P | [ (P.i)*(P.j)-&+[mp1(M[k,t])*P.t : t in [2..n]]-mp1(M[k,1])
              where k is (i-2)*n - ((i*(i-1)) div 2) + j :
                  i,j in [2..n] | i le j ] >;
    delete M;
    if (n eq 2) or (not bMinimise) then
        return I,mp;
    end if;

    pols,gens := FindMinimalGenerators(F,K,Bs);
    Q := Universe(pols);
    mp2 := hom<P->Q | pols>;
    qpols := [ &+[mp1(s[j])*(P.j) : j in [2..n]] + mp1(s[1]) where
                   s is Eltseq(g) : g in gens];
    // pols express the Bs in terms of the gens.
    // qpols express the gens in terms of the Bs.
    
    //"clean" the new relations a bit.
    lst := [mp2(b) : b in Basis(I)] cat 
                          [ Q.i - mp2(qpols[i]) : i in [1..#gens]];
    lst_cln := [Q|];
    for elt in lst do
        if (elt eq Q!0) or (elt in lst_cln) then
            continue;
        end if;
        Append(~lst_cln,elt);
    end for;   
    J := ideal<Q| lst_cln>;
    return J,mp*mp2;

end function;

// A particular NoetherNormalisation for a principal ideal <f> in a
// 2-generator polynomial ring. A change of vars is made so that
// f becomes monic in the second variable. If char(k) = p, the var
// change also guarantees that f(x,y) is separable over k(x) if f is
// irreducible (& it's assumed that f isn't a pth power in general).
function MakeMonic(f)

    P := Generic(Parent(f));
    fld := BaseRing(P);
    char := Characteristic(fld);
    idm := hom<P->P | [P.1,P.2]>;
    revm := hom<P->P | [P.2,P.1]>;
    d1 := Degree(f,1);
    d2 := Degree(f,2);
    td := TotalDegree(f);
    mx := TotalDegree(LeadingTerm(f,1)) eq d1; //monic in 1st var?
    my := TotalDegree(LeadingTerm(f,2)) eq d2; //monic in 2nd var?
    // add separability condition
    if char ne 0 then
      f_x := Derivative(f,1);
      f_y := Derivative(f,2);
      mx and:= f_x ne P!0;
      my and:= f_y ne P!0;
    end if;

    // if f monic in either variable, choose the one with least degree
    if (d2 le d1) and my then
        return f,idm;
    end if;
    if mx then
       revm := hom<P->P | [P.2,P.1]>; 
       return revm(f),revm;
    end if;
    if my then return f,idm; end if;
    
    // f isn't monic in either variable. First try a linear change 
    // in variables.
    sep_check := false;
    if char eq 0 then
        ch_lim := td;
    else
        // if char finite, we may have to worry about separability
        if IsDivisibleBy(td,char) then sep_check := true; end if;
        ch_lim := Ceiling(char/2);
    end if;
    
    Q := PolynomialRing(fld);
    lead_pol := &+[LeadingCoefficient(t)*(Q.1)^(Exponents(t)[2]) : 
                     t in Terms(f) | TotalDegree(t) eq td];

    i := 1; nrt := fld!0;
    for i in [1..ch_lim] do
        for elt in [fld!i,-fld!i] do 
	  if Evaluate(lead_pol,elt) ne fld!0 then
	     if (not sep_check) or ((f_y+elt*f_x) ne P!0) then
               nrt := elt; 
               break i;
	     end if;
          end if;
        end for;
    end for;
    if nrt ne fld!0 then
        mp :=  hom< P->P | [P.1+nrt*P.2,P.2] >;
        return mp(f),mp;
    end if;
    
    // if we're here, we've been unlucky in small characteristic!
    // now, 1st choose the variable with least degree to work with
    if d2 lt d1 then
       mp := hom<P->P | [P.2,P.1]>; 
       f1 := mp(f);
    else
       mp := idm;
       f1 := f;
    end if;    
    degs := [ Degree(t,1)+Degree(t,2) : t in Terms(f1,1)];
    // look for substitution x->x+y^r to give a unique maximal
    // degree term a power of y and also separability.
    r := 2;
    while true do
        degs := [degs[i]+i-1 : i in [1..#degs]];
        d,ind := Max(degs);
        if &and[degs[j] ne d : j in [ind+1..#degs]] then
           f2 := Evaluate(f1,1,P.1+(P.2)^r);
           // check separability
           if Derivative(f2,2) ne P!0 then break; end if;
        end if;
        r +:= 1;
    end while;
    return f2,mp * hom<P->P | [P.1+(P.2)^r,P.2]>;
        
end function;

// Main function for FunctionField normalisation.
function FunctionFieldNormalisation(I,bMin)

    P := Generic(I);
    assert (Rank(P) eq 2);
    idm := hom<P->P|[P.1,P.2]>;
    d := Dimension(I);
    if (d le 0) or (d eq 2) then
        return I,idm;
    end if;
    prims := RadicalDecomposition(I); //we assume I is Radical!
    res := [**];
    for prim in prims do
        if Dimension(prim) eq 0 then
            Append(~res,<prim,idm>);
            continue;
        end if;
        if #Basis(prim) ne 1 then // basis not grobner - unlikely!
            f := P!(Basis(EasyIdeal(prim))[1]);
        else
            f := Basis(prim)[1];
        end if;
        f,mp := MakeMonic(f);
        I, mp1 := FFNormalisePrime(f,bMin);
        Append(~res,<I,mp*mp1>);
    end for;
    return res;
    
end function;

//////// General functions for the computation of the ///////////
//  integral closure. The algorithm followed is basically the  //
// one given by De Jong in J. Symb. Comp. 26 (1998).           //

function Minor(M,rowinds,colinds)

    N := Matrix(#rowinds,[M[i,j] : j in colinds, i in rowinds]);
    return Determinant(N);
  
end function;

function EliminateGenerators(I)
/* I is an ideal in k[x_1,..,x_n]. "Naively" tries to eliminate generators
   of k[x]/I by looking at basis elements of I. Returns I1, the ideal with
   variables eliminated and the corr. hm:Generic(I) -> Generic(I1)        */
    P := Generic(I);
    n := Rank(P);
    B := Basis(I);
    ims := [P.i: i in [1..n]];
    for i := #B to 1 by -1 do
	pol := B[i];
	if pol eq 0 then Remove(~B,i); continue; end if;
	vars := [j : j in [1..n] | ((c ne 0) and (Degree(pol-c*P.j,P.j) le 0))
		where c is MonomialCoefficient(pol,P.j)];
	if #vars eq 0 then continue; end if;
	j := vars[1];
	subst := [P.k : k in [1..n]];
	subst[j] := (c*(P.j)-pol)/c where c is MonomialCoefficient(pol,P.j);
	ims := [Evaluate(f,subst): f in ims];
	Remove(~B,i);
	B := [Evaluate(f,subst): f in B];
    end for;
    vars := [j : j in [1..n] | ims[j] eq P.j];
    if #vars eq n then
	return I,hom<P->P|ims>;
    end if;
    Q := PolynomialRing(BaseRing(P),#vars);
    subst := [ind eq 0 select Q!0 else Q.ind where ind is Index(vars,j) :
		j in [1..n]];
    return ideal<Q|[Evaluate(b,subst): b in B]>,
		hom<P->Q|[Evaluate(f,subst): f in ims]>;
end function;

function HomogeneousQuotientBasis(I,J)
/* I > J are homogeneous ideals in k[x_1,..x_n] with the grevlex ordering.
   Function returns a minimal basis for I/J                                */

    P := Generic(I);
    n := Rank(P);
    mI := ideal<P|[P.i: i in [1..n]]>*I;
    //d := Degree(PolynomialRing(Rationals())!(HilbertSeries(mI)-HilbertSeries(I)));

    // find minimal basis of I directly as the vector space generated by
    // normal forms mod mI of generators of I
    BImI := [NormalForm(b,mI) : b in Basis(I)];
    mons := Setseq(&join[Seqset(Monomials(f)) : f in BImI]);
    Sort(~mons);
    V := KSpace(BaseRing(P),#mons);
    BV := Basis(V);
    WI := sub<V| [ &+[LeadingCoefficient(t)*BV[Index(mons,LeadingMonomial(t))]
		: t in Terms(b)] : b in BImI | b ne 0 ]>;

    // now find the subspace generated by J
    BJmI := [NormalForm(b,mI) : b in Basis(J)];
    WJ := sub<V| [ &+[LeadingCoefficient(t)*BV[Index(mons,LeadingMonomial(t))]
		: t in Terms(b)] : b in BJmI | b ne 0 ]>;

    U := Complement(WI,WJ);
    return [ &+[cs[i]*mons[i] : i in [1..#mons]] where cs is
		Eltseq(b) : b in Basis(U) ];

end function;

function SmallQuotientBasis(I,J)

     // Function to try to find a small set of generators of the
     // ideal I mod J (I contains J).
     //    ie b_1,..b_s with s small s.t. I = <J,b_1,..b_s>

    //do initial check - gives speed up when I = J!
    if I subset J then return []; end if;
    
    // homogenise and work with quotient modules - for
    // homogeneous modules over a polynomial ring, a genuine
    // minimal number of generators can be computed
    P := Generic(I);
    if IsHomogeneous(I) and IsHomogeneous(J) then
        Jh := ChangeOrder(J,"grevlex"); //guarantee grevlex order!
	Q := Generic(Jh);
	mp := hom<P->Q | [Q.i : i in [1..Rank(P)]]>;
        mpi := hom<Q->P | [P.i : i in [1..Rank(P)]]>;
	Ih := ideal<Q|[mp(b):b in Basis(I)]>;
    else
       Jh,mp := Homogenization(J,false);
       Q := Generic(Jh);
       mpi := hom<Q->P| [P.i : i in [1..Rank(P)]] cat [P!1]>;
       Ih := Homogenization(I,false);
       Ih := ideal<Q|[hm(b): b in Basis(Ih)]> where hm is
	hom<G->Q|[G.i: i in [1..Rank(G)]]> where G is Generic(Ih);
       //Ih := ideal<Q|[mp(b):b in Basis(I)]>+Jh;
    end if;
    /*M := Module(Q,1);
    MJ := quo<M | [[b] : b in Basis(Jh)]>;
    IJ := sub<MJ | [[mp(b)] : b in Basis(I)]>;
    MinB := MinimalBasis(IJ);*/
    MinB := HomogeneousQuotientBasis(Ih,Jh);
    return  [ mpi(mb) : mb in MinB ];
    
end function;

function HomJToJ(J,x,I,Ix)

    /* NB. Ix := ideal <I,x> is passed as an argument as it will
            already have a computed Grobner basis in general */
    P := Generic(I); n := Rank(P);
    vprint IntCl: "  Computing colon ideal.";
    xJJ := ColonIdeal(I+(J*ideal<P|x>),J);
    vprint IntCl: "  Finding small quotient basis.";
    Bs := SmallQuotientBasis(xJJ,Ix); // can this be improved to give a
                               // genuiniely minimal P-basis for xJJ/Ix ?!

    m := #Bs;
    vprintf IntCl: "  Number of new generators: %o\n",m;
    if m eq 0 then // Hom(J,J) = P/I
      return I,x;
    end if;
    Q := PolynomialRing(BaseRing(P),n+m);
    incl := hom<P->Q | [Q.i : i in [m+1..m+n]]>;
    x1 := incl(x);
/*  Simpler but generally slower (??) alternative:
    I1 := ideal<Q | [x1*Q.i-incl(Bs[i]) : i in [1..m]] cat
                        [incl(b) : b in Basis(I)]>;
    return ColonIdeal(I1,x1),x1;                           */

    // get nic(ish) basis for I
    vprint IntCl: "  Finding new relations...";
    I1,mp := EasyIdeal(I);
    BI := [b@@mp : b in Basis(I1)];
    vprint IntCl: "   Computing fixed ideal bases.";
    I1 := IdealWithFixedBasis([x] cat Bs cat BI);
    Ix1 := IdealWithFixedBasis([x] cat BI);
    // generate quadratic relations
    vprint IntCl: "   Determining quadratic relations.";
    R := [Q.j*Q.k - &+[incl(a[i+1])*Q.i : i in [1..m]] - incl(a[1])
            where a is Coordinates(I1,elt) 
             where elt is Coordinates(Ix1,Bs[j]*Bs[k])[1]:
                  j,k in [1..m] | j le k];
    delete I1,Ix1;
    // generate linear realations
    vprint IntCl: "   Determining linear relations.";
    M := SyzygyMatrix([x] cat Bs cat BI);
    syzs := [];
    for i in [1..NumberOfRows(M)] do
        r := [M[i][j] : j in [1..m+1]];
	if r notin syzs then Append(~syzs,r); end if;
    end for;    
    R1 :=  [ &+[incl(syz[j+1])*Q.j : j in [1..m]] + incl(syz[1])
               : syz in syzs ];

    return ideal<Q| [incl(b) : b in BI] cat R cat R1>,x1;

end function;

/* NB: The Jacobian criterion used here needs the assumption that the
       base field of the polynomial algebra is PERFECT (eg, finite or
       characteristic 0).                                            */
intrinsic Normalisation(I::RngMPol :
            UseFF := true, FFMin := true, UseMax := false, Prime := false) -> List
{Computes the integral closure, C, of P/I in its total ring of fractions
where P is Generic(I) and I is assumed to be radical. The result is a
list of <I_i,mp_i> such that C is the direct sum of Generic(I_i)/I_i and
mp_i gives the map from P to Generic(I_i) inducing P/I -> C. }
 
    P := Generic(I);
    n := Rank(P);
    if (n eq 2) and UseFF then
	vprint IntCl:"Using function field normalisation.";
        return FunctionFieldNormalisation(I,FFMin);
    end if;
    vprint IntCl: "Finding prime factors of ideal";
    if not Prime then
      facts := RadicalDecomposition(I);
    else
      facts := [I];
    end if;
    if n eq 1 then    //result trivial!
        return SequenceToList([<fact,idm> : fact in facts]) where
                  idm is hom<P->P | [P.1]>;
    end if;
    jac_elts := [P|];
    // find good elements in the jacobian matrices of the factors
    vprint IntCl: "Finding non-zero elements in jacobian ideals.";
    for J in facts do
       d := n-Dimension(J);
       JM := JacobianMatrix(Basis(J));
       // pick a random (non-zero) d*d minor of JM

/*
       for rowset in Subsets({1..NumberOfRows(JM)},d),
           colset in Subsets({1..NumberOfColumns(JM)},d) do
*/
       while true do
	    rowset := RandomSubset({1..Nrows(JM)},d);
	    colset := RandomSubset({1..Ncols(JM)},d);
	    rows := Isetseq(SetToIndexedSet(rowset));
	    cols := Isetseq(SetToIndexedSet(colset));
	    x := Minor(JM,rows,cols); // correct to sign!
	    if x notin J then
		break;
	    end if;
	    //end for;
       end while;

       Append(~jac_elts,x);
    end for;
    
    // now normalise each factor
    res := [**];
    for i in [1..#facts] do
      vprintf IntCl: "Dealing with prime factor %o.\n",i;
      J := facts[i]; x := jac_elts[i];
      Q := Generic(J);
      ims := [Q.j:j in [1..Rank(Q)]];
      while true do
	 J1 := J + ideal<Q|x>;
         if UseMax then
            J2 := ideal<Q|[Q.j : j in [1..Rank(Q)]]>;
	 else
	 vprint IntCl: " Computing radical of ideal.";
	    J2 := Radical(J1);
	    if IsRadical(J1) then  //J1 radical => Q/J integrally closed 
                break;
            end if;
	 end if;
	 vprint IntCl: " Computing Hom(J,J)...";
	 J,x := HomJToJ(J2,x,J,J1);
	 Q1 := Generic(J);
	 m := Rank(Q1) - Rank(Q);
         if m eq 0 then // Q/J integrally closed
            break;
         end if;
	 // try to reduce #generators of Q1
	 vprint IntCl: " Eliminating algebra generators.";
	 J,hm := EliminateGenerators(J);
	 vprintf IntCl: " Total number of generators: %o.\n",Rank(Generic(J));
	 x := hm(x);
	 ims := [Evaluate(f,seq): f in ims] where seq is
		  [hm(Q1.(j+m)) : j in [1..Rank(Q)]];
	 //ims := [Q1.j : j in [Rank(Q1)-Rank(P)+1..Rank(Q1)]];
	 Q := Generic(J);
      end while;
      Append(~res,< J, hom<P->Q | ims > >);
    end for;
    return res;

end intrinsic;
