freeze;
////////////////////////////////////////////////////////////////
//      Gonal maps and plane models for genus 6 curves        //
//            mch - 12/11                                     //
////////////////////////////////////////////////////////////////

import "gon_main.m": do_hyperelliptic_case, simplify_map;
import "cd1.m": parametrize_veronese;

function prime_ideal_to_point(P)
// P is a maximal ideal of polynomial ring R=k[x1,..xn]
// return a field L=k(alpha) which is the residue field R/P
// and the L-vector [x1 mod P,..,xn mod P]. Don't want to use
// FldAC as this gives the full splitting field

//NB: Assumed that Degree(P) le 5 and that if Degree(P)=4
// then R/P isn't a Galois extension of k [actually Deg(P)=4
// should never happen here anyway]

    R := Generic(P);
    k := BaseRing(R);
    n := Rank(R);

    GB := GroebnerBasis(P);
    assert #GB eq n;
    subs := [k!0 : i in [1..n]];
    j := n;
    while Degree(GB[j],j) eq 1 do
	cs := Coefficients(GB[j],j);
	assert cs[2] eq 1;
	subs[j] := -(k!cs[1]);
	j -:= 1;
	if j eq 0 then break; end if;
    end while;
    if j eq 0 then return subs; end if;
    pol := UnivariatePolynomial(GB[j]);
    L<a> := ext<k|pol>;
    ChangeUniverse(~subs,L);
    subs[j] := a;
    while j gt 1 do
	j -:= 1;
	f := GB[j];
	cs := Coefficients(f,j);
	assert #cs eq 2;
	assert cs[2] eq 1;
	subs[j] := -Evaluate(cs[1],subs);   
    end while;
    return subs;

end function;

function deg_2_map(C)
// C is a projective normal genus 1 curve. Return a degree 2 map to P^1
//  maybe over a field extension of the basefield.
//  Can we improve this???

    P := Ambient(C);
    n := Rank(CoordinateRing(P)); //only use for n=5 here
    k := BaseRing(P);
    pt := 0;
    if k cmpeq Rationals() then
	pts := PointSearch(C,10);
	if #pts gt 0 then
	    pt := pts[1];
	end if;
    elif Type(k) eq FldFin then
	pts := RationalPointsByFibration(C:Max := 1);
	if #pts gt 0 then
	    pt := Representative(pts);
	end if;	
    end if;
    // in other cases, just look for a really obvious point
    if Type(pt) eq RngIntElt then
	seq := [k!0 : i in [1..n]];
	for i in [1..n] do
	    ptseq := seq;
	    ptseq[i] := k!1;
	    boo,pt1 := P!ptseq in C;
	    if boo then pt := pt1; break; end if;
	end for;
    end if;

    L := k;
    if Type(pt) eq RngIntElt then
	// decompose a hyperplane section
	Z := C meet Scheme(P,P.1);
	Zs := PrimeComponents(Z);
	degs := [Degree(Z) : Z in Zs];
	md,i := Min(degs);
	Z := Zs[i];
	Saturate(Z);
	if md eq 1 then
	   pt := Representative(Support(Z));
	   pt := C!Eltseq(pt);
	elif md eq 2 then //assume n=5
	   assert #degs eq 2;
	   assert degs[3-i] eq 3;
	   Z := Zs[3-i];
	   Saturate(Z);
	   rr := [l : l in Basis(Ideal(Z)) | TotalDegree(l) eq 1];
	   assert #rr eq 2;
	   return map<C->Curve(ProjectiveSpace(L,1))|rr>;
	else
	   I := Ideal(Z);
	   i := 0;
	   for j in[1..n] do
	     if P.(n-j) notin I then i := j; break; end if;
	   end for;
	   assert i gt 0;
	   I := Ideal(AffinePatch(Z,i)); 
	   ptseq := prime_ideal_to_point(I);
	   L := Universe(ptseq);
	   Insert(~ptseq,n+1-i,L!1);
	   C := BaseChange(C,L);
	   pt := C!ptseq;
	end if;
    end if;

    I := Ideal(Cluster(P!pt));
    I := Saturation(I^(n-2)+Ideal(C));
    rr := [l : l in Basis(I) | TotalDegree(l) eq 1];
    assert #rr eq 2;
    return map<C->Curve(ProjectiveSpace(L,1))|rr>;    
    
end function;

function get_Y(X,res)
// return the uniquely determined surface Y that contains the 4-gonal canonical
//  genus 6 curve X

    R := CoordinateRing(Ambient(X));
    mp0 := Matrix(BoundaryMap(res,1));
    mp1 := Matrix(BoundaryMap(res,2));
    mp2 := Matrix(BoundaryMap(res,3));
    deg1 := [Max([LeadingTotalDegree(e) : e in r | e ne 0]) : 
			r in RowSequence(mp1)];
    deg2 := [Max([LeadingTotalDegree(e) : e in r | e ne 0]) : 
			r in RowSequence(Transpose(mp2))];
    assert Sort(deg1) eq [1: i in [1..5]] cat [2: i in [1..5]];
    assert &and[deg1[i]+deg2[i] eq 3 : i in [1..10]];

    perm := [i : i in [1..10] | deg1[i] eq 1] cat 
	[i : i in [1..10] |deg1[i] eq 2];
    iperm := [Index(perm,i) : i in [1..10]];

    mat1 := Matrix([mp1[p] : p in perm]);
    mat11 := RowSubmatrix(mat1,1,5);
    matf := Matrix([[MonomialCoefficient(mat11[k,j],R.i) : j in [1..Ncols(mat11)]]
           :i in [1..6], k in [1..Nrows(mat11)]]);
    b := Basis(Kernel(Transpose(matf)))[1];
    V := Kernel(Transpose(Matrix(b)));
    assert Dimension(V) eq 5;
    matV := EchelonForm(Matrix(Basis(V))); //EchelonForm usually unnecessary!
    B := Eltseq(ChangeRing(matV,R)*Matrix(mp0));
    return Scheme(Ambient(X),B),matV;

end function;

function Y_is_ell_cone(Y)
// Y is an anticanonical degree 5 Del Pezzo (maybe singular) or an
// elliptic cone in P^5. Returns whether it is an elliptic cone
// and, if so, a linear change of coords so that the vertex
// is at [0,0,0,0,0,1] and the transformed Y

    P5 := Ambient(Y);
    sngs := ReducedSubscheme(SingularSubscheme(Y));
    if Degree(sngs) ne 1 then return false,_,_; end if;
    pt := Representative(Support(sngs));
    V := Kernel(Matrix(6,1,Eltseq(pt)));
    mat := EchelonForm(Matrix(Basis(V))); //EchelonForm usually unnecessary!
    inds := [Min(Support(mat[i])) : i in [1..5]];
    inds := [i : i in [1..6] | i notin inds];
    assert #inds eq 1;
    R := CoordinateRing(P5);
    K := BaseRing(R);
    vec := [K!0 : i in [1..6]];
    vec[inds[1]] := K!1;
    mat := Matrix(RowSequence(mat) cat [vec]);
    mons := [R.i : i in [1..6]];
    lins := [Polynomial(r,mons) : r in RowSequence(mat)];
    mati := mat^-1;
    linsi := [Polynomial(r,mons) : r in RowSequence(mati)];
    defs := [Evaluate(f,linsi) : f in DefiningPolynomials(Y)];
    if not &and[#Coefficients(f,R.6) eq 1 : f in defs] then
	return false,_,_;
    end if;
    Y1 := Scheme(P5,defs);
    trans := iso<P5->P5|lins,linsi : Check := false>;
    return true,Y1,trans;

end function;

function process_data(ap_data)
// from the list of solutions for the different Grassmannian patches, recover
// the overall set of (<= 5) solutions

    if ap_data[#ap_data][1] eq 5 then
	dat := ap_data[#ap_data];
	pcs := RadicalDecomposition(dat[2]);
	return [<Degree(Homogenization(p)),p,dat[3]> : p in pcs]; 
    end if;

    tot_deg := Max([d[1] : d in ap_data]);
    i := [j : j in [1..#ap_data] | ap_data[j][1] eq tot_deg][1];
    dat := ap_data[i];
    pcs := RadicalDecomposition(dat[2]);
    lst := [<Degree(Homogenization(p)),p,dat[3]> : p in pcs];

end function;

function get_mat_from_ap_data(dat,mat)
// return the 2x3 matrix giving the scroll coming from ap_data solution dat.
//  mat is the 5x5 matrix of linear forms giving R(-3)^5 -> R(-2)^5

    I := dat[2];
    c1,c2,d1,d2,d3 := Explode(dat[3]);
    k := BaseRing(I);
    if dat[1] eq 1 then
      P := Generic(I);
      rs := [k!NormalForm(P.i,I) : i in [7..9]];
      ss := [k!NormalForm(P.i,I) : i in [10..12]];
      L := k;
    else
      vec := prime_ideal_to_point(I);
      rs := vec[7..9];
      ss := vec[10..12];
      L := Universe(vec);
    end if;
    M := ZeroMatrix(L,2,5);
    M[1,c1] := 1; M[2,c2] := 1;
    inds := [i : i in [1..5] | i notin [c1,c2]];
    for i in [1..3] do
	M[1,inds[i]] := rs[i]; M[2,inds[i]] := ss[i];
    end for;

    R := BaseRing(mat);
    if not (L cmpeq k) then
	R := ChangeRing(R,L);
	mat := ChangeRing(mat,R);	
    end if;
    matsol := Submatrix(ChangeRing(M,R)*mat,[1,2],[d1,d2,d3]);
    return matsol,(L cmpeq k);

end function;

function g_1_4_ap_data(X,res,matY)
// X is a gonality 4 canonical genus 6 curve (with Y a Del Pezzo), res is the 1 6 10 6 1
//  minimal free resolution of R/IX. The rows of matY give the generators of the
//  5D subspace of R(-2)^6 that map onto the space of quadrics generating Y in res. 

    // Restrict the map R(-3)^5 -> R(-2)^6 to R(-3)^5 -> R(-2)^5
    R := CoordinateRing(Ambient(X));
    mp0 := Matrix(BoundaryMap(res,1));
    mp1 := Matrix(BoundaryMap(res,2)); // R(-2)^5+R(-3)^5 -> R(-2)^6
    mp2 := Matrix(BoundaryMap(res,3)); // R(-4)^6 -> R(-2)^5+R(-3)^5

    // permute the rows/cols at the rank 10 part of res to split into R(-3)^5+R(-4)^5
    //  mat1 will be the 6x5 matrix linear form matrix giving R(-3)^5 -> R(-2)^6
    deg1 := [Max([LeadingTotalDegree(e) : e in r | e ne 0]) : 
			r in RowSequence(mp1)];
    deg2 := [Max([LeadingTotalDegree(e) : e in r | e ne 0]) : 
			r in RowSequence(Transpose(mp2))];
    assert Sort(deg1) eq [1: i in [1..5]] cat [2: i in [1..5]];
    assert &and[deg1[i]+deg2[i] eq 3 : i in [1..10]];

    perm := [i : i in [1..10] | deg1[i] eq 1] cat 
	[i : i in [1..10] |deg1[i] eq 2];
    iperm := [Index(perm,i) : i in [1..10]];
    mat1 := Matrix([mp1[p] : p in perm]);
    mat1 := RowSubmatrix(mat1,1,5);

    // restrict to R(-3)^5 -> R(-2)^5
    inds := [Min(Support(matY[i])) : i in [1..5]];
    assert #Seqset(inds) eq 5;
    mat1r := Transpose(Matrix([r[i] : i in inds])) where r is RowSequence(Transpose(mat1));

    // Determine pairs (rank 2 direct summand M, rank 3 direct summand N) s.t. mat1r maps M -> N
    // M will be generated by vectors [1 0 r1 r2 r3], [0 1 s1 s2 s3] with some permutation of the 
    // columns.
    // N will be generated by vectors [1 0 0 u1 u2], [0 1 0 v1 v2], [0 0 1 w1 w2] with some
    // permtation of the columns

    P := PolynomialRing(BaseRing(X),12);
    AssignNames(~P,
	["u" cat IntegerToString(i) : i in [1..2]] cat
	["v" cat IntegerToString(i) : i in [1..2]] cat
	["w" cat IntegerToString(i) : i in [1..2]] cat
	["r" cat IntegerToString(i) : i in [1..3]] cat
	["s" cat IntegerToString(i) : i in [1..3]]);
    u1 := P.1; u2 := P.2;
    us := [P.i : i in [1,2]];
    v1 := P.3; v2 := P.4;
    vs := [P.i : i in [3,4]];
    w1 := P.5; w2 := P.6;
    ws := [P.i : i in [5,6]];
    r1 := P.7; r2 := P.8; r3 := P.9;
    rs := [P.i : i in [7..9]];
    s1 := P.10; s2 := P.11; s3 := P.12;
    ss := [P.i : i in [10..12]];
    PR := PolynomialRing(P,6);
    mat1R := ChangeRing(mat1r,PR);

    ap_data := [**];
    bdone := false;
    tot_deg := 0;

    for d1 in [1..3] do 
    for d2 in [d1+1..4] do 
    for d3 in [d2+1..5] do
    for c1 in [1..4] do 
    for c2 in [c1+1..5] do

      rels0 := [P|];
      // build the matrices for M and N with permutation of cols echelonising them and
      //  based on ci di, echelonise them and set various ri,si.. =0 in rels0
      matrs := ZeroMatrix(P,2,5);
      matuvw := ZeroMatrix(P,3,5);
      rels0 cat:= rs[1..c1-1]; matrs[1,c1] := 1; j := c1;
      for i in [k : k in [c1+1..5] | k ne c2] do matrs[1,i] := rs[j]; j +:= 1; end for;
      rels0 cat:= ss[1..c2-2]; matrs[2,c2] := 1; j := c2-1;
      for i in [c2+1..5] do matrs[2,i] := ss[j]; j +:= 1; end for;
      rels0 cat:= us[1..d1-1]; matuvw[1,d1] := 1; j := d1;
      for i in [k : k in [d1+1..5] | (k ne d2) and (k ne d3)] do matuvw[1,i] := us[j]; j +:= 1; end for;
      rels0 cat:= vs[1..d2-2]; matuvw[2,d2] := 1; j := d2-1;
      for i in [k : k in [d2+1..5] | k ne d3] do matuvw[2,i] := vs[j]; j +:= 1; end for;
      rels0 cat:= ws[1..d3-3]; matuvw[3,d3] := 1; j := d3-2;
      for i in [d3+1..5] do matuvw[3,i] := ws[j]; j +:= 1; end for;
//Append(~ap_data,<matrs,matuvw,rels0,[c1,c2,d1,d2,d3]>); continue;
      // matrix whose rows give the image of M in R(-2)^5
      Ls := ChangeRing(matrs,PR)*mat1R;

      // get equations for inclusion of M into N
      seq := [d1,d2,d3];
      rels := &cat[[r[i]-&+[matuvw[j,i]*r[seq[j]] : j in [1..3]]
	: i in [1..5] | i notin seq] : r in RowSequence(Ls)];
      rels1 := Setseq( Exclude( Seqset(&cat[[MonomialCoefficient(e,PR.i) : 
	i in [1..6]] : e in rels]), P!0) );

      I := ideal<P|rels0 cat rels1>;
      dim := Dimension(I);
      assert dim le 0;
      if dim eq 0 then
        deg := Degree(Homogenization(I));
	tot_deg +:= deg;
	if tot_deg ge 5 then bdone := true; end if;
	Append(~ap_data,<deg,I,[c1,c2,d1,d2,d3]>);
      end if;
      if bdone then break; end if;
    end for;
      if bdone then break; end if;
    end for;
      if bdone then break; end if;
    end for;
      if bdone then break; end if;
    end for;
      if bdone then break; end if;
    end for;

    apd := [dat : dat in ap_data | dat[1] eq 1];
    if true or (#apd eq 0) then
      apd := [];
      for dat in ap_data do
	if dat[1] eq 1 then
	    Append(~apd,dat);
	else
	    pcs := RadicalDecomposition(dat[2]);
	    for p in pcs do
		Append(~apd,<Degree(Homogenization(p)),p,dat[3]>);
	    end for;
	end if;
      end for;
    end if;
    ap_data := apd;
    return ap_data,mat1r;

end function;

function do_general_gen_6(X,res)
// For the generic (up to Y-type) genus 6 case. When Y is an elliptic cone, return
//  0,prj where prj is a degree 2 map of X to a projrctivr normal genus 1 curve in
//  P^4. When Y is a Del Pezzo return 1,mat where mat is the 2x3 matrix of linear
//  forms over a field of smallest degree over the base field s.t. the minors of
//  mat give a deg 3 dim 3 scroll containing X.

    // determine if Y is Del Pezzo or ell cone. In the ell cone case, handle differently.
    Y,matY := get_Y(X,res);
    boo_ell,Y1,trY1 := Y_is_ell_cone(Y);
    if boo_ell then //elliptic cone case
       P4 := ProjectiveSpace(BaseRing(X),4);
       E := Curve(P4,[Evaluate(f,[P4.i : i in [1..5]] cat [0]) : f in
			DefiningPolynomials(Y1)]);
       prj := map<X->E|(DefiningPolynomials(trY1))[1..5] : Check := false>;
       return 0,prj;
    end if;
    //general case (Y a Del Pezzo)
    ap_data,mat := g_1_4_ap_data(X,res,matY);
    d_min := Min([dat[1] : dat in ap_data]);
    dat := [d : d in ap_data | d[1] eq d_min][1];
    mat_scr := get_mat_from_ap_data(dat,mat);
    return 1,mat_scr;

end function;

function gonality_4_map(X,res)

    boo,val := do_general_gen_6(X,res);
    k := BaseRing(X);
    if boo eq 0 then // Y an elliptic cone case
	mp1 := deg_2_map(Codomain(val));
	L := BaseRing(Domain(mp1));
	if not (L cmpeq k) then
	  X1 := BaseChange(X,L);
	  val1 := map<X1->Domain(mp1)|[R!f : f in DefiningPolynomials(val)]>
			where R is CoordinateRing(Ambient(X1));
	else
	  val1 := val;
	end if; 
	return boo,Expand(val1*mp1),val;
    end if;
    // Y a Del Pezzo case
    L := BaseRing(BaseRing(val));
    if not (k cmpeq L) then
	X1 := BaseChange(X,L);
    else
	X1 := X;
    end if;
    return boo,map<X1->Curve(ProjectiveSpace(L,1))|[val[1,1],val[2,1]]>,_;

end function;

function general_plane_model(C,res)
// finds a birational map to a degree 6 plane model (maybe over a finite extn)
//  for C a general type (gonailty 4, Y a Del Pezzo) canonical curve of genus 6

   boo,mat := do_general_gen_6(C,res);
   if boo eq 0 then return false,_; end if; //Y an elliptic cone
   k := BaseRing(C);
   K := BaseRing(BaseRing(mat));
   if not (k cmpeq K) then
	C1 := BaseChange(C,K);
   else
	C1 := C;
   end if;
   R1 := CoordinateRing(Ambient(C1));
   if not (k cmpeq K) then
	mat := Matrix(R1,2,3,[R1!f : f in Eltseq(mat)]);
   end if;

   // we want D where D has degree 6, |D| is a g^2_6 where D is GCD((l1),(l2))
   // [|K-D| is given by the sections of <l1,l2>-D]
   //  compute via ColonIdeal except in some degenerate cases
   l1 := mat[1,1]; l2 := mat[2,1];
   I1 := Ideal(C1)+ideal<R1|l1>;
   ID := ColonIdeal(I1,l2);
   if Degree(ID) ne 4 then
      ID := ColonIdeal(I1,ideal<R1|l2>);
      ID := Saturation(ID);
   end if;
   assert Degree(ID) eq 4;
   lins := [l : l in Basis(ID) | TotalDegree(l) eq 1];
   assert #lins eq 3;

   mp := map<C1 -> ProjectiveSpace(K,2)|lins>;
   C6 := mp(C1);
   return true,map<C1->C6|lins : Check := false>;

end function;

function point_on_quintic(C)
// C is a non-singular quintic curve in P2. Returns the sequence of
// coordinates of a point on C (over an extn field)

    k := BaseRing(C);
    if Type(k) cmpeq FldRat then
	pts := PointSearch(C,100);
	if #pts gt 0 then 
	  pt := pts[1];
	  return Eltseq(pt);
	end if;
    elif Type(k) cmpeq FldFin then
	pts := RationalPointsByFibration(C : Max := 1);
	if #pts gt 0 then
	  pt := pts[1];
	  return Eltseq(pt);
	end if;
    end if;
    pts := Scheme(C,Ambient(C).1);
    pts := PrimeComponents(pts);
    degs := [Degree(p) : p in pts];
    m := Min(degs);
    pt := pts[Index(degs,m)];
    i := 3;
    pta := AffinePatch(pt,1);
    if IsEmpty(pta) then
	i := 2; pta := AffinePatch(pt,2);
    end if;
    GB := GroebnerBasis(Ideal(pta));
    R1 := Generic(Universe(GB));
    if Degree(GB[2],R1.2) eq 1 then
	e := -MonomialCoefficient(GB[2],R1!1)/
			MonomialCoefficient(GB[2],R1.2);
	f := UnivariatePolynomial(GB[1]);
	K := ext<k|f>;
	pt_seq := [K.1,e];
    else
	f := UnivariatePolynomial(GB[2]);
	K := ext<k|f>;
	P := PolynomialRing(K);
	f1 := Evaluate(GB[1],[P.1,K.1]);
	e := -Coefficient(f1,0)/Coefficient(f1,1);
	pt_seq := [e,K.1];
    end if;
    Insert(~pt_seq,i,1);
    return pt_seq;

end function;

intrinsic Genus6GonalMap(C::Crv : DataOnly := false, IsCanonical:=false) -> 
		RngIntElt,RngIntElt,MapSch,MapSch
{Computes smallest degree (gonal) maps to P^1 for a genus 6 curve, possibly over
a finite extension of the base field. Returns the gonality, a secondary type number,
and a map if DataOnly is false. The type number (1,2,3) is only relevant for
gonality 4. In the gonality 4 case, also returns a degree 2 cover of a genus 1 curve
(type 2) or an isomorphism to a plane quintic (type 3). If C is a canonical curve in
ordinary projective space, IsCanonical should be set to true for efficiency}

    if IsCanonical then
	assert IsOrdinaryProjective(C);
	bHyp := false;
	g := Rank(CoordinateRing(Ambient(C)));
	cmap := IdentityMap(C);
	is_can := true;
    else
      g,bHyp,cmap := GenusAndCanonicalMap(C);
      is_can := (Domain(cmap) cmpeq Codomain(cmap));
    end if;
    require g eq 6: "C should be a curve of genus 6";
    if bHyp then
        if DataOnly then return 2,_,_,_,_; end if;
	mp := do_hyperelliptic_case(C,cmap);
	return 2,1,mp,_;
    end if;
    Cc := Codomain(cmap);//canonical image
    k := BaseRing(Cc);
    if &or[TotalDegree(f) eq 3 : f in DefiningPolynomials(Cc)] then
	//gonality 3 or plane quintic case
	require Characteristic(k) ne 2:
		"Sorry. Can't do the gonality 3 case in characteristic 2";
	X := Scheme(Ambient(Cc),[f : f in DefiningPolynomials(Cc) |
					TotalDegree(f) eq 2]);
	phi := CliffordIndexOne(Cc,X);
	if Dimension(Ambient(Codomain(phi))) eq 1 then //gonality 3
	  if DataOnly then return 3,_,_,_,_; end if;
	  K := BaseRing(Domain(phi));
	  if (not is_can) and (not (K cmpeq k)) then
	    CK := BaseChange(C,K); CcK := Domain(phi);
	    cmap := map<CK->CcK|defs> where defs is 
		[R1!f : f in DefiningPolynomials(cmap)] where
		  R1 is CoordinateRing(Ambient(CK));
	  end if;
	  if not is_can then
	    phi := Expand(cmap*phi);
	    phi := simplify_map(phi);
	  end if;
	  return 3,1,phi,_;
	else //plane quintic case
	  if not is_can then
	    phi := Expand(cmap*phi);
	    phi := simplify_map(phi);
	  end if;
	  if DataOnly then return 4,3,_,phi; end if;
	  pt := point_on_quintic(Codomain(phi));
	  K := Universe(pt);
	  if K cmpeq k then
	    defs := DefiningPolynomials(phi);
	    CK := C;
	    P2K := Ambient(Codomain(phi));
	  else
	    CK := BaseChange(C,K);
	    QK := BaseChange(Codomain(phi),K);
	    defs := [R1!f : f in DefiningPolynomials(phi)] where
		  R1 is CoordinateRing(Ambient(CK));
	    P2K := Ambient(QK);
	  end if;
	  _,prj := Projection(P2K,P2K!pt);
	  vs := [Evaluate(f,defs) : f in DefiningPolynomials(prj)];
	  mp := map<CK->Curve(ProjectiveSpace(K,1))|vs : Check := false>;
	  return 4,3,mp,phi;
	end if;
    else
	//gonality 4 (general) case
	res := MinimalFreeResolution(QuotientModule(Ideal(Cc)));
	boo,mp1,mp2 := gonality_4_map(Cc,res);
	if (boo eq 0) and not is_can then 
	   mp2 := Expand(cmap*mp2);
	   mp2 := simplify_map(mp2);
        end if;
	if DataOnly then
	  if boo eq 0 then
	    return 4,2,_,mp2;
	  else
	    return 4,1,_,_;
	  end if;
	end if;
	K := BaseRing(Domain(mp1));
	if not (K cmpeq k) then
	    CK := BaseChange(C,K); CcK := Domain(mp1);
	    cmap := map<CK->CcK|[R1!f : f in DefiningPolynomials(cmap)] :
		Check := false> where R1 is CoordinateRing(Ambient(CK));
	end if;
	mp1 := Expand(cmap*mp1);
	if not is_can then 
	  mp1 := simplify_map(mp1);
	end if;
	if boo eq 0 then
	  return 4,2,mp1,mp2;
	else
	  return 4,1,mp1,_;
	end if;	
    end if;

end intrinsic;

intrinsic Genus6PlaneCurveModel(C::Crv : IsCanonical:=false ) -> BoolElt, MapSch
{ Returns a birational map to a degree 5 or 6 plane curve (maybe over an extension
  of the base field) from genus 6 curve C, when C is 4-gonal and not a double cover
  of a genus 1 curve. The first return value is whether C is of the correct type and
  the second is the map if so. If C is a canonical curve in ordinary projective space,
  IsCanonical should be set to true for efficiency } 

    if IsCanonical then
	assert IsOrdinaryProjective(C);
	bHyp := false;
	g := Rank(CoordinateRing(Ambient(C)));
	cmap := IdentityMap(C);
	is_can := true;
    else
      g,bHyp,cmap := GenusAndCanonicalMap(C);
      is_can := (Domain(cmap) cmpeq Codomain(cmap));
    end if;
    require g eq 6: "C should be a curve of genus 6";
    if bHyp then return false,_; end if;
    Cc := Codomain(cmap);//canonical image
    k := BaseRing(Cc);
    if &or[TotalDegree(f) eq 3 : f in DefiningPolynomials(Cc)] then
	X := Scheme(Ambient(Cc),[f : f in DefiningPolynomials(Cc) |
		TotalDegree(f) eq 2]);
	Repr := myFindLieAlgebra(Ideal(X));
	L := Domain(Repr);
	_, ls := HasLeviSubalgebra(L);
	if Dimension(ls) eq 8 then // X is Veronese, Cc is IM to a smooth plane quintic
	  phi := parametrize_veronese(X,L,Repr);
	  defs := DefiningPolynomials(Inverse(phi));
	  C5 := Image(map<Cc->Domain(phi)|defs>);
	  phi := iso<Cc->C5|defs,DefiningPolynomials(phi) : Check := false>;
	  if not is_can then
	    phi := Expand(cmap*phi);
	    phi := simplify_map(phi);
	  end if;
	  return true,phi;
	else // X a rational scroll and C has gonality 3
	  return false,_; //trigonal case
	end if;
    end if;
    //gonality 4, Clifford index > 1
    if IsOrdinaryProjective(C) and (Dimension(Ambient(C)) eq 2) then
	if Degree(C) eq 6 then return true,IdentityMap(C); end if;
    end if;
    res := MinimalFreeResolution(QuotientModule(Ideal(Cc)));
    boo,phi := general_plane_model(Cc,res);
    if not boo then return boo,_; end if;
    if not is_can then
	K := BaseRing(Domain(phi));
	if not (K cmpeq k) then
	    CK := BaseChange(C,K); CcK := Domain(phi);
	    cmap := map<CK->CcK|[R1!f : f in DefiningPolynomials(cmap)] :
		Check := false> where R1 is CoordinateRing(Ambient(CK));
	end if;
	phi := Expand(cmap*phi);
	phi := simplify_map(phi);	
    end if;
    return true,phi;

end intrinsic;
