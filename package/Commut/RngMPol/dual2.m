freeze;
////////////////////////////////////////////////////////////////////////
//        Some functions used in sheaf.m - mch                        //
////////////////////////////////////////////////////////////////////////

import "homogeneous.m": GradModCpx, GradModMap, GradMod;
import "homogeneous.m": GetPresentation;

declare attributes RngMPol : quotient_module;
declare attributes ModMPol : canonical_module;

//////////////////////////////////////////////////////////////////
/////////// Projection to noether normalisation intrinsic ////////

function MyMinimise(M,boohms)
/* 
   Takes a matrix M whose rows gives the relations for a module mod
   and returns a new matrix which give the relations wrt a minimal
   basis. [Temporary hack while core function is unavailable!]
*/
    if boohms then
      tr := IdentityMatrix(BaseRing(M),Ncols(M));
      gens := [1..Ncols(M)];
      n0 := Ncols(M);
    end if;
    while true do
	ind := Index([TotalDegree(m) : m in Eltseq(M)],0);
        if ind eq 0 then break; end if; // M has no non-zero constant terms
        nc := Ncols(M); nr := Nrows(M);
	if nc eq 1 then
	  if boohms then
	    return Matrix(BaseRing(M),0,0,[]),Matrix(BaseRing(M),n0,0,[]),
		[Integers()|];
	  else 
	    return Matrix(BaseRing(M),0,0,[]);
	  end if;
	end if;
        row := Floor((ind-1)/nc) + 1;
	col := ind - (row-1)*nc;
	// M[row,col] is constant - eliminate variable col and 
	// adjust M accordingly
	MultiplyRow(~M,-1/M[row,col],row);
	for i in [1..nr] do
	    if i eq row then continue; end if;
	    AddRow(~M,M[i,col],row,i);
	end for;
	// remove row row and column col
	M := HorizontalJoin( ColumnSubmatrix(M,col-1),
		ColumnSubmatrix(M,col+1,nc-col) );
	if boohms then 
	  tr *:= Matrix([rs[i]: i in [1..col-1]] cat [Eltseq(M[row])] cat
		[rs[i]: i in [col..nc-1]]) where rs is
		RowSequence(IdentityMatrix(BaseRing(M),nc-1));
	  Remove(~gens,col);
	end if;
	M := VerticalJoin(RowSubmatrix(M,row-1),RowSubmatrix(M,row+1,nr-row));
    end while;
    if boohms then 
      return M,tr,gens;
    else
      return M;
    end if;	
end function;

function MyAnnihilator(M)
 // M is a ModMPol in presentational form over R. Returns the
 // annihilator of M: an ideal of R

 mat := RelationMatrix(M); 
 R := BaseRing(mat);
 r := Nrows(mat);
 s := Ncols(mat);
 
 // do special cases first
 if r eq 0 then 
    return ideal<R|>;
 end if;
 if s eq 1 then
    return ideal<R|Eltseq(mat)>;
 end if;
 if r eq 1 then
    return &meet[ideal<R|m> : m in Eltseq(mat)];
 end if;
  
 I := ideal<R|R!1>;
 F := Module(R,s-1);
 
 for i in [1..s] do
   modu := sub<F|[F!Eltseq(M1[j]) : j in [1..r]]>
	where M1 is RemoveColumn(mat,i);
   syzs := [Eltseq(b) : b in Basis(SyzygyModule(modu))];
   I meet:= ideal<R | [ &+[mat[j,i]*syz[j]:j in [1..s]] : syz in syzs]>;
 end for;
 
 return I;
 
end function;

/*
function process_relations(G,Gx_inds,Gy,cwts,d)
// In the module case, the Gy relations may not give all relations
// in the projected module. It's possible that some of the Gx relations
// that produce generators can also be modified by Gy relations to
// produce new Gy relations! We do that here.

    if #Gx_inds eq 0 then return Gy; end if;
    R := Parent(G[1][1]);
    n := Rank(R);
    r := #Eltseq(G[1]);
    // Create "Gx"-module and "Gy"-modules for further reduction
    G1 := [G[i] : i in Gx_inds];
    Gy1 := Gy;
    F := Generic(Parent(G1[1]));
    Gxmod := sub<F | G1>;
    Gymod := sub<F | Gy>;
    
    done := false;
    while not done do
      done := true;
      for j := #G1 to 1 by -1 do
	g := G1[j];
	lm := LeadingTerm(g);
	i := [k: k in [1..r]|lm[k] ne 0][1];
	lm := Eltseq(lm)[i];
	eg := Exponents(lm);
	h := 0;
	for h1 in Gy do
	   lh := h1[i];
	   if IsZero(lh) or (&or[e[k] ne 0 : k in [1..n-d]] where e is 
		Exponents(LeadingMonomial(lh))) then
		 continue;
	   end if;
	   ts := [t : t in Terms(lh) | &or[e[k] ne 0 : k in [1..n-d]]
		where e is Exponents(t)];
	   ts := [t : t in ts | &and[e[k] le eg[k] : k in [1..n-d]]
		where e is Exponents(t)];
	   if #ts eq 0 then continue; end if;
	   t := ts[1]; 
	   t1 := Monomial(R,[0: k in [1..n-d]] cat [e[k] : k in [n-d+1..n]])
		where e is Exponents(t);
	   h := h1; break;
	end for;
	if h cmpeq 0 then continue; end if;
	v := (LeadingCoefficient(t)*t1)*g-((lm*t1) div LeadingMonomial(t))*h;
	v := NormalForm(v,Gxmod);
//error "lard!";
	//v := NormalForm(v,Gymod);
	if v notin Gymod then
	  Gy1 := Append(Gy1,v);
	  Gymod := sub<F | Gy1>;
	  Remove(~G1,i);
	  done := false;
	end if;	
      end for;
    end while;
    return Gy1;

end function;
*/

intrinsic ModuleProjectM(M::ModMPol,Ry::RngMPol) -> ModMPol,SeqEnum
{}
/* 
   takes graded module M over S=k[x_1,..x_n], finite over Ry=k[y_1,..y_d]
   if y_i is mapped to x_(n-d+i), and returns the corresponding
   module over k[y_1,..,y_d] as a reduced (ie presentational) module.

   as well as returning M, the function also returns a sequence of
   r*r matrices (where M = Ry^r/relations) giving the actions of
   x_1,..,x_(n-d) on M, so that the S-module structure can be recovered 
*/
    require MonomialOrder(Ry)[1] eq "grevlex":
	"Second argument must have grevlex ordering";

    rmat := RelationMatrix(M);
    R0 := BaseRing(M);
    cwts := ColumnWeights(M);

    if Rank(R0) eq Rank(Ry) then
	if R0 cmpeq Ry then
	  return M,[];
	else 
	  return quo<F|[F!r : r in RowSequence(ChangeRing(rmat,Ry))]>,[]
	    where F is RModule(Ry,cwts);
	end if;
    end if;

    //force R0 to have degrevlex!
    if MonomialOrder(R0)[1] eq "grevlex" then
	R := R0;
    else
	R := PolynomialRing(BaseRing(R0),Rank(R0),"grevlex");
	rmat := ChangeRing(rmat,R);	
    end if;

    n := Rank(R);
    d := Rank(Ry);
    assert (n ge d) and (d gt 0);

    F := EModule(R,cwts); // has top grevlexw ordering!
    I := sub<F|[F!r: r in RowSequence(rmat)]>;
    G := GroebnerBasis(I);

    Rx := PolynomialRing(BaseRing(R),n-d,"grevlex");
    Fx := EModule(Rx,cwts);
    mpx := map<F -> Fx | x :-> Fx![mp(e) : e in Eltseq(x)]> where
	mp is hom<R->Rx|[Rx.i:i in [1..n-d]] cat [0:i in [1..d]]>;

    //1. find module generators.
    Gx1 := [<g,i> : i in [1..#G] | g ne Fx!0 where g is mpx(LeadingTerm(G[i]))];
    Gx := [g[1] : g in Gx1];
    Gx_inds := [g[2] : g in Gx1];
    delete Gx1;
//printf "#Gx: %o\n",#Gx;
    Itmp := quo<Fx|Gx>; //MarkGroebner(Itmp);
    _,deg := HilbertPolynomial(Itmp);
    delete Itmp;
    mons := {Fx|};
    for i in [1..#cwts] do
	r := deg-1-cwts[i];
	if r lt 0 then continue; end if;
	Gi := [g[i] : g in Gx | g[i] ne 0];
	monsi := &join[Isetset(MonomialsOfDegree(Rx,j)) : j in [0..r]];
	for g in Gi do
	    monsi := {m : m in monsi | not IsDivisibleBy(m,g)};
	end for;
	mons join:= {Fx|Fx!(v1 cat [f] cat v2) : f in monsi} where
	   v1 := [Rx|0:j in [1..i-1]] where v2 is [Rx|0:j in [i+1..#cwts]];
    end for;
    mons := Sort(Setseq(mons));
    // convert M rep [0,..0,mon,0..] (mon in kth pos) to <mon,k>
    mon_idxs := [[k: k in [1..#cwts]|m[k] ne 0][1] : m in mons];
    mons := [<mons[i][j],j> where j is mon_idxs[i] : i in [1..#mons]]; 
    mwts := [cwts[m[2]]+LeadingTotalDegree(m[1]) : m in mons]; 
//printf "mons: %o\n",mons;
    //mons now form a set of generators for our module

    //2. find relations
    N := RModule(Ry,mwts);
    B := Basis(N);
    Gy := [g:g in G|l lt (R.(n-d))^TotalDegree(l) where l is 
	[f[k]:k in [1..#cwts] | f[k] ne 0][1] where f is 
	  Eltseq(LeadingMonomial(g))];
//printf "#Gy: %o\n",#Gy;
    //Gy := process_relations(G,Gx_inds,Gy,cwts,d);
    rels := [N| &+[LeadingCoefficient(t[j])*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,<Monomial(Rx,E[1]),j>)
                 where E is Partition(Exponents(t[j]),[n-d,d])
		  where j is [k: k in [1..#cwts]|t[k] ne 0][1]
		   : t in Terms(g)] : g in Gy];
//printf "#mons: %o\n",#mons;
//    if #rels gt 0 then N := quo<N|rels>; end if;
//printf "rk N: %o\n",Rank(N);

    //3. find the sequence of #mons*#mons matrices that give the
    //   action of x_1,..x_(n-d) on N
    mons1 := [hm(m[1])*(F.(m[2])) : m in mons] where hm is
		hom<Rx->R|[R.i:i in [1..n-d]]>;
    mats := [ Matrix(Ry,[ Eltseq( &+[N|LeadingCoefficient(t[k])*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,<Monomial(Rx,E[1]),k>)
                 where E is Partition(Exponents(t[k]),[n-d,d])
		  where k is [l: l in [1..#cwts]|t[l] ne 0][1]
		   : t in Terms(NormalForm((R.j)*m,I))]) : m in mons1])
			: j in [1..n-d] ]; 

    //4. rels may not give all relations: the total set of relations
    // is given by the closure of multiplication by x_1,..,x_(n-d) on
    // the current rels. Compute this now.
    if #rels gt 0 then
      // first do quick Hilbert series check
      hs1 := HilbertSeries(M);
      N1 := Module(Ry,mwts);
      seq := [N1!Eltseq(r) : r in rels];
      relMy := sub<N1|seq>;
      hs2 := HilbertSeries(quo<N1|relMy>);
      if hs1 ne hs2 then
       rels := seq;
       while hs1 ne hs2 do
        rels_new := [];
	for mat in mats, r in rels do
	  r1 := N1!Eltseq(Vector(Eltseq(r))*mat);
	  if r1 notin relMy then
	    Append(~rels_new,r1);
	  end if;
	end for;
        relMy := sub<N1|rels cat rels_new>;
        rels := GroebnerBasis(relMy);
	hs2 := HilbertSeries(quo<N1|relMy>);
       end while;
       rels := [N!Eltseq(r) : r in rels];
      end if;
    end if;

    //5. mons1 may not be a minimal set of generators. Use MyMinimise to
    // minimise them before quotienting by rels, so as to adjust mats
    if #rels gt 0 then
      rel_mat := Matrix([Eltseq(r) : r in rels]);
      mat1,prj_mp,gens := MyMinimise(rel_mat,true);
      if Ncols(mat1) lt Ncols(rel_mat) then   //mons1 not minimal generators
	N := RModule(Ry,[mwts[i] : i in gens]);
	N := quo<N|[N!r : r in RowSequence(mat1)]>;
	mats := [RowSubmatrix(m*prj_mp,gens) : m in mats];
      else
	N := quo<N|rels>;
      end if;
    end if;

    return N,mats;

end intrinsic;
 

intrinsic ModuleProject(I::RngMPol,Ry::RngMPol : col_wt := 0)
		-> ModMPol,SeqEnum
{}
/* 
   takes module M=(S/I)(-col_wt) over S=k[x_1,..x_n], finite over 
   Ry=k[y_1,..y_d] if y_i is mapped to x_(n-d+i), and returns the 
   corresponding module over k[y_1,..,y_d] as a reduced
   (ie presentational) module.

   as well as returning M, the function also returns a sequence of
   r*r matrices (where M = Ry^r/relations) giving the actions of
   x_1,..,x_(n-d) on M, so that the S-module structure can be recovered 
*/

    R0 := Generic(I);
    require MonomialOrder(Ry)[1] eq "grevlex":
	"Second argument must have grevlex ordering";

    //force R0 to have degrevlex!
    if MonomialOrder(R0)[1] eq "grevlex" then
	R := R0;
    else
	I := ChangeOrder(I,"grevlex");
	R := Generic(I);	
    end if;
    n := Rank(R);
    d := Rank(Ry);
    assert (n ge d) and (d gt 0);

    if n eq d then // I = 0!
        return RModule(Ry,[col_wt]),[]; 
    end if;

    Rx := PolynomialRing(BaseRing(R),n-d,"grevlex");
    //Ry := PolynomialRing(BaseRing(R),d,"grevlex");
    mpx := hom<R->Rx|[Rx.i:i in [1..n-d]] cat [0:i in [1..d]]>;
    G := GroebnerBasis(I);

    //1. find module generators.
    Gx := [g : f in G | g ne 0 where g is mpx(LeadingTerm(f))];
//printf "#Gx: %o\n",#Gx;
    Itmp := ideal<Rx|Gx>; MarkGroebner(Itmp);
    _,deg := HilbertPolynomial(Itmp);
    delete Itmp;
    mons := &join[Isetset(MonomialsOfDegree(Rx,i)) : i in [0..deg]];
    for g in Gx do
	mons := {m : m in mons | not IsDivisibleBy(m,g)};
    end for;
    mons := Sort(Setseq(mons));
//printf "mons: %o\n",mons;
    //mons now form a set of generators for our module

    //2. find relations
    N := RModule(Ry,[LeadingTotalDegree(m)+col_wt : m in mons]);
    B := Basis(N);
    Gy := [g:g in G|l lt (R.(n-d))^TotalDegree(l) where l is
			LeadingMonomial(g)];
//printf "#Gy: %o\n",#Gy;
    rels := [N| &+[LeadingCoefficient(t)*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,Monomial(Rx,E[1]))
                 where E is Partition(Exponents(t),[n-d,d]) :
		   t in Terms(g)] : g in Gy];
    M := (#rels gt 0) select quo<N|rels> else N;

    //3. find the sequence of #mons*#mons matrices that give the
    //   action of x_1,..x_(n-d) on N/rels
    mons1 := [hm(m) : m in mons] where hm is hom<Rx->R|[R.i:i in [1..n-d]]>;
    mats := [ Matrix(Ry,[ Eltseq( &+[M|LeadingCoefficient(t)*Monomial(Ry,E[2])*
		B[i] where i is Index(mons,Monomial(Rx,E[1]))
                 where E is Partition(Exponents(t),[n-d,d]) :
		   t in Terms(NormalForm((R.j)*m,I))]) : m in mons1])
			: j in [1..n-d] ];
 
    //4. rels may not give all relations: the total set of relations
    // is given by the closure of multiplication by x_1,..,x_(n-d) on
    // the current rels. Compute this now.
    if /*false */#rels gt 0 then
      // first do quick Hilbert series check
      hs1 := HilbertSeries(I);
      hs1 *:= (Parent(hs1).1)^col_wt; 
      hs2 := HilbertSeries(M);
      if hs1 ne hs2 then
       N1 := Module(Ry,[LeadingTotalDegree(m)+col_wt : m in mons]);
       rels := [N1!Eltseq(r) : r in rels];
       relMy := sub<N1|rels>;
       while hs1 ne hs2 do
        rels_new := [];
	for mat in mats, r in rels do
	  r1 := N1!Eltseq(Vector(Eltseq(r))*mat);
	  if r1 notin relMy then
	    Append(~rels_new,r1);
	  end if;
	end for;
        relMy := sub<N1|rels cat rels_new>;
        rels := GroebnerBasis(relMy);
	hs2 := HilbertSeries(quo<N1|relMy>);
       end while;
       M := quo<N|[N!Eltseq(r) : r in rels]>;
      end if;
    end if;

    return M,mats;

end intrinsic;
 
intrinsic GenModuleProject(M::ModMPol : do_rk_one := true, norm_data := 0) -> 
		ModMPol,SeqEnum,Map
{}
    R := BaseRing(M);
    I := Annihilator(M);
    if Type(norm_data) eq RngIntElt then
      vars,h,hinv := NoetherNormalisation(I);
    else
      vars := norm_data[1]; h := norm_data[2]; hinv := norm_data[3];
    end if;
    d := #vars; n := Rank(R);
    change_vars := &or[vars[i] ne R.(n-d+i) : i in [1..d]];

    M1 := Presentation(M);
    if change_vars then
	F := RModule(R,ColumnWeights(M1));
	M1 := quo<F|[F![h(e) : e in r] : r in 
		RowSequence(RelationMatrix(M1))]>;	
    end if;
    Ry<[y]> := PolynomialRing(BaseRing(R),d,"grevlex");
    if do_rk_one and (Degree(M1) eq 1) then
	if change_vars then
	  I := ideal<R|[h(b) : b in Basis(I)]>;
	end if;
	Mprj,mats := ModuleProject(I,Ry:col_wt := ColumnWeights(M1)[1]);
    else
	Mprj,mats := ModuleProjectM(M1,Ry);
    end if;

    return Mprj,mats,hinv;

end intrinsic;

intrinsic StoRModule(M::ModMPol,R::RngMPol,xmults::SeqEnum,xmap::Map) -> ModMPol
{}
    S := BaseRing(M);
    n := #xmults;
    assert Rank(R)-Rank(S) eq n;
    hm := hom<S->R|[xmap(R.i) : i in [n+1..Rank(R)]]>;
    F := RModule(R,ColumnWeights(M));
    xms := [Matrix(Nrows(mat),Ncols(mat),[hm(e) :e in Eltseq(mat)]) -
		ScalarMatrix(R,Nrows(mat),xmap(R.i)) where mat is xmults[i] :
		i in [1..n]];
    rels := [F![hm(e) : e in Eltseq(rel)] : rel in Relations(M)] cat
		&cat[[F!r : r in RowSequence(mat)] : mat in xms];
    return quo<F|rels>;

end intrinsic;


function tmpy(yEqns,IEqns,n)
    R := Generic(Universe(yEqns));
    m := Rank(R)-n;
    R1 := PolynomialRing(BaseRing(R),m+n,"grevlex");
    str := ["x" cat IntegerToString(i) : i in [1..n]] cat 
		["y" cat IntegerToString(i) : i in [1..m]];
    AssignNames(~R1,str);
    phi := hom<R->R1|[R1.i: i in [1..m+n]]>;
    I1 := ideal<R1|[phi(f) : f in IEqns] cat [phi(f) : f in yEqns]>;
    B := GroebnerBasis(I1);
    B := [f : f in B | &+[e[i] : i in [n+1..n+m]] eq 1
			where e is Exponents(LeadingTerm(f))];
    return B;
end function;


function MapFromGraph(yEqns,I,n)

    R := Generic(Universe(yEqns));
    m := Rank(R)-n;

    S := Generic(I);
    F := FieldOfFractions(S);
    subs := [F.i : i in [1..n]] cat [F!1 : i in [1..m]];
    hm := hom<R->F | [F.i : i in [1..n]] cat [1 : i in [1..m]]>;
    
    // get equations one at a time: first for y_(m-1)/y_m, then
    // for y_(m-2)/y_m etc - not nice!
    for i := m-1 to 1 by -1 do
	eqns := [e : e in yEqns | Exponents(LeadingTerm(e))[n+i] eq 1];
	y_eqn := eqns[#eqns];
	E,F := Explode(Coefficients(y_eqn,R.(n+i)));
	yi := -Evaluate(E,subs)/Evaluate(F,subs);
	subs[n+i] := yi;
    end for;
    map_eqns := [subs[i] : i in [n+1..n+m]];
    return map_eqns;
 
end function;


intrinsic ImageFromMat(mat::Mtrx,I::RngMPol,X::Sch,d::RngIntElt) -> Sch,MapSchGrph
{}
// L is an invertible module on X <= P^(n-1) generated by global sections.
//  I is the defining ideal of X and
//  the module M_L = sum r>= 0 H^0(L(r)) has presentation matrix mat.
// If d > 0, then it is known that the image is generated by (homogeneous)
//  polys of degree <= d.
//
// Function returns the image of phi_L(X).

    n := Rank(I);
    m := Ncols(mat);

    // map is from P^(n-1) -> P^(m-1) - get it's graph from mat
    PG := PolynomialRing(BaseRing(I),n+m,"grevlex");
    incl_hom := hom<Generic(I) -> PG | [PG.i : i in [1..n]]>;
    I_gr := ideal<PG|[incl_hom(b) : b in Basis(I)] cat
	Eltseq(Matrix([[incl_hom(f) : f in r] : r in RowSequence(mat)])*
		Matrix(PG,m,1,[PG.(n+i): i in [1..m]])) >;

    // now get image of adjoint map by projecting to last m variables
    // by elimination
    P_gr := Generic(I_gr);
    // must saturate the ideal before projection. In this case
    // (the graph is an irreducible scheme), this only needs to be
    // done with one of the coordinate variables to be eliminated
vprint SchImage : "Saturating..";
    i := 1; R := CoordinateRing(Ambient(X));
    while i le Rank(R) do
	if not IsInRadical(R.i,Ideal(X)) then break; end if;
	i +:= 1;
    end while;
    assert i le Rank(R);
    I_gr_sat := ColonIdeal(I_gr,P_gr.i);
vprint SchImage : "   Done";
//return I_gr_sat;

vprint SchImage : "Eliminating..";
    if d gt 0 then
        GB := GroebnerBasis(Basis(I_gr_sat),d);
    else
        GB := GroebnerBasis(I_gr_sat);
    end if;
    B_im := [f : f in GB | &and[e[i] eq 0 : i in [1..n]] 
			where e is Exponents(LeadingTerm(f))];
    if d gt 0 then 
        B_im := [f : f in B_im | LeadingTotalDegree(f) le d];
    end if;
vprint SchImage : "   Done";
    Py<[y]> := PolynomialRing(BaseRing(I),m,"grevlex");
    Iy := ideal<Py|[hm(b) : b in B_im]> where
	hm is hom<P_gr->Py|[0: i in [1..n]] cat [Py.i : i in [1..m]]>;
    //Iy is the ideal of the image

/*
    // get the "equations" part
    B_eqns := [f : f in GB | &+[e[i] : i in [n+1..n+m]] eq 1
			where e is Exponents(LeadingTerm(f))];
    //and ideal gens with the graph ordering
    I_eqns := [f : f in GB | &and[e[i] eq 0 : i in [n+1..n+m]] 
			where e is Exponents(LeadingTerm(f))];
    map_eqns := MapFromGraph(B_eqns,I,n);//tmpy(B_eqns,I_eqns,n);
*/

    Prjy := Proj(Py);
    // test for special type of image
    d_im := Dimension(Iy);
    By := MinimalBasis(Iy);
    if d_im eq 2 then
      Xy := Curve(Prjy,By);
    elif (d_im eq 3) and ISA(Type(X),Srfc) then
      Xy := Surface(Prjy,By : Check :=false);
    else
      Xy := Scheme(Prjy,By); // image in P^m
    end if;
    gr_map := SchemeGraphMap(X,Prjy,I_gr_sat : Saturated := true);
    InternalMapSchGrphImageSet(gr_map,Xy);
    return gr_map,Xy,I_gr_sat;//map_eqns,B_eqns;

end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Temporary Hilbert Function/Polynomial functions for graded modules.

function MyHilbertSeries(M)
// computes the Hilbert series of graded module M (must be a 
// quotient module)

    //assert Type(M) eq ModMPolGrd;
    R := BaseRing(M);
    n := Ncols(M);
    if n eq 0 then return RationalFunctionField(Integers())!0; end if;
    rels := GroebnerBasis(sub<Universe(R) | R>) where 
		R is Relations(M);
    wts := ColumnWeights(M);
    
    lead_rels := [LeadingTerm(r) : r in rels];
    Iseq := [[]: i in [1..n]];
    for lr in lead_rels do
	j := 1;
	while (lr[j] eq R!0) and (j le n) do j +:= 1; end while;
	if j le n then Append(~(Iseq[j]),lr[j]); end if;
    end for;
    Is := [ideal<R|seq> : seq in Iseq];
    for I in Is do MarkGroebner(I); end for;

    // get hilb series for each ideal
    HSs := [HilbertSeries(I) : I in Is];
    // shift by col weights
    t := Parent(HSs[1]).1;
    HSs := [(t^wts[i])*HSs[i] : i in [1..n]];

    return &+HSs;

end function;

function MyHilbertPolynomial(M)
// computes the Hilbert polynomial of graded module M (must be a 
// quotient module) and minimal k s.t. H(d) agrees with the Hilbert
// function of I at d for d >= k.

    HS := MyHilbertSeries(M);
    den := Denominator(HS);
    num := Numerator(HS);
    if IsZero(num) then return num,0; end if;

    // deal with possible t in the denominator
    t := Parent(den).1;
    d := Min([i : i in [1..#cs] | cs[i] ne 0])-1 where
		cs is Coefficients(den);
    if d gt 0 then
	den div:= t^d;
    end if;

    k := Max(0,Degree(num)-Degree(den)+1)-d;
    dd := Degree(den);
    num := (num mod den);
    num1 := Evaluate(num,t+1);
    assert Evaluate(den,t+1) eq t^dd;
    cs := Coefficients(num1);
    cs cat:= [0 : i in [1..dd-#cs]];
    
    // HilbPoly(x) is sum_i (-1)^(dd+1-i)*cs[i]*Binomial(x+d+dd-i,dd-i)
    R := PolynomialRing(Rationals());
    x := (R.1)+d; HP := R!(cs[1]);
    for i in [1..dd-1] do
	HP := HP*((x+(dd-i))/(dd-i)) + R!(((-1)^i)*cs[i+1]);
    end for;

    return ((-1)^dd)*HP,k;
    //return HilbertPolynomial(M);

end function;

/////////////////////////////////////////////////////////////////////

function MyHomology(f,g,wts,wts1)
// Temporary script function to compute homology module at a position
// in a graded free complex.
// Arguments are maps f and g s.t. homology = ker(f)/im(g),
// wts = column weights of domain(f) = codomain(g),
// wts1 = column weights of codomain(f)

    ker_mat := Matrix(f);
    im_mat := Matrix(g);

    // first get ker(f) as a submodule
    R := BaseRing(ker_mat);
    f_im := sub< Module(R,wts1) | RowSequence(ker_mat)>;
    B := Basis(SyzygyModule(f_im));
    ker := sub< F | [F!b : b in B]> where F := Module(R,wts);
    // now get (non-minimal) presentation of ker
    kerp,Melts,Belts := GetPresentation(ker);
    B := GroebnerBasis(ker);
    //compute the image of g in kerp
    g_rels := [&+[e[i]*Melts[i] : i in [1..#Melts]] where e is
	Coordinates(ker,ker!r) : r in RowSequence(im_mat)];
    quoty := quo<kerp|g_rels>;
    return quoty;
    
end function;

function MyEcheloniseSolve(M,N)
// used by MySolutions below
    R := BaseRing(M); K := BaseRing(R);
    nr := Nrows(M);
    assert nr ge N;
    c1 := Ncols(M)-N+1;
    M1 := ColumnSubmatrix(M,c1-1);
    M2 := ColumnSubmatrixRange(M,c1,Ncols(M));
    newrows := [];
    for j in [1..N] do
        // find first row of M2 from jth s.t. the jth column
	// entry is a nonzero constant
	i := j;
	while (i le nr) and LeadingTotalDegree(M2[i,j]) ne 0 do 
	  i +:= 1;
	end while;
	assert i le nr;
        c := -1/(K!M2[i,j]);
	if i ne j then SwapRows(~M1,j,i); SwapRows(~M2,j,i); end if;
	MultiplyRow(~M2,c,j); MultiplyRow(~M1,c,j);
	for k in [1..nr] do
	    if k eq j then continue; end if;
	    if M2[k,j] ne 0 then
		AddRow(~M1,M2[k,j],j,k);
		AddRow(~M2,M2[k,j],j,k);
	    end if;
	end for;
    end for;
    return RowSubmatrix(M1,N);

end function;

function MySolutions(M,N,wts)
// expresses each of the last N rows of matrix M as a linear combination
// (coordinates) of the other first Nrows(M)-N rows and returns this
// array of coordinates in a matrix (as the rows)

//printf "wts:\n%o\n",Matrix([[LeadingTotalDegree(f): f in r]: r in RowSequence(M)]);
//printf "M:\n%o\n",M;
    R := BaseRing(M);
    nr1 := Nrows(M)-N;
    F := Module(R,wts);
    S := sub<F|RowSequence(M)>;
    syz := SyzygyModule(S);
    B := Basis(syz); //assuming this is a Groebner basis for some ordering!
    Bmat := Matrix(R,[Eltseq(b) : b in B]);
//error "bad";
//printf "Bmat:\n%o\n",Bmat;
    return MyEcheloniseSolve(Bmat,N);
    /*pick out syzygies with last N entries constant (but not all zero)
    M1 := Matrix([e : b in B | Max([LeadingTotalDegree(e[i+nr1]) : i in [1..N]]) eq 0 
		where e is Eltseq (b)]);
    // solve for k-linear comb of rows = (***,-1,0,0,..0), (***,0,-1,0,..0) etc.
    assert Nrows(M1) ge N;
    M2 := ChangeRing(Submatrix(M1,1,nr1+1,Nrows(M1),N),BaseRing(R));
    solns := Solution(M2,Rows(ScalarMatrix(N,BaseRing(R)!(-1))));
    solns := ChangeRing(Matrix(solns),R)*Submatrix(M1,1,1,Nrows(M1),nr1);
    return solns;*/

end function;

intrinsic MyGradedMap(M::Rec,N::Rec,mat::Mtrx,deg::RngIntElt) -> Rec
{ convenience function}
  return rec<GradModMap |
	  domain := M, codomain := N,
	  map := Homomorphism(M`M,N`M,mat : Check := false),
	  degree := deg>; 
end intrinsic;

intrinsic GradedDualComplex(cplx::Rec, twist::RngIntElt) -> Rec
{ Returns the dual complex of a graded module complex adding a weight twist }

    if #(cplx`terms) eq 0 then return cplx; end if;
    P := BaseRing(((cplx`terms)[1])`M);
    dual := rec<GradModCpx|low_index := cplx`low_index>;
    dual`terms := [GradedFreeModule(P,[twist-w : w in t`wts]) : t in
		Reverse(cplx`terms)];
    n := #dual`terms;
    dual`maps := [Homomorphism(((dual`terms)[i])`M,((dual`terms)[i+1])`M,
	Transpose(Matrix((cplx`maps)[n-i]))) : i in [1..#cplx`maps]];
    return dual;

end intrinsic;

intrinsic GradedDual(M::Rec, I::RngMPol) -> Rec, Map
{ Computes the graded dual Hom(M,can_R/I) where I is the annihilator of
  equidimensional module M over polynomial ring R }

    r := Rank(I)-Dimension(I); // codimension of I = height(I)
    P := Generic(I);

    // 1) compute can_R/I as Ext^r(R/I,R)
    if assigned I`quotient_module then
	M1 := I`quotient_module;
    else
	M1 := GradedModule(QuotientModule(I));
	I`quotient_module := M1;
    end if;
    if assigned (M1`M)`canonical_module then
	can_R_I := (M1`M)`canonical_module;
    elif IsZero(I) then
        can_R_I := GradedFreeModule(P,[Rank(P)]);
        (M1`M)`canonical_module := can_R_I;
    else
      res_I := GradedMinimalFreeResolution(M1);
      cores_I := GradedDualComplex(res_I,Rank(I));
      // length of res/cores is >= r+1 with equality iff R/I
      // is arithmetically Cohen-Macaulay (ie CM at the max homog. ideal)
      if #(res_I`maps) eq r then
	can_R_I := GradedModule(quo<RModule(P,(cores_I`terms)[r+1]`wts) |
		RowSequence(Matrix((cores_I`maps)[r]))>);
      else
        md := MyHomology((cores_I`maps)[r+1],
          (cores_I`maps)[r],(cores_I`terms)[r+1]`wts,(cores_I`terms)[r+2]`wts);
	can_R_I := GradedModule(md);//MyHomology((cores_I`maps)[r+1],
	  //(cores_I`maps)[r],(cores_I`terms)[r+1]`wts,(cores_I`terms)[r+2]`wts));
      end if;
      (M1`M)`canonical_module := can_R_I;
    end if;

    // 2) return Hom(M,can_R/I)
    dual, dual_map := GradedHoms(M,can_R_I);
    return dual,dual_map;

end intrinsic;

intrinsic GradedDualWithHoms(M::Rec, I::RngMPol, hms::SeqEnum) -> Rec, Map, SeqEnum
{ Computes the graded dual M*=Hom(M,can_R/I) where I is the annihilator of
  equidimensional module M over polynomial ring R. The map returned takes
  elements of M* to the correponding module homomorphism. hms is a sequence of
  endomorphisms f:M->M and the function also computes and returns the sequence
  of corresponding dual endomorphisms f*:M*->M*.}

    Md,dmp := GradedDual(M,I);

    gens_d := [(Md`M).i : i in [1..Degree(Md`M)]]; // gens of M*
    gens_d_im := [dmp(g) : g in gens_d]; // corresponding maps

    Mmats := [[Mmp*Matrix(mp`map): mp in gens_d_im] where 
	Mmp is Matrix(f`map) : f in hms];
    //Mmats contains sequences of matrixs for maps M -> Can_R_I
    // which are the images of generators of M* under f*, f in hms

    Mdmp_mat := Matrix([Eltseq(Matrix(g`map)) : g in gens_d_im]);
    hms_seq := [];
    if M`type eq 0 then // M is free
	boo,r := IsDivisibleBy(Degree(Md`M),#(M`wts));
	assert boo;
	if r eq 1 then
	    hms_seq := [ rec<GradModMap | domain := Md, codomain := Md,
	  map := Homomorphism(Md`M,Md`M,Transpose(Matrix(hm`map)) : Check := false),
	  degree := hm`degree> : hm in hms];
	else
	    idmat := IdentityMatrix(BaseRing(Md`M),r);
	    hms_seq := [ rec<GradModMap | domain := Md, codomain := Md,
	  map := Homomorphism(Md`M,Md`M,
	   TensorProduct(Transpose(Matrix(hm`map)),idmat) : Check := false),
	  degree := hm`degree> : hm in hms];
	end if;
    else
      for i in [1..#hms] do
	big_mat := VerticalJoin(Mdmp_mat,
	  Matrix([Eltseq(m) : m in Mmats[i]]));
//print "Computing solutions...";
        coords := MySolutions(big_mat,#Mmats[i],
	[wtc-wt : wtc in (gens_d_im[1])`codomain`wts, wt in M`wts]);
        Append(~hms_seq,rec<GradModMap |
	  domain := Md, codomain := Md,
	  map := Homomorphism(Md`M,Md`M,coords : Check := false),
	  degree := (hms[i])`degree>);
      end for;
    end if;

    return Md,dmp,hms_seq;

end intrinsic;

intrinsic DoubleDual(M::Rec, I::RngMPol, retMap::BoolElt) -> Rec, Map
{ Computes the graded double dual M** = Hom(Hom(M,can_R/I), R/I)
  where I is the annihilator of equidimensional module M over
  polynomial ring R. This gives the "saturation" of M. If retMap is true
  then the natural map M->M** is also computed and returned.}

    dual, dm := GradedDual(M,I);

    assert assigned I`quotient_module and 
	assigned ((I`quotient_module)`M)`canonical_module;

    dd, dm2 := GradedDual(dual,I);

    // compute the M -> M** map
    if retMap then 
      gens_d := [(dual`M).i : i in [1..Degree(dual`M)]]; // gens of M*
      gens_d_im := [dm(g) : g in gens_d];
      if M`type le 1 then
	M1 := M`M;
      else
	M1 := M`pres;
      end if;
      Mmats := [Matrix([Matrix(mp`map)[i] : mp in gens_d_im]) : 
		i in [1..Degree(M1)]];
      // Mmats[i] is the matrix giving the homomorphism M* -> can_R_I
      //  corresponding to the ith generator of (the presentation of) M.
      // Now must pull these back to elements of M** by dm2. THIS IS
      // PROBABLY QUITE A COSTLY OPERATION IN GENERAL!
      gens_dd_im := [Matrix((dm2((dd`M).i))`map) : i in [1..Degree(dd`M)]];
      big_mat := Matrix([Eltseq(g) : g in gens_dd_im] cat
		[Eltseq(m) : m in Mmats]);
//print "Computing solutions...";
      
      coords := MySolutions(big_mat,#Mmats,
	[wtc-wtd : wtc in can_mod`wts, wtd in dual`wts]) where
		can_mod is ((I`quotient_module)`M)`canonical_module;
      mp := rec<GradModMap |
	  domain := M, codomain := dd,
	  map := Homomorphism(M1,dd`M,coords : Check := false),
	  degree := 0>;
      return dd,mp;
    else
      return dd;
    end if;

end intrinsic;

//////////////////////////////////////////////////////////////////

intrinsic ModuleSaturation(M::ModMPol) -> ModMPol
{}
// M is a graded module over R=k[x1,..xn]. Computes the maximal module
// M1 with no maximal associated prime that represents the same sheaf.

// ASSUMING M/M[max^infty] IS EQUIDIMENSIONAL HERE!

    require IsHomogeneous(M): "M must be a homogeneous module";
    d := Degree(HilbertPolynomial(M))+1; // dim(M)
    R := BaseRing(M);
    n := Rank(R);

    // check to see if depth(M) >= 2 [=> M = M1 already]
    res := MinimalFreeResolution(M);
    dep := n+3-#Terms(res);  //p.d. = #Terms(res)-3;
    if dep ge 2 then
	return M;
    end if;
    
    // express as module over Noether normalisation
    Mprj,mats_x,hinv := GenModuleProject(M);
    Ry := BaseRing(Mprj);

    // silly graded module "type" conversion
    GMprj := GradedModule(Mprj);
    hms := [ MyGradedMap(GMprj,GMprj,mat,1) : mat in mats_x];

    // do double dual over Ry M1 = Hom(Hom(Mprj,Ry),Ry) as Ry module.
    //  also compute the multiplications by x [from mats_x] to recover
    //  R module at the end.
    try
      DM,_,hmsd := GradedDualWithHoms(GMprj, ideal<Ry|>, hms);
      DDM,_,hmsdd := GradedDualWithHoms(DM, ideal<Ry|>, hmsd);
    catch e
      error "Error computing the maximal module of a sheaf.\n",
	"All sheaf arguments should have equidimensional",
        "support of dimension > 0 and no embedded associated places.";
    end try;

    // recover M1 as an R module from (Ry module) DDM
    M1 := StoRModule(DDM`M,R,[Matrix(hm`map) : hm in hmsdd],hinv);
    
    return M1;

end intrinsic;

intrinsic CanonicalModule(I::RngMPol : Saturate := false) -> ModMPol, BoolElt
{ I is a homogeneous ideal (for the usual grading) of k[x0,..,xn]. Returns
a module KX giving the canonical sheaf on X, the scheme in P^n defined by I.
NB: It is assumed that X is an equidimensional CM scheme. If Saturate is true,
then the module returned is always the maximal module giving KX. The second
return value gives whether KX is definitely saturated in any case.}

    R := Generic(I);
    require IsHomogeneous(I) : "I must be a homogenous ideal";

    d := Dimension(I);
    n := Rank(R);
    OX := GradedModule(I);
    res := MinimalFreeResolution(OX);
    dep := n+3-#Terms(res);  //p.d. = #Terms(res)-3;
    if dep eq 0 then //I not saturated
	I := Saturation(I);
	res := MinimalFreeResolution(GradedModule(I));
	dep := n+3-#Terms(res);  //p.d. = #Terms(res)-3;
    end if;
    assert dep gt 0;

    if dep eq d then  // nice case! X is arithmetically CM
	c_wts := [n- wt : wt in ColumnWeights(Term(res,n-d))];
	F := RModule(R,c_wts);
	return quo<F|[F!r : r in RowSequence(Transpose(Matrix(
		BoundaryMap(res,n-d))))]>, true;
    end if;
	
    KX := Ext(n-d,OX,RModule(R,[n]));
    if Saturate then
	KX := ModuleSaturation(KX);
	return KX,true;
    else
	return KX,false;
    end if;

end intrinsic;
