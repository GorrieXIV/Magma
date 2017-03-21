freeze;

/********************************************************************

    Some (incomplete) structures and intrinsics to simulate a
                      graded module type.

    First version:
	- no element structures
	- (so) no sub or quo
	- no attempt to store or use "forward resolutions"
	  (M has a forward resolution if there is an exact
	   sequence of graded modules with Fi free and n >= 1:
	   0 -> M -> F0 -> F1 .. -> Fn )
     Included:
      Basic creation intrinsics for free graded mods and to
      make a ModMPol into a graded module:
	GradedFreeModule
	GradedModule
      MinimalFreeResolution:
	GradedMinimalFreeResolution
	GradedBettiTable
      Twisting intrinsic - Twist
      Homomorphism module creation and kernel,image,cokernel of homogeneous
      maps:
	GradedHoms
	GradedKernel
	GradedImage
	GradedCokernel

    Problems:  - can't change fields in a record argument in intrinsics.
               - if F is RModule(P,wts), a free (reduced) module with
		 some non-trivial column weights, the weights are lost
                 in quo<F|[some elts]>. Didn't think this happened
		 and have assumed that it doesn't in several places!

    BASICALLY HARDLY USED NOW, BUT STILL LINKED TO dual2.m

***********************************************************************/

//////////////// BASIC STRUCURES AS RECORDS ////////////////////////////

/* not including the zero terms at either end here for simplicity */
GradModCpx := recformat<
   low_index	: RngIntElt, // index of right-hand element
   terms	: SeqEnum,   // the terms of the complex - (free) HomogMods
   maps		: SeqEnum    // the connecting maps (repd as just ModMPolHoms)
>;

// A map to/from an embedded module is represented by a map
// to/from its reduced presentation here - the actual domain and
// codomain are stored in the structure.
// Maps must be homogeneous of given degree d, which means that
// if map f: M->N and m is any homogeneous element of degree d1, say,
// then f(m) will be homogeneous of degree d+d1 in N. This is equivalent
// to this being true for all generators of M. Any module map from
// M -> N can be uniquely written as a sum of homogeneous maps of
// various degrees from M to N
GradModMap := recformat<
   domain	: Rec,	      // the domain of the map
   codomain	: Rec,        // the codomain of the map
   map		: ModMPolHom, // actual module map (between reduced modules!)
   degree	: RngIntElt   // degree of map
>;

GradMod := recformat<
   M	  	: ModMPol,
   type		: RngIntElt,// 0 = free (reduced) 1 = reduced, 2 = embedded
   wts  	: SeqEnum,  // col weights of M
//  extra data for presentation of embedded modules only
   pres		: ModMPol,  // presentation of M when an embedded module
   PElts	: SeqEnum,  // elts of pres <-> Groebner basis of M
   MElts	: SeqEnum,  // elts of Groebner basis of M <-> generators of pres
// end extra data
   pol_res	: Rec,      // minimal free resolution of M
   pol_res_map  : Rec       // connecting homorphism from pol_res to M
/*
   forward_res  : Rec,      // a free res (0 -> M -> ) F0 -> F1 -> ... if known
   forward_res_map: Rec     // connecting homorphism from M to forward_res
*/
>;

///////////////// Auxiliary Functions /////////////////////////////////

function BettiResolveCols(M,vs)
// M an m*n matrix of homogeneous polynomials representing
// a (degree 0) homogeneous map from R^m to R^n.
// vs is a sequence of length n giving column weights on R^n.
// Returns the column weights on R^m.
    nr := Nrows(M); nc := Ncols(M);
    assert #vs eq nc;

    if nr eq 0 then return []; end if;
    us := [Integers()|];
    for j in [1..nr] do Undefine(~us,j); end for;

    for i in [1..nr], j in [1..nc] do
	deg := LeadingTotalDegree(M[i,j]);
	if deg ne -1 then
	    if IsDefined(us,i) then
		error if deg ne (us[i]-vs[j]), "Input vs are invalid";
	    else
		us[i] := vs[j]+deg;
	    end if;
	end if;
    end for;

    if not ((#us eq nr) and IsComplete(us)) then
				//some zero rows - fill in with some small weight
	val := (#us eq 0) select 0 else Min(Seqset(us))-1;
        for i in [1..nr] do
	    if not IsDefined(us,i) then us[i] := val; end if;
	end for;
    end if;
    return us;

end function;

function BettiRes(res)
// Returns a matrix giving the betti numbers for a free resolution res &
// the column weight corresponding to the top-left entry.
//  The form is as follows (note a free res is assumed to start and
//    end with the zero module), for, eg, the resolution
//  0 <- S(1)+2S(2) <- 3S(2)+4S(4) <- 5S(5) <- 0
//    return is [ 1, 3, 0 ]
//		[ 2, 0, 0 ]
//		[ 0, 4, 5 ]
//  and for the (non- minimal) resolution
//  0 <- S(2) <- S(2)+2S(3) <- S(3)+S(4) <- 0
//    return is [ 0, 1, 1 ]
//		[ 1, 2, 1 ]
//   ie the top line <-> S(j-a) multiplicity in the jth place where
//  a is max_j{j-r|S(r) occurs in the jth place}
//
    // first get all weights and shift
    Z := Integers();
    len := #(res`terms);
    all_wgts := [t`wts : t in res`terms];
    Reverse(~all_wgts);
    all_wgts := [[w-i: w in all_wgts[i+1]] : i in [0..len-1]];

    // build betti table
    min,max := Explode([Min(seq),Max(seq)]) where seq is &cat all_wgts;
    mat := ZeroMatrix(Z,max-min+1,len);
    for i in [1..len], j in all_wgts[i] do
	mat[j-min+1,i] +:= 1;
    end for;
    return mat,min;
end function;

function MyIsHomogeneous(f,wts)
// f is an element in a graded free module with column weights wts.
// Return whether f is homogeneous and, if so, it's grading
    fseq := Eltseq(f);
    inds := [i : i in [1..#fseq] | fseq[i] ne 0];
    if #inds eq 0 then return true,0; end if;
    d := LeadingTotalDegree(fseq[i])+wts[i] where i is inds[1];
    boo := &and[ (IsHomogeneous(e) and 
	(LeadingTotalDegree(e)+wts[j] eq d))
	  where e is fseq[j] : j in inds ];
    return boo,d;
end function;

function RecoverBasisIndices(mat)
// mat is a matrix giving a map from a free module F onto a reduced module
// M where some subset {F.i1,..F.ir} map onto the basis elements M.1,..M.r
// Function returns the indices i1,..ir [very crudely!]
    n := Nrows(mat); r := Ncols(mat);
    P := BaseRing(mat);
    filt := [ [i,p[1]]  : i in [1..n] | #p eq 1
	where p is [j : j in [1..r] | mat[i,j] ne 0] ];
    filt := [f : f in filt | mat[f[1],f[2]] eq P!1];
    assert #filt ge r;
    filt2 := [f[2] : f in filt];
    inds := [filt[Index(filt2,i)][1] : i in [1..r]];
    return inds;   
end function;

function GetPresentation(S)
// gets presentation of embedded module S - internal function doesn't
// seem to be working
    B := GroebnerBasis(S);
    P := BaseRing(S);
    syz := SyzygyModule(S);
    F := RModule(P,ColumnWeights(syz));
    // get minimal presentation
    M :=  quo<F|[F!b : b in Basis(syz)]>;
    // NB - assuming here that the M will have a homogeneous presentation!
    // recover data to convert between B and M
    hm := Morphism(F,M);
    Melts := [hm(F.i) : i in [1..Degree(F)]]; //images of B in M
    Belts := [B[i] : i in RecoverBasisIndices(Matrix(hm))];
    return M,Melts,Belts;
end function;

////////// Functions to compute Hom(M,N) as graded module /////////////

function InvImage(M,N,wts1,boo)

   /*
       M, N are r x t and s x t matrices over ring R representing
       (degree 0 homogeneous) linear maps
	l_M : R^r[wts1] -> R^t[wts3] and l_N : R^s[wts2] -> R^t[wts3].
       Function computes l_M^(-1)(Image(l_N)) as a homogeneous submodule of
       R^r[wts1], returning the result as a k x r matrix whose rows
       generate this submodule (not necessarily giving a minimal basis!).
       If boo is true, use a minimal basis for the submodule.

       r,s or t may be 0
   */

   r := NumberOfRows(M);
   t := NumberOfColumns(M);
   s := NumberOfRows(N);
   assert t eq NumberOfColumns(N);
   R := BaseRing(M);
   assert R eq BaseRing(N);
   // handle special cases 
   if r eq 0 then
      return Matrix(0,0,[R|]);
   end if;
   if t eq 0 then
      return ScalarMatrix(r,R!1);
   end if;
   // general case  - compute syzgies for rows of M and N
   syz_mat := VerticalJoin(M,N);
   S := sub<Module(R,t)|RowSequence(syz_mat)>;
   B := Basis(SyzygyModule(S));
   if #B eq 0 then return Matrix(R,0,r,[]); end if;
   // and finally, project back to R^r
   if s gt 0 then
       B := [Partition(Eltseq(b),[r,s])[1] : b in B];
   end if;
   // minimise generators
   if boo then
    S := sub<Module(R,wts1)|B>;
    B := MinimalBasis(S);
   end if;
   return Matrix([Eltseq(b) : b in B]);
   
end function;

function contraHom(M,n)

    /*
      M is an r x s matrix over R representing phi_M: R^r -> R^s.
      Funstion returns matrix M*, an s*n x r*n matrix representing
          phi_M^* : Hom(R^s,R^n) -> Hom(R^r,R^n)
      where Hom(R^a,R^b) = R^(a*b) in the natural row-major way.
    */
    R := BaseRing(M);
    r := NumberOfRows(M);
    s := NumberOfColumns(M);
    if (r eq 0) or (s eq 0) or (n eq 0) then
        return Matrix(s*n,r*n,[R|]);
    else
        return
          Matrix(R,[Eltseq(M*b) where b is 
                     Matrix(SparseMatrix(s,n,[<i,j,R!1>]))
		     : j in [1..n], i in [1..s]]);
    end if;

end function;

function coHom(M,n)

    /*
      M is an r x s matrix over R representing phi_M: R^r -> R^s.
      Function returns matrix M*, an r*n x s*n matrix representing
          phi_M_* : Hom(R^n,R^r) -> Hom(R^n,R^s)
      where Hom(R^a,R^b) = R^(a*b) in the natural row-major way.
    */
    R := BaseRing(M);
    r := NumberOfRows(M);
    s := NumberOfColumns(M);
    if (r eq 0) or (s eq 0) or (n eq 0) then
        return Matrix(r*n,s*n,[R|]);
    else
        return
          Matrix(R,[Eltseq(b*M) where b is 
                     Matrix(SparseMatrix(n,r,[<i,j,R!1>]))
		     : j in [1..r], i in [1..n]]);
    end if;

end function;

function RHoms(M,N,wtsM,wtsN)

   /*
       M, N are m x n and r x s matrices over ring R representing
       linear maps l_M : R^m -> R^n and l_N : R^r -> R^s.
       modM and modN are the module cokernels of l_M and l_N.
       When R^n is given column weights wtsM and R^s is given
       column weights wtsN, l_M and l_N are homogeneous, so
       modM and modN are GRADED modules w.r.t. these weightings.
       Function computes a presentation of Hom_R(modM,modN)
       AS A GRADED MODULE, thought of as a subquotient of
	Hom(R^n[wtsM],R^s[wtsN]) = R^(n*s)[wtsN-wtsM] (see below)

       R is assumed to be an polynomial ring over a field! m,n,r or s may be 0
   */

   // first note  R^m and R^r have natural column weights wtsM1 and wtsN1
   // s.t. the linear maps l_M and l_N are degree 0 homogeneous maps
   // between graded modules. wtsM1 and wtsN1 can be computed as
   //   wtsM1 := BettiResolveCols(M,wtsM);
   //   wtsN1 := BettiResolveCols(N,wtsN);
   // though we don't need to get these values for the comps below

   // get matrix representing
   //  l_M^*s : Hom(R^n[wtsM],R^s[wtsN]) -> Hom(R^m[wtsM1],R^s[wtsN])
   M1 := contraHom(M,NumberOfColumns(N));
   // get matrix representing
   //  l_N_*m : Hom(R^m[wtsM1],R^r[wtsN1]) -> Hom(R^m[wtsM1],R^s[wtsN])
   N1 := coHom(N,NumberOfRows(M));
   // get matrix representing
   //  l_N_*n : Hom(R^n[wtsM],R^r[wtsN1]) -> Hom(R^n[wtsM],R^s[wtsN])
   N2 := coHom(N,NumberOfColumns(M));
   
   // NB. Hom(R^a[wts1],R^b[wts2]) = R^(a*b)[wts] with the natural row-major
   // identification (ie, a*b matrix M -> Eltseq(M)) has wts given by
   // wts = [ wts2[1]-wts1[1],wts2[2]-wts1[1],..wts2[b]-wts1[1],
   //    wts2[1]-wts1[2],wts2[2]-wts1[2],..,wts2[b]-wts1[a] ]
   //  which we write as wts2-wts1
   // Our matrices M1,N1,N2 here correctly give degree 0 maps between
   // the relevant graded Hom modules with the above weighting method.

   // compute result = (l_M^*)^(-1) (Im l_N_*m) / Im l_N_*n
   //  - the weights of the domain of M1 are wtsN-wtsM
   wts1 := [wN-wM : wN in wtsN, wM in wtsM]; 
   //printf "first inv image: %o %o %o\n",Nrows(M1),Nrows(N1),Ncols(M1);
   S1 := InvImage(M1,N1,wts1,true);
   wts2 := BettiResolveCols(S1,wts1);
   //printf "second inv image: %o %o %o\n",Nrows(S1),Nrows(N2),Ncols(S1);
   S2 := InvImage(S1,N2,wts2,false);
   
   // result is R^k/Q 
   // here S1 is a k x (n*s) matrix giving the map of 
   //   R^k[wts2] -> Hom(R^n[wtsM],R^s[wtsN])=R^(n*s)[wts1]
   //  and S2 is a t x k matrix giving generators of Q
   //
   // minimise quotient and get matrix images of generators
   P := BaseRing(M);
   F := RModule(P,wts2);
   if Nrows(S2) eq 0 then
     homM := F;
     inds := [1..#wts2];
   else	
     homM :=  quo<F|RowSequence(S2)>;     
     hm := Morphism(F,homM);
     inds := RecoverBasisIndices(Matrix(hm)); //i s.t. F.i <-> basis elts of homM
   end if;
   mats := [Matrix(Ncols(M),Ncols(N),Eltseq(S1[i])) : i in inds];

   return homM,mats;

end function;

function GetMap(m,mats,M,N)
// checks that an element m in the underlying (reduced) module of graded module
// homMN=Hom(M,N) is homogeneous and, if so, returns the corresponding map
    homs := Parent(m);
    boo,d := MyIsHomogeneous(m,ColumnWeights(homs));
    error if not boo, "Can only create maps from homogeneous elements";
    mat := &+[e[i]*mats[i] where e is Eltseq(m) : i in [1..#mats]];
    M1 := (M`type le 1) select M`M else M`pres;
    N1 := (N`type le 1) select N`M else N`pres;
    return rec<GradModMap | domain := M, codomain := N, 
	map := Homomorphism(M1,N1,mat : Check := false), degree := d >;
end function;

//////////////////////////////////////////////////////////////////////
//                    Creation Intrinsics                           //

intrinsic GradedFreeModule(P::RngMPol, wts::SeqEnum[RngIntElt]) -> Rec
{ Create free module over P with weights wts. }

    M := RModule(P,wts);
    M1 := rec<GradMod | M := M, type := 0, wts := wts>;
    return M1;

end intrinsic;

intrinsic GradedModule(M::ModMPol) -> Rec
{ Creates a graded module from a plain one }

    // first check if M is reduced or embedded
    if M cmpeq Presentation(M) then  // reduced case
	rels := Relations(M);
	type := (#rels eq 0) select 0 else 1;
	wts := ColumnWeights(M);
	if type eq 1 then // check relations are homogeneous for the weighting
	  //first simple check
	  bhom := &and[MyIsHomogeneous(f,wts) : f in rels];
	  if not bhom then //look at Groebner basis
	    S := sub<Module(BaseRing(M),wts)|[Eltseq(r):r in rels]>;
	    rels1 := GroebnerBasis(S);
	    if &or[not MyIsHomogeneous(f,wts) : f in rels1] then
		error "Module is not homogeneous!";
	    end if;
	    //replace relations by rels1 (so they are all homogeneous!)
	    M1 := quo<RModule(BaseRing(M),wts)|[Eltseq(r) : r in rels1]>;
	  else
	    M1 := M;
	  end if;
	else
	  M1 := M;
	end if;
	return 	rec<GradMod | M := M1, type := type, wts := wts>;	
    else //embedded case
	wts := ColumnWeights(M);
	if M eq Generic(M) then // free
	    return GradedFreeModule(BaseRing(M),wts);
	end if;
	B := Basis(S);
	bhom := &and[MyIsHomogeneous(f,wts) : f in rels];
	if not bhom then //look at Groebner basis
	    B := GroebnerBasis(S);
	    if &or[not MyIsHomogeneous(f,wts) : f in B] then
		error "Module is not homogeneous!";
	    end if;
	end if;
	pres,PElts,MElts := GetPresentation(M);
	return 	rec<GradMod | M := M, type := 2, wts := wts, pres := pres,
		PElts := PElts, MElts := MElts>;	
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//     Minimal Free Resolution and Twist                            //

intrinsic GradedMinimalFreeResolution(M::Rec) -> Rec
{ Returns the minimal free resolution of M }

    if assigned M`pol_res then
	return M`pol_res, M`pol_res_map;
    end if;

    if M`type eq 2 then
     //  Call min free resolution for the presentation.
     //  Internal function doesn't seem to work currently for embedded mods.
	M1 := M`pres;
    else
	M1 := M`M;
    end if;

    res, mp := MinimalFreeResolution(M1);
    cpx := rec<GradModCpx | low_index := 0 >;
    wts := ColumnWeights(M1);
    trms := []; mps := [];
    raw_terms := Terms(res);
    raw_maps := BoundaryMaps(res);
    P := BaseRing(raw_terms[1]);
    
    for r := #raw_maps-1 to 2 by -1 do
	assert #wts eq Degree(raw_terms[r+1]);
	Append(~trms, GradedFreeModule(P,wts));
	Append(~mps,raw_maps[r]);
	wts := BettiResolveCols(Matrix(raw_maps[r]),wts);
    end for;
    Append(~trms, GradedFreeModule(P,wts));
    Reverse(~trms); Reverse(~mps);

    cpx`terms := trms; cpx`maps := mps;
    // FORGOT THAT ASSIGNMENT TO EXTERNAL M DOESN"T WORK HERE
    M`pol_res := cpx;
    M`pol_res_map := rec<GradModMap | domain := cpx`terms[#(cpx`terms)],
	codomain := M, map := mp, degree := 0>;

    return M`pol_res, M`pol_res_map;

end intrinsic;

intrinsic GradedBettiTable(M::Rec) -> ModMatRngElt
{ Returns the Betti table for the graded module M }

    if not assigned M`pol_res then
	pol_res := GradedMinimalFreeResolution(M);
    else
	pol_res := M`pol_res;
    end if;
    return BettiRes(pol_res);

end intrinsic;

intrinsic Twist(M::Rec,d::RngIntElt) -> Rec
{ Twist of M by d, M(d), ie all col wts are shifted down by d}

    P := BaseRing(M`M);
    wts := [w-d: w in M`wts];
    M1 := rec<GradMod | type := M`type, wts := wts>;
    if M`type le 1 then //free or reduced
	N := RModule(P,wts);
	if M`type eq 1 then
	    N := quo<N|RowSequence(RelationMatrix(M`M))>;
	end if;
	M1`M := N;
    else //embedded
	N := sub<Module(P,wts)|[Eltseq(b):b in Basis(M`M)]>;
	M1`M := N;
	M1`MElts := [N!Eltseq(m) : m in M`MElts];
	p1 := quo<RModule(P,ColumnWeights(M`pres))|
		RowSequence(RelationMatrix(M`pres))>;
	M1`PElts := [p1!Eltseq(m) : m in M`PElts];
	M1`pres := p1;
    end if;
    if assigned M`pol_res then
	pr := M`pol_res;
	pr1 := 	rec<GradModCpx | low_index := pr`low_index,
		  terms := [Twist(t,d) : t in pr`terms]>;
	pr1`maps := [Homomorphism((pr1`terms)[i],(pr1`terms)[i+1],
	  Matrix((pr`maps)[i]) : Check := false) : i in [1..#(pr`maps)]];
	M1`pol_res := pr1;
	prm := M`pol_res_map;
	dom := pr1`terms[#(pr1`terms)];
	M1`pol_res_map := rec<GradModMap |
	  domain := dom, codomain := M1,
	  map := Homomorphism(dom`M,(M`type le 1) select M1`M else M1`pres,
		Matrix(prm`map) : Check := false),
	  degree := prm`degree>;
    end if;

    return M1;

end intrinsic;

/////////////////////////////////////////////////////////////////////
//    Computation of (graded) Hom(M,N), kernels, images and        //
//     cokernels. CONVENTION: if f: M-> N is of degree d,          //
//     interpret as a degree 0 map M -> N(d) where N(d) is         //
//     the twist of N by d: all column weights are REDUCED by d.   //

intrinsic GradedHoms(M::Rec,N::Rec) -> Rec,Map
{ computes the graded Hom(M,N) module and a map from this to actual
  graded module maps }

    M1 := (M`type le 1) select M`M else M`pres;
    N1 := (N`type le 1) select N`M else N`pres;

    homMN,mats := RHoms(RelationMatrix(M1),RelationMatrix(N1),
	ColumnWeights(M1),ColumnWeights(N1));
    typ := (#Relations(homMN) eq 0) select 0 else 1;
    GhomMN := rec<GradMod | M := homMN, type := typ, 
		wts := ColumnWeights(homMN)>;

    // Parent(M) eq Power Structure of Rec!
    return GhomMN, map< homMN -> Parent(M) | m :-> GetMap(m,mats,M,N)>;

end intrinsic;

intrinsic GradedIdentityMap(M::Rec) -> Rec
{ returns the identity from M to itself }

    M1 := (M`type le 1) select M`M else M`pres;
    return rec<GradModMap | domain := M, codomain := M,
	map := Homomorphism(M1,M1,IdentityMatrix(BaseRing(M1),Degree(M1)) :
 				Check := false),
	degree := 0>;

end intrinsic;

intrinsic GradedKernel(f::Rec) -> Rec
{ Kernel of a graded module map }

    M := f`domain;
    mp := f`map;
    P := BaseRing(M`M);
    type := M`type;
    case type:
	when 0: // free case
	  // really should check if f=0 here => result=M=free
	  wts := ColumnWeights(M`M);
	  mat := Matrix(mp);
	  mat1 := RelationMatrix(Codomain(mp));
	  ker_mat := InvImage(mat,mat1,wts,false);
	  F1 := Module(P,wts);
	  kerS := sub<F1|RowSequence(ker_mat)>;
 	  pres,PElts,MElts := GetPresentation(kerS);
	  ker := rec<GradMod | M := kerS, type := 2, wts := wts, pres := pres,
		PElts := PElts, MElts := MElts>;
	when 1: // reduced (but not free)
	  ker := Kernel(mp); // may as well just use built-in fn here!
	  ker := rec<GradMod | M := ker, type := 1, wts := ColumnWeights(ker)>;
	when 2: // embedded
	  // get kernel as submodule of original embedded mod?
	  // presentation <-> sub mod groebner basis hassles.
	  // Come back to later!
	  ker := Kernel(mp); // just use built-in fn here!
	  ker := rec<GradMod | M := ker, type := 1, wts := ColumnWeights(ker)>;	
    end case;
    return ker;
	  
end intrinsic;

intrinsic GradedImage(f::Rec) -> Rec
{ Image of a graded module map }

    N := f`codomain;
    mp := f`map;
    d := f`degree;
    P := BaseRing(N`M);
    type := N`type;
    case type:
	when 0: // free case
	  // really should check if f is onto => result=N=free
	  wts := [w-d : w in ColumnWeights(N`M)];
	  mat := Matrix(mp);
	  F1 := Module(P,wts);
	  imS := sub<F1|RowSequence(mat)>;
 	  pres,PElts,MElts := GetPresentation(imS);
	  im := rec<GradMod | M := imS, type := 2, wts := wts, pres := pres,
		PElts := PElts, MElts := MElts>;
	when 1: // reduced (but not free)
	  im := Image(mp); // just use built-in fn here!
	  if d ne 0 then
	    F := RModule(P,[w-d : w in ColumnWeights(im)]);
	    im := quo<F|RowSequence(RelationMatrix(im))>;
	  end if;
	  im := rec<GradMod | M := im, type := 1, wts := ColumnWeights(im)>;
	when 2: // embedded
	  wts := [w-d : w in ColumnWeights(N`M)];
	  mat := Matrix(mp);
	  F1 := Module(P,wts);
	  im := [&+[r[i]*(N`Melts[i]): i in [1..Ncols(mat)]] :
			r in RowSequence(mat)];
	  imS := sub<F1|im>;
 	  pres,PElts,MElts := GetPresentation(imS);
	  im := rec<GradMod | M := imS, type := 2, wts := wts, pres := pres,
		PElts := PElts, MElts := MElts>;
    end case;
    return im;
	  
end intrinsic;

intrinsic GradedCokernel(f::Rec) -> Rec
{ Cokernel of a graded module map }

    N := f`codomain;
    mp := f`map;
    d := f`degree;
    P := BaseRing(N`M);
    // don't differentiate between types here - all results reduced!
    // However, should really check for f = 0 map!
    coker := Cokernel(mp); // just use built-in fn here!
    if d ne 0 then
	F := RModule(P,[w-d : w in ColumnWeights(coker)]);
	coker := quo<F|RowSequence(RelationMatrix(coker))>;
    end if;
    coker := rec<GradMod | M := coker, type := 1, wts := ColumnWeights(coker)>;

    return coker;
	  
end intrinsic;

/////////////////////////////////////////////////////////////////////
//////      SOME OTHER MODULE OPERATIONS                       //////
/////////////////////////////////////////////////////////////////////

intrinsic GradedDirectSum(Ms::SeqEnum) -> Rec, SeqEnum
{ Computes the direct sum of the modules in Ms and returns this
  along with the inclusion maps }

    // handle special cases
    assert #Ms gt 0; // can't handle 0 modules here as there is no way to recover
		     //  the base ring from the SeqEnum!
    if #Ms eq 1 then
	return Ms[1],[GradedIdentityMap(Ms[1])];
    end if;

    // result will be of reduced type
    R := BaseRing(Ms[1]`M);
    wts := &cat[ColumnWeights((M`type le 1) select M`M else M`pres) : M in Ms];
    F := RModule(R,wts);
    rels := [];
    mps := [];
    n := 0; N := #wts;
    for M in Ms do
	M1 := (M`type le 1) select M`M else M`pres;
	r := Degree(M1);
	Append(~mps,HorizontalJoin(ZeroMatrix(R,r,n),HorizontalJoin(
	   IdentityMatrix(R,r),ZeroMatrix(R,r,N-n-r))));
	rM := Relations(M1);
	if #rM gt 0 then
	    v1 := [R!0 : i in [1..n]]; v2 := [R!0 : i in [1..N-n-r]];
	    rels cat:= [v1 cat Eltseq(rel) cat v2 : rel in rM];
	end if;
	n +:= r;
    end for;
    Mres := quo<F|[F!r : r in rels]>; typ := (#rels eq 0) select 0 else 1;
    DS := rec<GradMod | M := Mres, type := typ, wts := wts>;
    mps := [rec<GradModMap | domain := M, codomain := DS,
	map := Homomorphism((M`type le 1) select M`M else M`pres,Mres, mps[i]:
 				Check := false), degree := 0> where M is Ms[i] :
			i in [1..#Ms]];

    return DS,mps;

end intrinsic;
