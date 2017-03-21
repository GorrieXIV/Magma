freeze;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      Creation functions                        //
//                                                                //
////////////////////////////////////////////////////////////////////

// update, 3rd Sept 2002: changed order in which
// generators of SL2(Z) are given, to be compatible
// with functions for computing words for matrices
// in terms of T=[1,1,0,1] and S=[0,-1,1,0],
// as used in the intersection_pairing modular symbols file.

function init_psl2_group(N,R) 
    /* The basic internal creation function. */
    G := New(GrpPSL2);
    // warning!  Need to check for which
    // rings GL(2,R) works or not!!!
    if (Type(R) in {Rng,RngInt,FldRat}) then 
       G`MatrixGroup := GL(2,R);
    else
       G`MatrixGroup := MatrixAlgebra(R,2);
    end if;
    G`BaseRing := R;
    G`Level := N;
    G`conjugate_list := [GL(2,R)!1];
    G`IsNormalizer := false;
    return G;
end function;

function init_psl2_group_char(N,R,char) 
    G := init_psl2_group(N,R);
    G`character_list := [char];
    return G;
end function;
 
intrinsic PSL2(R::Rng) -> GrpPSL2
    {The projective special linear matrix group PSL(2,R).}
    require Type(R) in {RngInt, FldRat, FldQuad, FldNum, FldRe}: 
           "The Argument must have type RngInt, FldRat, FldQuad, or FldRe";
    require not R cmpeq ComplexField(): "The Argument must be contained in the reals";
    if Type(R) eq FldQuad then
	require Discriminant(R) gt 0: "The Argument must be a ring contained in the reals";
    end if;
     
    G := init_psl2_group(1,R);
    G`BaseRing := R;
    G`Level := 1;
    G`gammaType_list:=[[1,1,1]];
    if Type(R) eq RngInt then
       T := G![1,1,0,1];
       S := G![0,1,-1,0];
       G`Generators := [T,S];
    end if;
    G`conjugate_list:=[GL(2,R)!1];
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(A::SeqEnum) -> GrpPSL2
    {Given A = [n,m,p], this returns
    the congruence subgroup consisting of 2 by 2 matrices
    with integer coefficients [a,b,c,d]
    with a = d = 1 mod m,
    b = 0 mod p, and c = 0 mod n}
    require Universe(A) eq Integers() and #A eq 3
            and &and[A[i] ge 1 : i in [1..3]]: 
           "Please provide a list of 3 positive integers";
    n,m,p := Explode(A);
    require ((n*p) mod m) eq 0 :
            "The Argument must be a sequence N of 3 integers "
           * "with N[2] dividing N[1]*N[3]";
    N := Lcm(A);
    G := init_psl2_group(N,IntegerRing());
    G`gammaType_list := [A]; 
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(A::SeqEnum,char::GrpDrchElt) -> GrpPSL2
    {Given N = [n,m,p], this returns
    the congruence subgroup consisting of 2 by 2 matrices
    with integer coefficients [a,b,c,d]
    with  b = 0 mod p, and c = 0 mod n, and char(a) = 1
    for char a Dirichlet character mod m}
    require Type(char) eq GrpDrchElt: "second argument must be a Dirichlet character";
    require A[2] mod Conductor(char) eq 0: 
      "The second argument must be a Dirichlet character with conductor dividing A[2]";    
    A[2] := Conductor(char);
    require char(-1) eq 1 : "Please give a character chi satisfying chi(-1) = 1";
    G := CongruenceSubgroup(A);
    subgroup_list_required := A[2] ne 1;  
    // Also not required if kernel(char) eq {1,-1} :
    if Order(Parent(char)) div Order(char) in {1,2} then 
        subgroup_list_required := false; end if;
    if subgroup_list_required then G`subgroup_list := [char]; end if;
    return G;
end intrinsic;

intrinsic CongruenceSubgroup(k::RngIntElt,N::RngIntElt) -> GrpPSL2
    {The congruence subgroup 
    Gamma_0(N), Gamma_1(N), Gamma(N), Gamma^1(N), or Gamma^0(N),
    when k = 0,1,2,3, or 4  respectively.}
    if k notin {0,1,2,3,4} then
	error "First argument must in {0,1,2,3,4}";
    end if;
    if N lt 1 then
	error "Second argument must be a positive integer";
    end if;
    if N eq 1 then
	return PSL2(Integers());
    end if;
    case k:
	when 0:
	return CongruenceSubgroup([N,1,1]);
	when 1:
	return CongruenceSubgroup([N,N,1]);
	when 2:
	return CongruenceSubgroup([N,N,N]);
	when 3:
	return CongruenceSubgroup([1,N,N]);
	when 4:
	return CongruenceSubgroup([1,1,N]);
    end case;
end intrinsic;

intrinsic CongruenceSubgroup(N::RngIntElt) -> GrpPSL2
   {The full projective congruence subgroup Gamma(N).}
   return CongruenceSubgroup(2,N);
end intrinsic;


//////////////////////////////////////////////////////////
//                                                      //
//  creation of special congruence subgroups            //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Gamma0(N::RngIntElt) -> GrpPSL2
    {creates the congruence subgroup Gamma_0(N)}
    require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([N,1,1]);    
    return G;
end intrinsic;

intrinsic Gamma1(N::RngIntElt) -> GrpPSL2
   {creates the congruence subgroup Gamma_1(N)}
   require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([N,N,1]);    
    return G;
 end intrinsic;


intrinsic GammaUpper0(N::RngIntElt) -> GrpPSL2
    {creates the congruence subgroup Gamma^0(N)}
    require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([1,1,N]);    
    return G;
end intrinsic;

intrinsic GammaUpper1(N::RngIntElt) -> GrpPSL2
   {creates the congruence subgroup Gamma^1(N)}
   require N gt 0: "Argument must be a positive integer";
    G := CongruenceSubgroup([1,N,N]);    
    return G;
end intrinsic;


//////////////////////////////////////////////////////////
//                                                      //
//  creation of normalizer of Gamma_0(N)                //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Normalizer(G::GrpPSL2) -> GrpPSL2
   {The normalizer of a congruence subgroup in SL_2(R)}
   require IsGamma0(G): "the argument must be Gamma_0(N) for some integer N";
   H := init_psl2_group(Level(G),Integers());
   N := Level(G);
   H`gammaType_list := [[N,1,1]]; 
   H`IsNormalizer := true;
   F := Factorization(N);
   r := #F;
   H`LevelFactorization := F;
   H`AtkinLehnerInvolutions := VectorSpace(FiniteField(2),r);
   return H;
end intrinsic;


//////////////////////////////////////////////////////////
//                                                      //
//  creation of random elements of congruence subgroups //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Random(G::GrpPSL2,m::RngIntElt) -> GrpPSL2Elt
    {returns a random element of the projective linear group G,
    m determines the size of the coefficients}    
    // assume the group is congruence, given by [N,M,P]
    N,M,P := Explode(G`gammaType_list[1]);
    limN := Ceiling(m/N);
    limM := Ceiling(m/M);
    limP := Ceiling(m/P);

    g := 0;
    while g ne 1 do
    c := Random(-limN,limN)*N;
    d := Random(-limM,limM)*M + 1;
    b := Random(-limP,limP)*P;
	g, r,a := Xgcd(-c*b,d);
    end while;
    // b and c have been lumped together;
    // so have to change r to r*b, and c*b to c, so that
    // r*b, a = Xgcd(-c,d) :
    b := r*b;
    // matrix [a,b,c,d] is OK, but would like to
    // have top coeffs, a,b as close as possible to
    // requested range, so need to add a multiple of
    // bottom row to top row.
    // WARNING : the following is not quite right yet!
    fac1 := M div Gcd(M,N);
    fac2 := P div Gcd(P,d);
    mul := Lcm(fac1,fac2);
    if c gt 0 then
	lims1 := [-Floor((a+m)/mul/c),Floor((m-a)/mul/c)];
    elif c lt 0 then
	lims1 := [-Floor((m-a)/mul/c),Floor(-(m+a)/mul/c)];
    else lims1 := [0,0];
    end if;
    if d gt 0 then
	lims2 := [-Floor((b+m)/mul/d),Floor((m-b)/mul/d)];
    elif d lt 0 then
	lims2 := [-Floor((m-b)/mul/d),Floor(-(m+b)/mul/d)];
    else lims2 := [0,0];
    end if;

    lims := [Max(lims1[1],lims2[1]),Min(lims1[2],lims2[2])];
    if lims[2] lt lims[1] then
	t := 0;
    else
	t := Random([lims[1],lims[2]]);
    end if;
    
    g := G![a + mul*c*t,b + mul*d*t,c,d];    
    return g;
end intrinsic;



//////////////////////////////////////////////////////////
//                                                      //
//      Methods of obtaining new congruence subgroups:  //
//  congugation and intersetcion                        //
//                                                      //
//////////////////////////////////////////////////////////


intrinsic Intersection(G::GrpPSL2,H::GrpPSL2) -> GrpPSL2
    {returns the intersection of two congruence subgroups.}

  require Type(G`BaseRing) eq RngInt : "G, H must be congruence subgroups";

    conListG := G`conjugate_list;
    conListH := H`conjugate_list;
    require #conListG eq 1 and #conListH eq 1 and
    conListG[1] eq GL(2,G`BaseRing)!1 and
    conListH[1] eq GL(2,H`BaseRing)!1:
    "Not yet implemented for the
    groups you have entered";
    // initiate group
    // find the 3 integers giving group
    HL := (H`gammaType_list)[1];
    GL := (G`gammaType_list)[1];
    A := [Lcm(HL[i],GL[i]) : i in [1..3]];   
    K := init_psl2_group(Lcm(A),Integers());
    K`gammaType_list := [A]; 
    return K;
end intrinsic;
 

intrinsic 'meet' (G::GrpPSL2,H::GrpPSL2) -> GrpPSL2
    {returns the intersection of two congruence subgroups.}
    return Intersection(G,H);
end intrinsic;
