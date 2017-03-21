freeze;

///////////////////////////////////////////////////////////////////
//     Intrinsics for computing the Kodaira-Enriques  		 //
//  type of ordinary projective surfaces with only simple 	 //
//   singularities and for computing minimal models of		 //
//   non-singular surfaces of Kodaira dimension <= 0		 //
//             mch - 10/2012                                     //
///////////////////////////////////////////////////////////////////

declare attributes Srfc:
    // invariants (for models with only simple sings)
    pg,		// RngIntElt - geometric genus
    q,		// RngIntElt - Irregularity
    K2,		// RngIntElt - K.K
    K2m,	// RngIntElt - K.K for a minimal model of S

    //NB: all Hodge diamond numbers, arith genus etc. are derivable from these
    /////////////////////////////////////////////////
    // Kodaira-Enriques classification data
    kod_dim,	// RngIntElt - Kodaira dimension (-1,0,1 or 2)
    kod_enr2,	// RngIntElt - secondary code number to specify K-E type for kod_dim 0:
	        // -3 = Enriques, -2 = K3, -1 = torus, 0 = bielliptic (order K unknown)
		//    2,3,4,6 (=r) = bielliptic (order K = r) 
    /////////////////////////////////////////////////
    // properties
    only_simple_sings, // BoolElt - does S have at worst simple (point) singularities
    simp_sings,	//  List - if S has only simple sings this contains a list of the
		//   singular points (over an extension) and their type

    //NB : non-sing => only_simple_sings => gor => CM, arith_gor => ACM and gor
    //  and ACM => CM. Also CM & (only point singularities) => normal
    ////////////////////////////////////////////
    // (maps to) other models
    min_map,	//  Map (MapSch/MapSchGrph) - birational map onto an ordinary
		// projective minimal model of S
    can_mod_map,//  Map (MapSch/MapSchGrph) - birational map from S of general type
		// to the weighted projective canonical model S1 of S (the
		// coordinate ring of S1 is the canonical coordinate ring)
    fibre_map;	// a map to a non-singular projective curve C with geometrically
		// integral general fibre

declare attributes Sch:
    // 'singularity' properties for schemes that are worth putting in now
    //  for more general schemes than just surfaces 
    CM,		//  BoolElt - is X (locally) Cohen-Macaulay
    ACM,	//  BoolElt - is X arithmetically Cohen-Macaulay (ie with CM coordinate ring)
    gor,	//  BoolElt - is X (locally) Gorenstein
    arith_gor,	//  BoolElt - is X arithmetically Gorenstein
    normal,	//  BoolElt - is X normal
    // sheaves
    KX;		//  ShfCoh - the canonical sheaf of X (X assumed CM at least)

declare verbose KodEnr, 1;
declare verbose MinModel, 1;

//// Functions to compute Kodaira-Enriques type /////

function h0(S)
// returns h^0(S) - the dimension of global sections of S
    SaturateSheaf(~S);      
    M := S`Mfull; n := 0;
    P := BaseRing(M);
    R := BaseRing(P);
    wts := ColumnWeights(M);
    N := #wts;//Rank(M)

    if n lt Min(wts) then
	return 0;
    end if;

    /* get all monomials of correct degree for each column */
    degs := [n-w : w in wts];
    diff_degs := Sort(Setseq(Seqset([d : d in degs | d ge 0])));
    Mons_d := [Setseq(MonomialsOfDegree(P,d)) : d in diff_degs];
    colMons := [(ind eq 0) select [P|] else Mons_d[ind] where
	ind is Index(diff_degs,d) : d in degs];

    V := KSpace(R,&+[#cm : cm in colMons]);
    mp_MtoV := map<M->V | m :-> 
	V!&cat[[MonomialCoefficient(e[i],mon):mon in colMons[i]]: i in [1..#e]]
		where e is Eltseq(m)>;
    
    //get relations
    Wvecs := [V|];
    rels := RelationMatrix(M);
    mp_PrtoV := map<PowerSequence(P)->V | m :-> 
        V!&cat[[MonomialCoefficient(m[i],mon):mon in colMons[i]]: i in [1..#m]]>;
    for i in [1..Nrows(rels)] do
        rel := Eltseq(rels[i]);
        if &and[f eq P!0 : f in rel] then continue; end if;
        d_min := Min([Min([TotalDegree(t)+wts[j] : t in Terms(rel[j])]) : 
                        j in [1..N] | rel[j] ne P!0]);
        d_max := Max([Max([TotalDegree(t)+wts[j] : t in Terms(rel[j])]) : 
                        j in [1..N] | rel[j] ne P!0]);
    
        for d in [d_min..d_max] do
            if d gt n then break; end if;
            rel_d := [P| (#ts eq 0 select 0 else &+[t:t in ts]) where
               ts is [te:te in Terms(rel[j])|TotalDegree(te) eq d-wts[j]] :
                           j in [1..N] ];
            Monoms := MonomialsOfDegree(P,n-d);
            Wvecs cat:= [mp_PrtoV([r*m:r in rel_d]):m in Monoms];
        end for;
    end for;
    delete mp_PrtoV;

    WS := Rowspace(Matrix(Wvecs));
    return Dimension(V)-Dimension(WS);

end function;

function has_elliptic_cmpt(I,X,bMin)
// I is the (saturated) ideal defining an effective divisor D on surface X
// in ord proj space. Returns whether D has an elliptic curve component.
// Used to distinguish between some cases of bi-elliptic surfaces
// and elliptic fibrations where D is either just a multiple
// sum of rational curves contracted in the minimal model or
// it also contains some multiples of (blow-ups of) multiple fibre
// elliptic curves. If bMin = true, then X is known to be minimal, so
// only D=0 or D!=0 need be checked.
  
   if not IsProper(I) then //D=0
	return false;
   end if;
   if bMin then return true; end if;
   ps := RadicalDecomposition(I);
   P := Ambient(X);
   return &or[((Dimension(Y) eq 1) and (ArithmeticGenus(Y) eq 1))
	where Y is Scheme(P,J) : J in ps];
end function;

intrinsic KodairaEnriquesType(X::Srfc : CheckADE := false) -> RngIntElt,RngIntElt,MonStgElt
{ Computes the Kodaira-Enriques type of surface X with at most simple singularities. }

    if (assigned X`kod_dim) and ((X`kod_dim ne 0) or (assigned X`kod_enr2)) then
	kd := X`kod_dim;
	case kd:
	  when -1:
	    if not assigned X`q then
	      X`q := GeometricGenus(X)-ArithmeticGenus(X);
	    end if;
	    q := X`q;
	    if q eq 0 then return -1,0,"Rational";
	    else
	      return -1,q,"Ruled surface over genus " cat IntegerToString(q) cat " curve";
	    end if;
	  when 0:
	    assert assigned X`kod_enr2;
	    ke2 := X`kod_enr2;
	    if ke2 eq -3 then
		return 0,-3,"Enriques";
	    elif ke2 eq -2 then
		return 0,-2,"K3";
	    elif ke2 eq -1 then
		return 0,-1,"Torus";
	    elif ke2 eq 0 then
		return 0,0,"Bi-elliptic";
	    else //ke2 > 0
		return 0,ke2,"Bi-elliptic (type " cat IntegerToString(ke2) cat ")";
	    end if;
	  when 1: return 1,0,"Elliptic fibration";
	  when 2: return 2,0,"General type";
	end case;
    end if;

    if CheckADE then
	if not (assigned X`only_simple_sings) then
	  vprint KodEnr: "Checking that X has only simple singularities";
	  boo := HasOnlySimpleSingularities(X);
	end if;
	require X`only_simple_sings:
		"Surface argument X should have only simple singularities";
    end if;

    if not (assigned X`pg) then
	KX := CanonicalSheaf(X);
	SaturateSheaf(~KX);
	X`pg := h0(KX); //geometric genus of X
    end if;
    p1 := X`pg;
    if not (assigned X`q) then
	pa := ArithmeticGenus(X);
	q := p1-pa;
	assert q ge 0;
	X`q := q;
    else
	q := X`q;
	pa := p1-q;
    end if;

    if pa lt -1 then // (birationally) ruled surface case
	assert p1 eq 0;
        X`kod_dim := -1; 
	return -1,q,"Ruled surface over genus " cat IntegerToString(q) cat " curve",
	   _,_;
    end if;

    KX := CanonicalSheaf(X);
    SaturateSheaf(~KX);

    if p1 ge 3 then
	f1,X1 := DivisorMap(KX);
	if Dimension(X1) eq 2 then
	  X`kod_dim := 2;
	  return 2,0,"General type";
	end if;
    end if;

    K2 := TensorPower(KX,2);
    p2 := h0(K2); //2nd plurigenus
    assert p2 ge p1;

    if (q eq 0) and (p1 eq 1) and (p2 eq 1) then //K3 surface
	X`kod_dim := 0; X`kod_enr2 := -2;
	return 0,-2,"K3";
    end if;

    if (q eq 2) and (p1 eq 1) then //torus or elliptic fibration
	if p2 eq 1 then
	  X`kod_dim := 0; X`kod_enr2 := -1;
	  return 0,-1,"Torus";
	else
	  X`kod_dim := 1;
	  return 1,0,"Elliptic fibration";
	end if;
    end if;

    if (p1 eq 0) then
      if q eq 0 then
	if p2 eq 0 then
	  X`kod_dim := -1;
	  return -1,0,"Rational";
	end if;
	K3 := TensorProduct(K2,KX : Maximize := true);
	p3 := h0(K3);
	if p2 eq 1 then
	  if p3 eq 0 then
	    X`kod_dim := 0; X`kod_enr2 := -3;
	    return 0,-3,"Enriques";
	  else
	    X`kod_enr := 1;
	    return 1,0,"Elliptic fibration";
	  end if;
	else //p2 >= 2
	  boo := (p3 eq (3*p2-2)); //condition for gen type
	  if boo and (p2 eq 2) then
	   //Yuck! could also be an elliptic fibration.
	   _,X3 := DivisorMap(K3);
	   boo := (Dimension(X3) eq 2);
	  end if;  
	  if boo then
	    X`kod_enr := 2; X`K2m := p2-pa-1;
	    return 2,0,"General type";
	  else
	    X`kod_enr := 1;
	    return 1,0,"Elliptic fibration";
	  end if;
	end if;
      else //q=1
	if p2 ge 2 then
	  X`kod_enr := 1;
	  return 1,0,"Elliptic fibration";
	elif p2 eq 1 then
	  // have bi-elliptic (type 2) or ell fib
	  // first try p4 to separate cases
	  K4 := TensorPower(K2,2);
	  p4 := h0(K4); //4th plurigenus
	  if p4 ge 2 then boo := true; end if;
	  // if p4=1 could still be a particular type of
	  // ell fib. p6 separates the cases
	  if not boo then
	    p6 := h0(TensorProduct(K4,K2 : Maximize := true));
	    boo := (p6 ge 2);
	  end if;  
	  if boo then
	    X`kod_enr := 1;
	    return 1,0,"Elliptic fibration";	
	  else
	    X`kod_enr := 0; X`kod_enr2 := 2;
	    return 0,2,"Bi-elliptic (type 2)";
	  end if;
	end if;
      end if;
    end if;

    if p2 eq 0 then //bi-elliptic or elliptic fibration or ruled with q=1
	// NB: Kod dim 1 srfs with p1=p2=0, q=1 correspond to
        // elliptic fibrations over P^1 with 3 bad fibres
	// (char !=2,3) that are multiples of a genus 1 curve with mults
	// m1,m2,m3 with (1/m1)+(1/m2)+(1/m3) < 1. If we could avoid these
	// unusual cases, we could avoid the calls to has_elliptic_cmpt below.
	K3 := TensorProduct(K2,KX : Maximize := true);
	p3 := h0(K3); //3rd plurigenus
	if p3 ne 0 then
	  if p3 eq 1 then
	    if not assigned X`K2 then
		X`K2 := IntersectionPairing(KX,KX);
	    end if;
	    D := SheafToDivisor(K3);
	    boo := has_elliptic_cmpt(D`ideal,X,X`K2 eq 0);
	  else
	    boo := true;
	  end if;
	  if boo then
	    X`kod_dim := 1;
	    return 1,0,"Elliptic fibration";
	  else
	    X`kod_dim := 0; X`kod_enr2 := 3;
	    return 0,3,"Bi-elliptic (type 3)";
	  end if;
	end if;
	K4 := TensorPower(K2,2);
	p4 := h0(K4); //4th plurigenus
	if p4 ne 0 then
	  if p4 eq 1 then
	    if not assigned X`K2 then
		X`K2 := IntersectionPairing(KX,KX);
	    end if;
	    D := SheafToDivisor(K4);
	    boo := has_elliptic_cmpt(D`ideal,X,X`K2 eq 0);
	  else
	    boo := true;
	  end if;
	  if boo then
	    X`kod_dim := 1;
	    return 1,0,"Elliptic fibration";
	  else
	    X`kod_dim := 0; X`kod_enr2 := 4;
	    return 0,4,"Bi-elliptic (type 4)";
	  end if;
	end if;
	delete K4;
	K6 := TensorPower(K3,2);
	p6 := h0(K6); //6th plurigenus
	if p6 eq 0 then
	  X`kod_dim := -1;
	  return -1,1,"Ruled surface over genus 1 curve";
	else //p6 > 0
	  if p6 eq 1 then
	    if not assigned X`K2 then
		X`K2 := IntersectionPairing(KX,KX);
	    end if;
	    D := SheafToDivisor(K6);
	    boo := has_elliptic_cmpt(D`ideal,X,X`K2 eq 0);
	  else
	    boo := true;
	  end if;
	  if boo then
	    X`kod_dim := 1;
	    return 1,0,"Elliptic fibration";
	  else
	    X`kod_dim := 0; X`kod_enr2 := 6;
	    return 0,6,"Bi-elliptic (type 6)";
	  end if;	  
	end if;
    end if;

    // Only elliptic fibrations and gen type cases left.
    // Having disposed of all p1=0 cases, 
    // Francia's thm + Catenese & Ciliberto => image of the
    // divisor map for K2 is dim 2 or KodDim(X) = 1
    if p2 le 2 then
	X`kod_dim := 1;
	return 1,0,"Elliptic fibration";
    else // p2 >= 3
      _,X2 := DivisorMap(K2);
      assert p2 eq Dimension(Ambient(X2))+1;
      if Dimension(X2) eq 2 then
	X`kod_dim := 2; X`K2m := p2-pa-1;
	return 2,0,"General type";
      else
	X`kod_dim := 1;
	return 1,0,"Elliptic fibration";
      end if;	
    end if;

end intrinsic;

intrinsic KodairaDimension(X::Srfc : CheckADE := false) -> RngIntElt
{ Computes the Kodaira dimension of surface X with at most simple singularities. }

    if not assigned X`kod_dim then
	kd := KodairaEnriquesType(X : CheckADE := CheckADE);
    end if;
    return X`kod_dim;

end intrinsic;

intrinsic MinimalModelRationalSurface(X::Srfc : CheckSing := false) -> Map
{ Computes and returns a birational map to a standard quasi-minimal (terminal) model for 
rational non-singular ordinary projective surface X }

    if assigned X`min_map then return X`min_map; end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckSing then
	require IsNonsingular(X):
		"Surface argument X should be non-singular";
    end if;

    n := Rank(CoordinateRing(Ambient(X)));
    if n eq 3 then // X is P^2!
       return IdentityMap(X);
    end if;

    // first make sure that X is embedded linearly normally
    // in P^n
    HX := StructureSheaf(X,1);
    SaturateSheaf(~HX);
    h := h0(HX);
    assert h ge n;
    if h ne n then
	mp,Y := DivisorMap(HX);
	n := h;
    else
	Y := X; mp := 0;
    end if;

    // special case of Veronese surface, rational scroll or Del Pezzo
    d := Degree(Y);
    if d le n-1 then
      X`min_map := ((Type(mp) eq RngIntElt) select IdentityMap(X) else mp);
      return X`min_map;
    end if;
    K := CanonicalSheaf(Y);

    while true do
      KplusH := Twist(K,1);
      mp1,Y1 := DivisorMap(KplusH); //adjunction map
      d1 := Dimension(Y1);
      assert d1 ge 1;
      if Dimension(Y1) eq 1 then // Y is conic bundle
	return ((Type(mp) eq RngIntElt) select IdentityMap(X) else mp);
      end if;
      n := Rank(CoordinateRing(Ambient(Y1)));
      d := Degree(Y1);
      // check for Y a deg 1 or 2 Del Pezzo
      if n eq 3 then //Y1 is P^2
	n1 := Rank(CoordinateRing(Ambient(Y)));
	d1 :=  Degree(Y);
	if ((n1 eq 7) and (d1 eq 8)) or ((n1 eq 6) and (d1 eq 7)) then
	  //Y poss a -2K embedded deg 2 Del Pezzo or single blow-up
	  if IntersectionPairing(KplusH,KplusH) eq 2 then
	    break;	  
	  end if;
	end if;
      elif (n eq 4) and (d eq 2) and IsSingular(Y1) then
	//Y a -3K embedded deg 1 Del Pezzo
	break;
      end if;
      mp1 := Restriction(mp1,Y,Y1);
      mp := (Type(mp) eq RngIntElt) select mp1 else Expand(mp*mp1);
      // check for P^2, Veronese, rational scroll or Del Pezzo
      if d le n-1 then
	break;
      end if;
      Y := Y1;
      K := CanonicalSheaf(Y);
    end while;
    if Type(mp) eq RngIntElt then
	X`min_map := IdentityMap(X);
    else
	X`min_map := mp;
	Y := Codomain(mp);
	Y`pg := 0; Y`q := 0; Y`K2m := 9;
	Y`kod_dim := -1; Y`min_map := IdentityMap(Y);
	if not assigned Y`Nonsingular then Y`Nonsingular := true; end if;
    end if;
    return X`min_map;

end intrinsic;

intrinsic MinimalModelRuledSurface(X::Srfc : CheckSing := false) -> Map
{ Computes and returns a birational map to a standard quasi-minimal (terminal) model for 
non-singular ordinary projective birationally ruled surface X}

    if assigned X`min_map then return X`min_map; end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckSing then
	require IsNonsingular(X):
		"Surface argument X should be non-singular";
    end if;
    if not assigned X`q then X`q := -ArithmeticGenus(X); end if;
    q := X`q;
    if q eq 0 then //rational case
	return MinimalModelRationalSurface(X : CheckSing := false);
    end if;

    mp := 0; Y := X;
    while true do
      KplusH := Twist(CanonicalSheaf(Y),1);
      if h0(KplusH) eq 0 then //Y a non-rational scroll
	break;
      end if;
      mp1,Y1 := DivisorMap(KplusH); //adjunction map
      d1 := Dimension(Y1);
      assert d1 ge 1;
      if (d1 eq 1) or (Dimension(Ambient(Y1)) eq 2) then 
	// d1=1 => Y is a conic bundle. Y1=P^2 => Y is a non-split ruled
	// surface over an elliptic curve with e=-1, embedded by 3*C0
	break;
      end if;
      mp1 := Restriction(mp1,Y,Y1);
      mp := (Type(mp) eq RngIntElt) select mp1 else Expand(mp*mp1);
      Y := Y1;     
    end while;
    if Type(mp) eq RngIntElt then
	X`min_map := IdentityMap(X);
    else
	X`min_map := mp;
	Y := Codomain(mp);
	Y`pg := 0; Y`q := q; Y`K2m := 8;
	Y`kod_dim := -1; Y`min_map := IdentityMap(Y);
	if not assigned Y`Nonsingular then Y`Nonsingular := true; end if;
    end if;
    return X`min_map;   

end intrinsic;

intrinsic MinimalModelKodairaDimensionZero(X::Srfc : CheckSing := false) -> Map
{ Computes and returns a birational map to a minimal model for 
non-singular ordinary projective surface of Kodaira dimension 0}

    if assigned X`min_map then return X`min_map; end if;
    require IsOrdinaryProjective(X):
	"Argument X should be a surface in ordinary projective space";
    if CheckSing then
	require IsNonsingular(X):
		"Surface argument X should be non-singular";
    end if;

    mp := 0; Y := X;
    K := CanonicalSheaf(Y);
    if not assigned Y`K2 then
	Y`K2 := IntersectionPairing(K,K);
    end if; 
    while Y`K2 lt 0 do
      mp1,Y1 := DivisorMap(Twist(K,1)); //adjunction map
      mp1 := Restriction(mp1,Y,Y1);
      mp := (Type(mp) eq RngIntElt) select mp1 else Expand(mp*mp1);
      Y := Y1;
      K := CanonicalSheaf(Y);
      Y`K2 := IntersectionPairing(K,K);   
    end while;
    if Type(mp) eq RngIntElt then
	X`min_map := IdentityMap(X);
    else
	X`min_map := mp;
	Y := Codomain(mp);
	Y`K2m := 0;
	Y`kod_dim := 0; Y`min_map := IdentityMap(Y);
	if assigned X`pg then
	  Y`pg := X`pg;
	else
	  Y`pg := h0(K); X`pg := Y`pg;
	end if;
	if assigned X`q then
	  Y`q := X`q;
	else
	  Y`q := (Y`pg)-ArithmeticGenus(Y); X`q := Y`q;
	end if;
	if not assigned Y`Nonsingular then Y`Nonsingular := true; end if;
    end if;
    return X`min_map;   

end intrinsic;

