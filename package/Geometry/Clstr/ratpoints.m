freeze;

////////////////////////////////////////////////////////////////////////
// ratpoints.m                                                        //
// Based on functions for 'Support' of Clusters: GDB 13/11/00         //
// David Kohel: 06/2002                                               //
////////////////////////////////////////////////////////////////////////

forward ClusterPoints;

////////////////////////////////////////////////////////////////////////
//	              Rational Point Enumeration                      //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
// Accessory boolean test functions                                   //
////////////////////////////////////////////////////////////////////////

function HasPointSet(S,K)
    R := BaseRing(S);
    if R cmpeq K then
	return true, S(K);
    elif Type(R) eq RngInt then
	return true, S(K);
    elif Characteristic(R) eq Characteristic(K) then
	// This must be changed!!!
	return true, S(K);
    end if;
    return false, _;
end function;

function RequireClusterEnum(S)
    bool := (IsAffine(S) or IsOrdinaryProjective(S)) or
        (Dimension(Ambient(S)) eq 2 and #Gradings(S) eq 2) or
        (#Gradings(S) eq 1 and Gradings(S)[1][1] eq 1 and Gradings(S)[1][3] eq
        1);
    return bool,
        "Argument must lie in affine or ordinary projective space " * 
        "space, or in a surface scroll, or a weighted projective plane with "*
        "weights 1,*,1.";
end function;

function RequireSchemeEnum(S)
    bool :=
        (IsAffine(S) or IsOrdinaryProjective(S)) and 
        Type(BaseRing(S)) eq FldFin;
    emsg :=
        "General scheme arguments of positive dimension must " * 
	"lie in an affine or ordinary space, and be defined over " * 
	"a finite field for rational point enumeration.";
    return bool, emsg;
end function;

////////////////////////////////////////////////////////////////////////
// Point enumeration                                                  //
////////////////////////////////////////////////////////////////////////

intrinsic RationalPointsGeneric(S::Sch: Al := "") -> SetIndx
{Generic rational points intrinsic}

 require Al in ["", "Direct", "Fibration" ] : "Al can only be set to Direct or Fibration";

 K:=BaseRing(S); require IsField(K) : "Base ring of argument must be a field.";
 if IsEmpty(S) then return {@ S(K) | @}; 
 elif Dimension(S) eq 0 then 
  bool, emsg := RequireClusterEnum(S); require bool : emsg;
  require IsExact(K) : "Base ring must be exact";
  return ClusterPoints(S,K);
 else 
  bool, emsg := RequireSchemeEnum(S);
  require bool : emsg;
  da := Dimension(Ambient(S));

  if Al eq "" then 
   if (da-Dimension(S) le 1) or ((#K)^da lt 10^7) then Al := "Direct"; end if;
  end if;

  if Al eq "Direct" then
    return Ratpoints(S);
  else
    return RationalPointsByFibration(S);
  end if; 
 end if; 
end intrinsic;

function BaseRingIsQorZ(X)
//{Returns whether the BaseRing of a Scheme is Q or Z}
 if Type(BaseRing(X)) ne FldRat and Type(BaseRing(X)) ne RngInt
 then return false; end if; return true; 
end function;

intrinsic RationalPoints(S::Sch : Bound:=1000, Al := "") -> SetIndx
{An indexed set of the rational points of S over its base field}
 if Type(BaseRing(S)) eq FldRat then 
   if IsProjective(S) and ISA(Type(S),Crv) and IsQuadricIntersection(S) then
     return SetToIndexedSet(Set(PointsQI(S,Bound))); end if;
   if IsPlanar(S) and IsCurve(S) and IsProjective(S) and IsIrreducible(S) then 
     return SetToIndexedSet(Set(PointSearch(S,Bound))); end if;
 end if;
 return RationalPointsGeneric(S: Al := Al); 
end intrinsic;

intrinsic RationalPoints(S::Sch,K::Rng : Bound:=1000, Al := "") -> SetIndx
 {An indexed set of the rational points of S(K). 
  Setting Al to "Direct" or "Fibration" chooses the algorithm to be used 
  if the scheme is generic. 
  If Al is not set the algorithm will be choosen heuristically.}
 require IsField(K) : "Base ring of argument must be a field.";

 require Al in ["", "Direct", "Fibration" ] : "Al can only be set to Direct or Fibration";
 bool, PSK := HasPointSet(S,K);
 require bool :
 "Argument 2 must have algebra structure over base ring of argument 1.";
/*
id := DefiningIdeal(S);
idK := BaseRing(id);
if Type(K) eq FldNum then
    _<w> := idK;
end if;
AssignNamesBase(~id, "x");
id;
*/
 if IsEmpty(S) then return {@ PSK | @};
 elif Dimension(S) eq 0 then 
  bool, emsg := RequireClusterEnum(S); require bool : emsg;
  require IsExact(K) : "Base ring must be exact";
  return ClusterPoints(S,K);
 else bool, emsg := RequireSchemeEnum(S); 
    require bool : emsg;
    da := Dimension(Ambient(S));

    if Al eq "" then 
     if (da-Dimension(S) le 1) or ((#K)^da lt 10^7) then Al := "Direct"; end if;
    end if;
    
    if Al eq "Direct" then
      return Ratpoints(PSK);
    else
      pts := RationalPointsByFibration(BaseChange(S,K));
      return {@ PSK!Eltseq(pt) : pt in pts @};
    end if; 
 end if;
end intrinsic;

intrinsic Points(S::Sch : Bound:=1000, Al := "") -> SetIndx
 {Same as RationalPoints.}
return RationalPoints(S : Bound:=Bound, Al := Al); end intrinsic;

intrinsic Points(S::Sch,K::Rng) -> SetIndx
 {Same as RationalPoints.}
 require IsField(K) : "Base ring of argument must be a field.";
 bool, PSK := HasPointSet(S,K);
 require bool :
 "Argument 2 must have algebra structure over base ring of argument 1.";
return RationalPoints(S,K); end intrinsic;

////////////////////////////////////////////////////////////////////////
//	            Rational Point Enumeration                        //
////////////////////////////////////////////////////////////////////////

Tupseq := func< t | [ t[i] : i in [1..#t] ] >;

function ClusterPoints(Z,K)
    if IsAffine(Z) then
	if IsAmbient(Z) then return {@ Z(K)![] @}; end if;
	assert IsExact(K) or IsEuclideanRing(K) and not IsField(K);
	return {@ Z(K) | Z(K)!Tupseq(p) : p in Variety(DefiningIdeal(Z),K) @};
    elif IsOrdinaryProjective(Z) then
	A := Ambient(Z);
	d := Dimension(A);
	if d eq 0 then // special case to avoid affine patch problem
	    if IsEmpty(Z) then
		return {@ Z(K) | @};
	    else
		return {@ Z(K)![1] @};
	    end if;
	end if;
	Z0 := Z;
	ratpts := {@ Z(K) | @};
	for i in [1..d+1] do
	    U0 := AffinePatch(Z0,i);
	    ratpts join:= {@ Z(K)!p : p in RationalPoints(U0,K) @};
	    Z0 := Scheme(A, DefiningPolynomials(Z0) cat [A.(d+2-i)]);
	end for;
    elif #Gradings(Z) eq 1 and Gradings(Z)[1][1] eq 1 and
                               Gradings(Z)[1][3] eq 1 then
        //separate case for hyperelliptic curves
        Za:=AffinePatch(Z,1);
        PC:=ProjectiveClosureMap(Ambient(Za));
        ratpts:={@ PC(p): p in RationalPoints(Za,K) @};
        Za:=AffinePatch(Z meet Scheme(Ambient(Z),Z.3),3);
        PC:=ProjectiveClosureMap(Ambient(Za));
        ratpts join:={@ PC(p): p in RationalPoints(Za,K) @};
        if not(IsEmpty(Z meet Scheme(Z,[Z.1,Z.3]))) then
          ratpts join:= {@ Z(K)![0,1,0] @};
        end if;
    else                           
	A := Ambient(Z);
	d := Dimension(A);
	gr := Gradings(Z);
	ratpts := {@ Z(K) |  @};
	Z0 := Z;
	for i in [1..d+#gr] do
	    U0 := AffinePatch(Z0,i);
	    ratpts join:= {@ Z(K)!p : p in RationalPoints(U0,K) @};
	    // THINK: the next line is trickier in this case; 
	    // it will speed up calculations up once it's right.
	    // Z0 := Scheme(A, DefiningPolynomials(Z0) cat [A.(d+3-i)] );
	end for;
    end if;
    return ratpts;
end function;
