freeze;
///////////////////////////////////////////////////////////////////
//     Functions for cuspidal points/places and Q-rational       //
//        non-cuspidal points on Small Modular Curves            //
//                                                               //
//             mch - 11/2011                                     //
///////////////////////////////////////////////////////////////////

//import "db_io.m": X0NData;

function is_a_cusp_point(p,X0Nd)
    PS := Parent(p);
    seq := Eltseq(p);
    for c in X0Nd`cusps do
      if ISA(Type(c),Pt) then
	if p eq PS!Eltseq(c) then return true; end if;
      else //c a cluster
	if &and[Evaluate(f,seq) eq 0 : f in DefiningPolynomials(c)] then
	  return true;
	end if;
      end if;
    end for;
    return false;
end function;

function is_a_cusp_place(p,X0Nd)
   cp := Cluster(p);
   Saturate(~cp);
   fs := Basis(Ideal(cp));
   A := Ambient(cp);
   for c in X0Nd`cusps do
      if ISA(Type(c),Pt) then
	seq := Eltseq(c);
	if &and[Evaluate(f,seq) eq 0 : f in fs] then return true; end if;
      else //c a cluster
	if A cmpeq Ambient(c) then
	  c1 := c;
	else
	  c1 := Scheme(A,[R!e : e in DefiningPolynomials(c)])
		where R is CoordinateRing(A);
	end if;
	if cp subset c1 then return true; end if;
      end if;
    end for;
    return false;   
end function;

intrinsic Cusp(CN::Crv, N::RngIntElt, d::RngIntElt) -> Any
{ For d a positive divisor of N, returns a point or cluster (depending on whether GCD(d,N/d) <= 2 or not)
  giving the cusps */d on CN, a base change of the curve from the X0N small modular curve database of level N }

    require N gt 0: "N should be a positive integer";
    require (d gt 0) and (IsDivisibleBy(N,d)): "d should be a positive divisor of N";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    ds := Divisors(N);
    c := (X0Ndata`cusps)[Index(ds,d)];
    if ISA(Type(c),Pt) then
	return CN!Eltseq(c);
    else
	A := Ambient(CN);
	return Cluster(A,[R!e : e in DefiningPolynomials(c)])
		where R is CoordinateRing(A);
    end if;

end intrinsic;

intrinsic CuspPlaces(CN::Crv, N::RngIntElt, d::RngIntElt) -> Any
{ For d a positive divisor of N, returns the places above the cusps */d on CN, a base change of the curve
  from the X0N small modular curve database of level N. If CN is defined over Q, there is always a unique
  place }

    require N gt 0: "N should be a positive integer";
    require (d gt 0) and (IsDivisibleBy(N,d)): "d should be a positive divisor of N";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    ds := Divisors(N);
    c := (X0Ndata`cusps)[Index(ds,d)];
    sngs := (assigned X0Ndata`sing_cusps) select X0Ndata`sing_cusps else [];
    sep := (assigned X0Ndata`cusp_pls) select X0Ndata`cusp_pls else [];
    sep := [s : s in sep | (s[1] eq d) or (s[2] eq d)];
    if ISA(Type(c),Pt) and (d notin sngs)then
      return [Place(CN!Eltseq(c))];
    elif ISA(Type(c),Pt) then
      pls := Places(CN!Eltseq(c));
    else
      clstr := ideal<R|[R!e : e in DefiningPolynomials(c)]> where R is
		CoordinateRing(Ambient(CN));
      D := Divisor(CN,clstr);
      pls := Support(D);
    end if;
    if #sep gt 0 then
      F := FunctionField(CN);
    end if;
    for s in sep do
      f := F!((R!s[3])/(R!s[4])) where R is 
	CoordinateRing(Ambient(CN));
      if s[1] eq d then
	pls := [p : p in pls | Valuation(f,p) gt 0];
      else //s[2] eq d
	pls := [p : p in pls | Valuation(f,p) le 0];
      end if;
    end for;
    return pls;

end intrinsic;

intrinsic CuspIsSingular(N::RngIntElt, d::RngIntElt) -> BoolElt
{ For d a positive divisor of N, returns whether the points under the cusps a/d on the X0N small modular
  curve of level N are singular}

    require N gt 0: "N should be a positive integer";
    require (d gt 0) and (IsDivisibleBy(N,d)): "d should be a positive divisor of N";
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    if assigned X0Ndata`sing_cusps then
       return d in X0Ndata`sing_cusps;
    else
       return false;
    end if;

end intrinsic;

intrinsic NonCuspidalQRationalPoints(CN::Crv, N::RngIntElt) -> SeqEnum
{ For CN a base change of the curve from the X0N small modular curve database of level N which is of
  genus > 0, returns all of the non-cuspidal Q-rational points on CN }

    require N gt 0: "N should be a positive integer";
    require Dimension(Ambient(CN)) gt 1: "CN should have genus greater than 0"; 
    try
      X0Ndata := Create_SmallCrvMod_Structure(N);
    catch e
      error e`Object;
    end try;
    if assigned X0Ndata`rat_pts then
       return [CN!Eltseq(r) : r in X0Ndata`rat_pts];
    else
       return [];
    end if;   

end intrinsic;

