freeze;

declare type AInfinity;
declare attributes AInfinity: A, k, i, R, S, P, m, f;

/*********************************************************************/
/* Taking preimages is a matter of solving linear equations, and thus
 * treated as such.
 */

preimage := function(cpx, v, n)
// { Return the preimage of v under the nth boundary map of cpx. }
return Solution(BoundaryMap(cpx,n),v);
end function;

preimages := function(cpx,v,n)
// { Returns the list of preimages of the vectors in v under the nth boundary map of cpx. }
return [ preimage(cpx,x,n) : x in v ];
end function;

primageF := function(f,v)
// { Returns the preimage of v under the map f. Throws an error unless v is in the image of f. }
return Solution(f,v);
end function;

preimagesF := function(f,vs)
// { Returns the list of preimages of the vectors in v under the map f. Throws an error unless the vectors in v are actually in the image of f. }
return [ Solution(f,v) : v in vs ];
end function;

/* Constructs the matrices of the right module actions of the basis elements
 * of an algebra A. Has been tested with algebras from AlgBasGrpP, but should
 * work in wider circles than that.
 */
basisActions := function(A)
    B := Basis(A);

    gs := [ Matrix([ b*v : v in B ]) : b in B];
    return gs;	
end function;


intrinsic ActionMatrix(A :: AlgBas,
    x :: Mtrx) -> ModMatFldElt
    { Given a vector x representing an element of A, returns a matrix corresponding to the right multiplication action of this vector on the algebra. }
    B := Basis(A);
    Ba := basisActions(A);
    V := VectorSpace(A);
    cs := Coordinates(V,V!x);

    return &+ [ cs[i]*Ba[i] : i in [1..#cs]];
end intrinsic;
    

/****************************************************/

/* Suppose you had a Cohomology Ring CR calculated,
   and you wish to perform calculations in it. Start
   by constructing an appropriate quotient ring. */

intrinsic CohomologyRingQuotient(CR :: Rec) -> Rng,Map
{ Returns the quotient ring of cohomology for a CohomologyRing result. }
return quo<CR`PolRing|CR`RelationsIdeal>;
end intrinsic;

/*****************************************************/

intrinsic LiftToChainmap(P :: ModCpx,
                         f :: Mtrx,
                         d :: RngIntElt) -> MapChn
{ Takes a module map and returns the corresponding chain map,
  unique up to chain homotopy, lifting the map in question. }
  Pmax,Pmin := Degrees(P);
  A := Algebra(P);
  V := VectorSpace(A);
  maps := [* f *];
  for i in [Pmin-d+1..Pmax] do
      B:= Basis(Term(P,i));
      fB := [ v@(BoundaryMap(P,i)*maps[i+d]) : v in B ];
      pfB := preimages(P,fB,i+d);

      M := Matrix(pfB);

      dA := Dimension(A);
      dn := #B/dA;
      d1 := Dimension(Term(P,i+d))/dA;
      

/* The following block converts the map to a A-module map by looking
 * at the tops for each block matrix component of the map, and
 * slotting in corresponding right group action matrices.
 */
      for x in [1..dn] do
	  for y in [1..d1] do
	      xx := 1+(x-1)*dA;
	      yy := 1+(y-1)*dA;

	      InsertBlock(~M,ActionMatrix(A,V!Submatrix(M,xx,yy,1,dA)),xx,yy);
	  end for;
      end for;
      Append(~maps,M);
  end for;
  // The ChainMap constructor expects the maps in reverse order to our
  // construction. 
  return ChainMap(Reverse(maps),P,P,d);
end intrinsic;

/* We know a map to be null-homotopic. We need to find a null homotopy
   for it. 
*/

intrinsic NullHomotopy(f :: MapChn) -> MapChn
{ Returns a null homotopy of the map f. This should fail IsChainMap and 
   similar tests. }
   P := Domain(f);
   Q := Codomain(f);
   n := Degree(f);
   A := Algebra(P);
   V := VectorSpace(A);
   ff := Field(V);
   dA := Dimension(V);

   Pmax,Pmin := Degrees(P);
   Qmax,Qmin := Degrees(Q);
   
   Ms := [* AHom(Term(P,Qmin-n-1),Term(Q,Qmin)) ! 0 *];

   for i in [Qmin-n .. Pmax] do
       B := Basis(Term(P,i-Pmin));
       fB := [ Term(P,i-Pmin+n) ! v@(ModuleMap(f,i-Pmin) -
	   (-1)^n*BoundaryMap(P,i-Pmin)*Ms[1+i+n-Qmin]) : v in B ];
       ffB := [ fB[1+(k-1)*dA] : k in [1..#B/dA] ];
       pfB := preimages(Q,ffB,i+n+1);

       M := AHom(Term(P,i-Pmin),Term(Q,i+n+1))!0;
       Mp := Matrix(pfB);
       
       dA := Dimension(A);
       dn := NumberOfRows(M)/dA;
       d1 := NumberOfColumns(M)/dA;
       
       /* The following block converts the map to a A-module map by looking
        * at the tops for each block matrix component of the map, and
        * slotting in corresponding right group action matrices.
        */

       for x in [1..dn] do
	   for y in [1..d1] do
	       xx := 1+(x-1)*dA;
	       yy := 1+(y-1)*dA;
	       
	       InsertBlock(~M,ActionMatrix(A,V!Submatrix(Mp,x,yy,1,dA)),xx,yy);
	   end for;
       end for;
       Append(~Ms,M);
   end for;
   
   return ChainMap(Reverse(Ms),P,Q,n+1);   
end intrinsic;

intrinsic IsNullHomotopy(f :: MapChn,
    H :: MapChn) -> BoolElt
    { Verifies a given null homotopy. }

    P := Domain(f);
    Q := Codomain(f);

    Pmax,Pmin := Degrees(P);
    Qmax,Qmin := Degrees(Q);

    n := Degree(f);

    checks := [];
    
    for i in [Qmin-n..Pmax] do
	d := BoundaryMap(P,i);
	dd := BoundaryMap(Q,i+n+1);
	ff := ModuleMap(f,i);
	h := ModuleMap(H,i);
	hh := ModuleMap(H,i-1);

	Append(~checks,IsZero(d*hh+h*dd + (-1)*ff));
    end for;
    return &and checks;
end intrinsic;



MapToTops := function(f, n)
    rn := NumberOfRows(f);

    return Matrix(rows) where
	rows is [ rs[i] : i in [1..rn] | i mod n eq 1] where
	rs is RowSequence(f);
end function;

intrinsic ChainmapToCohomology(f :: MapChn,
    CR :: Rec) -> RngElt
    { Takes a cocycle and returns an element of the cohomology quotient
    ring containing that cocycle. }
    S := CohomologyRingQuotient(CR);
    MD := CR`MonomialData;
    d := -Degree(f);
    f0 := ModuleMap(f,d);
    P := Domain(f);
    Pmax,Pmin := Degrees(P);
    A := Algebra(P);
    k := SimpleModule(A,1);
    e := AHom(Term(P,Pmin),k).1;
    ff := f0 * e;
    F := MapToTops(ff,Dimension(A));
    B := [ MD[i] : i in [1..#MD] | MD[i][1] eq d ];


    vf := Vector(Eltseq(F));
    vB := Matrix([ Eltseq(ModuleMap(v[3],d)) : v in B ]);
    cf := Eltseq(Solution(vB,vf));

    return S!&+ [ cf[i]*B[i][2] : i in [1..#B] ];
end intrinsic;

findMonomial := function(m,R)
    foo:=exists(j){ i : i in R`MonomialData | Parent(m)!i[2] eq m };
    assert foo;
    return j;
end function;

expandMap := function(F,m,n)
    k := NumberOfRows(m);
S := Matrix(F,n*k,n,[]);
for i in [1..k] do
    InsertBlock(~S,ScalarMatrix(n,m[i,1]),1+(i-1)*n,1);
end for;
return S;
end function;

intrinsic CohomologyToChainmap(xi :: RngElt,
    CR :: Rec,
    P :: ModCpx) -> MapChn
    { Takes an element of the quotient cohomology ring and constructs a chain map within that coclass. }
    c := Coefficients(xi);
    m := Monomials(xi);
    n := #c;
    MD := CR`MonomialData;
    
    seeds := [ <findMonomial(x,CR)[3],WeightedDegree(x)> : x in m ];
    cochains := [ <ModuleMap(x[1],x[2]),x[2]> : x in seeds ];
    modmaps := [ <expandMap(Parent(c[1]),x[1],Dimension(Term(P,0))),x[2]>:x in cochains ];
    cocycles := [ LiftToChainmap(P,c[i]*modmaps[i][1],-modmaps[i][2]) : i in [1..n] ];

    return &+ cocycles;
end intrinsic;

/* The code, as it stands, should very easily extend to any Basic Algebra -
 * however, the support for cohomology ring calculation is not good enough
 * for anything but p-group basic algebras. Once CohomologyRing works
 * well enough for Basic algebras, the code here can be easily extended.
 *
 * The extension work basically only needs to give a new constructor that
 * allows the user to set A, i and n himself, and generates k, R, P, S for him.
 */
intrinsic AInfinityRecord(G :: Grp, n :: RngIntElt) -> Rec
    { Constructs the data structure storing data for Aoo calculations
    in group cohomology. Expects G to be a p-group. n controls how
    far resolutions are pushed and might be depreciated later. }

    A := BasicAlgebra(G);
    i := 1;
    k := SimpleModule(A,i);
    R := CohomologyRing(k,n);
    P := ProjectiveResolution(k,n);
    S := CohomologyRingQuotient(R);

    m := AssociativeArray();
    f := AssociativeArray();

    /*
    AooInfo := recformat< A : AlgBas,
			  k : ModAlgBas,
			  i : RngIntElt,
			  R : Rec,
			  S : Rng,
			  P : ModCpx,
			  m : AssocArr,
                          f : AssocArr
    >;

    Aoo := rec<AooInfo|
	A:=A,
	k:=k,
	i:=i,
	R:=R,
	S:=S,
	P:=P,
	m:=m,
	f:=f>;
    */

    Aoo := New(AInfinity);
    Aoo`A:=A;
    Aoo`k:=k;
    Aoo`i:=i;
    Aoo`R:=R;
    Aoo`S:=S;
    Aoo`P:=P;
    Aoo`m:=m;
    Aoo`f:=f;

    return Aoo;    
end intrinsic;

intrinsic MasseyProduct(Aoo :: AInfinity,
    terms :: SeqEnum[RngElt]) -> RngElt
    { Calculates a Massey product of the given cohomology elements, or
    if no Massey product exists, calculates an A-infinity higher product
    in its place. }
    return HighProduct(Aoo,terms);
end intrinsic;


intrinsic HighProduct(Aoo :: AInfinity,
    terms :: SeqEnum[RngElt]) -> RngElt
    { Calculates the Aoo product of the elements in terms. }

    if IsDefined(Aoo`m,terms) then
	return Aoo`m[terms];
    end if;
    
    n := #terms;
    R := Aoo`R;

    if n eq 0 then
	return Aoo`S!0;
    end if;

    if n eq 1 then
	return Aoo`S!0;
    end if;

    if exists(i){ i : i in [1..n] | terms[i] eq 0 } then
	return Aoo`S!0;
    end if;

    if exists(i){ i : i in [1..n] | terms[i] eq 1 } then
	return Aoo`S!0;
    end if;
    
    mapDeg := &+ [ WeightedDegree(x) : x in terms ] + 2 - n;

    require mapDeg le R`NumberOfSteps: "Too short resolution, need",mapDeg;
    
    ZeroMap := ChainMap(
	[* AHom(Term(Aoo`P,i),Term(Aoo`P,i-mapDeg))!0
	   : i in Reverse([mapDeg..Degrees(Aoo`P)]) *],
	Aoo`P,
	Aoo`P,
	-mapDeg);

    Fs := [* ZeroMap *];

    u := Field(VectorSpace(Term(Aoo`P,mapDeg)))!(-1);

    for i in [1..n-1] do
	ts := Partition(terms,[i,n-i]);
        sgn := u^(#ts[1]+(#ts[2]-1)*(&+ Append([WeightedDegree(t):t in ts[1]],0)));
	fi := HighMap(Aoo,ts[1]);
	fj := HighMap(Aoo,ts[2]);
	if not IsZero(fi*fj) then
	    Append(~Fs,sgn*fi*fj);
	end if;
    end for;

    for j in [2..n-1] do
        for k in [0..n-j] do
	    s := terms[1..k];
	    sgn := u^(k+j*(n-k-j+(&+ Append([WeightedDegree(t) : t in s],0))));
	    fk := HighProduct(Aoo,terms[k+1..k+j]);
	    if not fk eq Aoo`S!0 then
		Append(~s,fk);
		s := s cat terms[j+k+1..n];

		Append(~Fs,sgn*HighMap(Aoo,s));
	    end if;
	end for;
    end for;

    F := u*&+ [ f : f in Fs ];
    
    m := ChainmapToCohomology(F,Aoo`R);
    if m eq 0 then
	ff := u*F;
    else
	ff := u*F + CohomologyToChainmap(m,Aoo`R,Aoo`P);
    end if;

    if IsZero(ff) then
	md := mapDeg-1;
	f := ChainMap(
	[* AHom(Term(Aoo`P,i),Term(Aoo`P,i-md))!0
	   : i in Reverse([md..Degrees(Aoo`P)]) *],
	Aoo`P,
	Aoo`P,
	-md);
    else
	f := NullHomotopy(ff);
    end if;
        
    Aoo`m[terms] := m;
    Aoo`f[terms] := f;

    return m;
end intrinsic;

intrinsic HighMap(Aoo :: AInfinity,
    terms :: SeqEnum[RngElt]) -> MapChn
    { Calculates the corresponding Aoo-quasiisomorphism evaluated at
    the elements in terms. }

    if IsDefined(Aoo`f,terms) then
	return Aoo`f[terms];
    end if;

    n := #terms;
    
    mapDeg := &+ [ WeightedDegree(x) : x in terms ] + 2 - n;

    ZeroMap := ChainMap(
	[* AHom(Term(Aoo`P,i),Term(Aoo`P,i-mapDeg))!0
	   : i in Reverse([mapDeg..Degrees(Aoo`P)]) *],
	Aoo`P,
	Aoo`P,
	-mapDeg);

    if n eq 0 then
	return ZeroMap;
    end if;

    if n eq 1 then
	return CohomologyToChainmap(terms[1],Aoo`R,Aoo`P);
    end if;

    if exists(i){ i : i in [1..n] | terms[i] eq 0 } then
	return ZeroMap;
    end if;

    if exists(i){ i : i in [1..n] | terms[i] eq 1 } then
	return ZeroMap;
    end if;

    m := HighProduct(Aoo,terms);
    return Aoo`f[terms];
end intrinsic;
