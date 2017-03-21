freeze;

/////////////////////////////////////////////////////////////////////////////
//
// Some attributes...
//
// The attribute UEADescription is not really useful for anyone, but the 
// subsequent programs; however, we want to use the attribute mechanism 
// to store the data that it computes.

declare attributes AlgLie: ChevalleyBasis, RootDatum, UEADescription,
  IsReductive, IsSemisimple;

intrinsic IsSemisimple( L::AlgLie ) -> BoolElt
{True iff L is a semisimple Lie algebra}
    if not assigned L`IsSemisimple then
      L`IsSemisimple := SolubleRadical(L) eq sub<L|>;
    end if;
    return L`IsSemisimple;
end intrinsic;

intrinsic IsReductive( L::AlgLie ) -> BoolElt
{True iff L is a reductive Lie algebra}
	if not assigned L`IsReductive then
		F := CoefficientRing(L);
		if Characteristic(F) notin {2,3} then
			L`IsReductive := IsSemisimple( L / Centre(L) );
		else
			try
				_ := ReductiveType(L);
				L`IsReductive := true;
			catch err
				L`IsReductive := false;
			end try;
		end if;
	end if;
	return L`IsReductive;
end intrinsic;

intrinsic SemisimpleRank( L::AlgLie ) -> RngIntElt
{The semisimple rank of L}
    require IsReductive( L ) : "The Lie algebra must be reductive";
    if assigned L`RootDatum then
      return Rank( L`RootDatum );
    else
      return Dimension( CartanSubalgebra(L*L) );
    end if;
end intrinsic;

intrinsic ReductiveRank( L::AlgLie : Check := true ) -> RngIntElt
{The reductive rank of L. Set Check to false to skip the check for reductiveness of L. }
	require (not Check) or IsReductive( L ) : "The Lie algebra must be reductive";

	if assigned L`RootDatum then
		return Dimension( L`RootDatum );
	else
		C := CartanSubalgebra(L);
		if Characteristic(BaseRing(L)) ne 2 then
			return Dimension(C);
		else
			return Dimension(Centraliser(L, C));
		end if;
	end if;
end intrinsic;




/////////////////////////////////////////////////////////////////////////////

CartanMatrixToPositiveRoots:= function( C )
        
    rank:= NumberOfRows( C );
       
    // `posr' will be a list of the positive roots. We start with the
    // simple roots, which are simply unit vectors.
       
    V:= VectorSpace( RationalField(), rank );
    posr:= [ ];
    for i in [1..rank] do
      r:= Vector( RationalField(), [ 0 : i in [1..rank] ] );
      r[i]:= 1;
      posr:= Append( posr, r );
    end for;   
       
    ind:= 1;
    len:= rank;
    while ind le len do
           
    // We loop over those elements of `posR' that have been found in
    // the previous round, i.e., those at positions ranging from
    // `ind' to `le'.
         
      len := #posr;
      for i in [ind..len] do
        a:= posr[i];
           
        // We determine whether a+ej is a root (where ej is the j-th
        // simple root.
        for j in [1..rank] do
          ej:= posr[j];
             
          // We determine the maximum number `r' such that a-r*ej is
          // a root.
          r:= -1;
          b:= a;
          while b in posr do
            b:= b-ej;
            r:=r+1;
          end while; 
          q:= r-InnerProduct( V!Transpose( C )[j], V!a );
          if q gt 0 and a+ej notin posr then 
            posr:= Append( posr, a+ej );
          end if;
        end for;
      end for;
      ind:= len+1;
      len:= #posr;
    end while; 
      
    return posr;
end function;

SetEntrySCTable:=procedure(~T, i, j, k, cf, n )

    ind1:=(i-1)*n^2+(j-1)*n+k;
    ind2:=(j-1)*n^2+(i-1)*n+k;
    T[ind1]:= cf; T[ind2]:= -cf;

end procedure;

