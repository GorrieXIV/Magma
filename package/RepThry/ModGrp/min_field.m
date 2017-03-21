freeze;
 

forward IsRealisableOverSubfield, ProcessSubfields, WriteOverSmallerField;

/////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteModuleOverMinimalField (M::ModGrp, F::FldFin) -> ModGrp
{Write the absolutely irreducible module M over the smallest possible 
field containing F, without increasing the dimension of the module}

      // First write the module over the smallest possible field K
 
      N := M;
      if Degree(Field(N)) gt 1 then 
           Min_K := MinimalField(N);
           if #Min_K lt #Field(N) then
                N := ChangeRing(N, Min_K);
           end if;
           yes, N1 := IsRealisableOverSmallerField(N);
           if yes then 
                N :=  N1; 
           end if;
      end if;

      // Now write the module over the smallest field L that contains
      // both F and K
 
      K := BaseRing(N);
      k := Degree(K);
      f := Degree(F);
      l := LCM(k, f);
      if l gt k then 
         L := ext< F | l div f >;
         N := ChangeRing(N, L);
      end if;

      return N;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteModuleOverMinimalField (M::ModGrp: Character := false) -> ModGrp
{Write the absolutely irreducible module M over the smallest possible 
field without increasing the dimension of the module}

      // First write the module over the smallest possible field K
 
      if Characteristic(Field(M)) eq 0 then
        return InternalAbsoluteModuleOverMinimalField(M : FindSmallest, Char := Character)[1];
      end if;

      N := M;
      if Degree(Field(N)) gt 1 then 
           Min_K := MinimalField(N);
           if #Min_K lt #Field(N) then
                N := ChangeRing(N, Min_K);
           end if;
           yes, N1 := IsRealisableOverSmallerField(N);
           if yes then 
                N :=  N1; 
           end if;
      end if;

      return N;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic AbsoluteModulesOverMinimalField (Q::SeqEnum, F::FldFin) -> SeqEnum
{Write the sequence Q of modules over the smallest possible field 
containing F, without increasing the dimension of the module}

      return [ AbsoluteModuleOverMinimalField(M, F) : M in Q ];

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic ModuleOverSmallerField (M::ModGrp, F::FldFin) -> ModGrp
{Write the module M over the field F}

      // First write the module over the smallest possible field K
 
      N := M;
      N := AbsoluteModuleOverMinimalField(N, F);

      // If the base field of M strictly contains F, write M over F by
      // blowing up the dimension of M
 
      if #Field(N) ne #F then
         N := WriteOverSmallerField(N, F);
      end if;

      return N;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic ModulesOverSmallerField (Q::SeqEnum, F::FldFin) -> SeqEnum
{Write the sequence Q of modules over the smallest possible field without
increasing the dimension of the module}

      return [ ModuleOverSmallerField(M, F) : M in Q ];

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic AbsolutelyIrreducibleConstituents(M::ModGrp) -> SeqEnum
{Given an irreducible module M, return M if it is already
absolutely irreducible, else return the absolutely irreducible
modules obtained by rewriting M in smaller degree after extending 
the base field of M to a splitting field}

        require IsIrreducible(M) : "Module is not irreducible.";

             yes, mx, deg := IsAbsolutelyIrreducible(M);
             if yes then
                 return [ M ];
             else
                F := BaseRing(M);
                M1 := ChangeRing( M, ext< F | deg >);
                return Constituents(M1); 
            end if;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////

intrinsic ModulesOverCommonField( M::ModGrp, N::ModGrp ) -> ModGrp, ModGrp
{Given A-modules M and N, change their base fields to F, where F is the 
smallest overfield containg the base fields of M and N}


         FldM := BaseRing(M);
         FldN := BaseRing(N);
         K := PrimeField(FldM);
         d1 := Degree(FldM);
         d2 := Degree(FldN);
         d := LCM(d1, d2);

         if d1 ne d then 
              M1 := ChangeRing(M, ext<Field(M) | d div d1>); 
         else
              M1 := M;
         end if;

         if d2 ne d then 
              N1 := ChangeRing(N, ext<Field(N) | d div d2>); 
         else
              N1 := N;
         end if;

         return M1, N1;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

intrinsic CommonOverfield( K::FldFin, L::FldFin ) -> FldFin
{Given finite fields K and L, both of characteristic p, return 
the smallest field which contains both of them} 

	 if K cmpeq L then
	    return K;
	 end if;

	 l, C := ExistsCoveringStructure(K, L);
	 require l: "No covering field exists";

	 if K subset L then
	    return L;
	 end if;
	 if L subset K then
	    return K;
	 end if;
	 S := sub<C | K.1, L.1>;
	 return S;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////
/*
intrinsic ConstituentsOverMinimalField ( M::ModGrp ) -> []
{Given a module M, return the irreducible constituients of M,
each written over the smallest field in which it can be realised}

     return [ WriteOverMinimalField(N) : N in Constituents(M) ];

end intrinsic;
*/
///////////////////////////////////////////////////////////////////////////////

intrinsic IsRealisableOverSmallerField (M:: ModGrp) -> BoolElt, ModGrp
{Determine whether M be realised over a proper subfield of its
base field.  If so, return true and the equivalent module.} 
 
     G := Group(M);
     K := Field(M);
     N := M;
     e := Degree (K);
     divse := Set (Exclude (Divisors (e), e));
     ProcessSubfields (~N, ~divse);
  
     // Weak test for correctness -- to be removed
     L := MinimalField(M);
     if #L ne #BaseRing(N) and #L lt #BaseRing(N) then 
         "ERROR in IsRealisableOverSmallerField with", M:Magma; 
          L; BaseRing(N);
     end if;

     // Verbose
     // if Field(N) ne K then 
     //    "Field reduced for", M, "to produce", N;
     // end if;

    return Field(N) eq K select false else true, N; 

end intrinsic;


///////////////////////////////////////////////////////////////////////////////

intrinsic IsRealisableOverSubfield(M:: ModGrp, F::FldFin) -> BoolElt, ModGrp
{Determine whether M can be realised over the subfield F of its
base field K.  If so, return true and the equivalent module.} 
 
     K := BaseRing(M);
     if #K eq #F then
         return true, M;
     end if;
     p := Characteristic(K);
     d := Degree(F);
     e := Degree(K);
     assert (e mod d) eq 0;
     yes, N, X := IsRealisableOverSubfield(M, d);
     return yes, N, X; 

end intrinsic;


/////////////////////////////////////////////////////////////////////////////

/*
intrinsic WriteOverSmallerField(M::ModGrp, F::FldFin) -> ModGrp
{Given a module of dimension d over a finite field E having degree e
and a subfield F of E having degree f, write the action of M as
d*e/f by d*e/f matrices over F and return the module and the isomorphism};
*/

function WriteOverSmallerField(M, F)

    K := Field(M);
    assert Type(K) eq FldFin; // "Argument 1 is not over a finite field";
    assert PrimeField(K) eq PrimeField(F); // "Arguments are not compatible";

    d := Dimension(M);
    Act := ActionGenerators(M);
    A := MatrixRing(K, d);
    B, f := MatrixRing(A, F);

    N := GModule( Group(M), [ f(Act[i]) : i in [1 .. #Act] ]);
    return N;

end function;


///////////////////////////////////////////////////////////////////////////////
//
//  ZProduct 
//
function ZProduct (Alpha, Z, k)

   z := Z[1];
   ZAlpha := Z;
   for i := 1 to k-1 do
      ZAlpha := Alpha (ZAlpha);
      z *:= ZAlpha;
   end for;
   return z[1];

   /*
   z := Z[1];
   ZAlpha := Alpha (Z);
   count := 0;
   while count ne (k - 1) do
       z := z * ZAlpha;
       ZAlpha := Alpha (ZAlpha);
       count +:= 1;
   end while;
   return z[1];
   */

end function;

///////////////////////////////////////////////////////////////////////////////
//
//  FindX
//
function FindX (Alpha, Z, Y, k)

   X := Y;
   count := 0;
   while count ne (k - 1) do
      X := Y + Z * Alpha (X);
      count +:= 1;
   end while;

   return X;

end function;

///////////////////////////////////////////////////////////////////////////////

function IsRealisableOverSubfield(M, d)

/*
   Test whether the module M can be realised over a degree d extension
   of the prime field
*/

   K := BaseRing(M);
   p := Characteristic(K);
   m := Dimension(M);
   A := ActionGenerators(M);
   n := #A;
   R := MatrixAlgebra(K, m);
   G := Group(M);
   
   Alpha := func<A | FrobeniusImage(A, d)>;
   k := Degree(K) div d;

   mod1 := M;
   mod2 := GModule(G, [Alpha (A[i]) : i in [1..n]]);
   // "Time for IsIsomorphism";
   flag, Z := IsIsomorphic(mod1, mod2);
   if not flag then 
      return false, M; 
   end if;

   F := GF(p, d);
   // "Time for ZProduct";
   lambda := ZProduct(Alpha, Z, k);
   // "Time for NormEquation";
   yes, mu := NormEquation(K, F ! lambda);
   if not yes then "ERROR in solving norm equation", K, F, lambda; end if;
   // assert Norm (mu, F) eq lambda;

   Z := mu^(-1) * Z;
   S := MatrixAlgebra( F, m );
   repeat 
      Y := Random(R);
      // "Time for FindX";
      X := FindX(Alpha, Z, Y, k);
      if Determinant(X) ne 0 then
         // assert Z eq X * Alpha (X)^-1;
         Xinv := X^-1;
         return true, GModule( G, [ S | Xinv * A[i] * X : i in [1..n]]), X;
      end if;
   until 1 eq 0;

end function;


///////////////////////////////////////////////////////////////////////////////

procedure ProcessSubfields (~M, ~divse)

/* Can G be written over one of the subfields whose
   degree is listed in divse? if so, rewrite G */

   if divse eq {} then return; end if;

   repeat 
      d := Maximum (divse);
      yes, M := IsRealisableOverSubfield(M, d);
      if not yes then 
         divse diff:= Set (Divisors (d));
      else 
         divse := divse meet Set (Exclude (Divisors (d), d));
         $$ (~M, ~divse); 
         return;
      end if;
   until #divse eq 0;
         
end procedure;


///////////////////////////////////////////////////////////////////////////////

intrinsic ActionGenerators(M::ModRng) -> []
{Return the matrices giving the action on M as a sequence}

    return [ ActionGenerator(M, i) : i in [1..Nagens(M)] ];

end intrinsic;


///////////////////////////////////////////////////////////////////////////////

intrinsic ActionGroup(M::ModGrp) -> GrpMat
{The matrix group generated by the action generators of a G-module M}

    G := Group(M);
    ngens := Ngens(G);
    gens := [ ActionGenerator(M, i) : i in [1..Nagens(M)] ];
    assert Type(G) eq GrpPC or #gens eq ngens;
    deg := Degree(Universe(gens));
    R := BaseRing(Universe(gens));    
    if Type(G) eq GrpMat and Degree(G) eq deg and BaseRing(G) cmpeq R and
	forall{i:i in [1..ngens]|G.i eq gens[i]}
    then
	return G;
    end if;

    res := MatrixGroup<deg, R | gens>;
    return res;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
