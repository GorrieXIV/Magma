freeze;

good_ring := func<K | Type(K) in {FldFin, RngInt, FldRat, FldCyc}>;
good_ring := func<K | Type(K) in {FldFin, FldRat, FldCyc}>;
FIELD_MSG := "Field must be finite, rational, or cyclotomic";

import "min_field.m" : WriteOverSmallerField;

/*******************************************************************************
			Main irreducible modules
*******************************************************************************/

intrinsic IrreducibleModules(
    G::Grp, K::Fld:
	Alg := "Default",
	MaxDegree := 0,
	UseInduction := true,
        Characters := {},
        CharacterDegrees := {},
	PermDegreeLimit := -1
) -> .
{Determine the irreducible G-modules over the field K.}

    require IsFinite(G): "Group is not finite";
    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"}:
	"Unknown algorithm specified";

    //=====================================================================================
    // Characteristic p fields

    if Type(K) eq FldFin then

        /* Derek Holt: Check whether modules already stored. */ 
       if assigned G`modrepinfo then 

          for entry in G`modrepinfo do
            if assigned entry`field and entry`field cmpeq K then
               //information has already been computed
               return entry`irreds;
            end if;
          end for;
       else G`modrepinfo := [* *];
       end if;

       /* Modules have to be computed */

          //-------------------------
          if Type(G) eq GrpPerm then
              if IsSoluble(G) and Alg eq "Schur" then
	         P, f := PCGroup(G);
	         return LiftModules(IrreducibleModules(P, K), f);
              else
                 return IrreducibleModulesBurnside(G, K);
              end if;

          //-------------------------
          elif Type(G) eq GrpMat then
              if IsSoluble(G) and Alg eq "Schur" then
	         P, f := PCGroup(G);
	         return LiftModules(IrreducibleModules(P, K), f);
              else
                 return IrreducibleModulesBurnside(G, K);
	         // error "Irreducible G-modules are not available for non-soluble matrix groups";
              end if;
               
          //-------------------------
          elif Type(G) eq GrpPC then
	    if Alg eq "Burnside" then
	        return IrreducibleModulesBurnside(G, K);
	    else
		AbsIrrs :=  AbsolutelyIrreducibleModulesSchur(G, K :
			MaxDimension := MaxDegree);

		  ModuleIndex := function(Mods, T)
			K := Field(T);
		    for i := 1 to #Mods do
			M := Mods[i];
			if #K eq #Field(M) and IsIsomorphic(M, T) then
			    return i;
			end if;
		    end for;
		    return 0;
		  end function;

		    ModulesSortCmp := function(M, N)

			/* Comparison routine for sorting final output */

			r := Dimension(M) - Dimension(N);
			if r ne 0 then 
			    return r; 
			else
			    return Degree(BaseRing(M)) - Degree(BaseRing(N));
			end if;
		    end function;



		  Irrs := [];
		  Cons := [];
		  for i := 1 to #AbsIrrs do
		     M := AbsIrrs[i];
		     N := AbsoluteModuleOverMinimalField(M, K);
		     if #Field(N) ne #K then
			 T := WriteOverSmallerField(N, K);
			 n := ModuleIndex(Irrs, T);
			 if n eq 0 then
			     Append(~Irrs, T);
			     Append(~Cons, [i]);
			 else
			     cons := Cons[n];
			     Append(~cons, i);
			     Cons[n] := cons;
			 end if;
		     else
			 Append(~Irrs, N);
			 Append(~Cons, [i]);
		     end if;
		  end for;

		  Sort(~Irrs, ModulesSortCmp, ~pi);

		  return Irrs, AbsIrrs, Cons;

	    end if;
               
          //-------------------------
          else
	    error "Irreducible G-modules are not available for this group type.";

       end if;              
             
   else

    //=====================================================================================
    // Characteristic 0 fields

    //-------------------------
    if Type(G) eq GrpPerm then

       if Type(K) in {RngInt, FldRat} and Alg eq "Default" then
      	   T, C := InternalIrreducibleIntegralModules(
   	   G: MaxDegree := MaxDegree, UseInduction := UseInduction,
   	   Characters := Characters, CharacterDegrees := CharacterDegrees,
   	   PermDegreeLimit := PermDegreeLimit
   	                                              );
   	   L := [];
	   for i := 1 to #T do
	       if IsDefined(T, i) then
	           L[i] := T[i, 1];
	        end if;
	   end for;
	   if Type(K) eq FldRat then
	        Q := RationalField();
	        LQ := [];
	        for i := 1 to #L do
	  	   if not IsDefined(L, i) then continue; end if;
		   M := L[i];
		   MQ := ChangeRing(M, Q);
		   procedure copy_attr(M, f, MQ)
		       if assigned M``f then
		           MQ``f := M``f;
		       end if;
		    end procedure;
		    MQ`IsIrreducible := true;
		    copy_attr(M, "SchurIndex", MQ);
		    copy_attr(M, "Character", MQ);
		    LQ[i] := MQ;
	        end for;
	        L := LQ;
	   end if;
	   return L, C;

          require Type(K) ne RngInt:
         	"Integer ring only allowed for default algorithm";
    
       elif IsSoluble(G) then

          P, f := PCGroup(G);
          return LiftModules(IrreducibleModules(P, K: Alg := Alg), f);

      else

         error "Irreducible G-modules are not available for matrix groups over this field.";

      end if;

        
    //-------------------------
    elif Type(G) eq GrpMat then

       if IsSoluble(G) then
           P, f := PCGroup(G);
	   return LiftModules(IrreducibleModules(P, K), f);
       else
           error "Irreducible G-modules are not available for non-soluble matrix groups";
      end if;
               

    //-------------------------
    elif Type(G) eq GrpPC then

       X := AbsolutelyIrreducibleModules(G, Rationals());
       X := [WriteGModuleOverExtensionOf(x, K) : x in X];
       X := [GModule(x, K) : x in X];
       return X;

    //-------------------------
    else

       error "Irreducible G-modules are not available for this group type.";

    end if;

  end if; // characteristic

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////

intrinsic OldIrreducibleModules(G::GrpPC, K::Fld : Alg := "Default") -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n   *** Error in parameter: Unknown algorithm specified.\n";

    if Characteristic(K) eq 0 then
      X := AbsolutelyIrreducibleModules(G, Rationals());
      if K cmpne Rationals() then
        X := [WriteGModuleOverExtensionOf(x, K) : x in X];
      end if;
      X := [GModule(x, K) : x in X];
      return X;
    end if;

    if Alg in { "Default", "Schur"} then
        return [ M : M in IrreducibleModulesSchur(G, K) ];
    else 
       if Type(K) eq FldFin then
	    return IrreducibleModulesBurnside(G, K);
       else
            error "\n   At present the Burnside algorithm is available only for finite fields\n";
       end if;
    end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic OldIrreducibleModules(G::GrpPerm, K::Fld : Alg := "Default") -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n   *** Error in parameter: Unknown algorithm specified.\n";

    if IsSoluble(G) then

        if Alg in { "Default", "Schur"} then
	    P, f := PCGroup(G);
            return LiftModules(IrreducibleModules(P, K:Alg := Alg), f);
        else 
            if Type(K) eq FldFin then
	        return IrreducibleModulesBurnside(G, K);
            else
                error "\n   At present the Burnside algorithm is available only for finite fields\n";
            end if;
        end if;

    else // G is non-soluble

        if Alg in { "Default", "Burnside"} then
             if Type(K) eq FldFin then
	         return IrreducibleModulesBurnside(G, K);
             else
                 error "\n   At present, in the case of non-soluble groups, irreducible modules may only be computed over finite fields.\n";
             end if;
        else
    	     error "\n   The Schur algorithm is not applicable to non-soluble groups.\n";
        end if;

   end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic OldIrreducibleModules(G::GrpMat, K::Fld : Alg := "Default") -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n   *** Error in parameter: Unknown algorithm specified.\n";

    if IsSoluble(G) then

        if Alg in { "Default", "Schur"} then
	    P, f := PCGroup(G);
            return LiftModules(IrreducibleModules(P, K:Alg := Alg), f);
        else 
            // Burnside specified
            if Type(K) eq FldFin then
	        return IrreducibleModulesBurnside(G, K);
            else
                error "\n   At present the Burnside algorithm is available only for finite fields\n";
            end if;
        end if;

    else // G is non-soluble

       error "\n   In the case of non-soluble matrix groups, the function is currently not implemented.\n";

    end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic AbsolutelyIrreducibleModules(G::GrpPC, K::Fld : Alg := "Default", Raw := false) -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n    Error in parameter: Unknown algorithm specified.\n";

    if Type(K) eq FldFin then
 /* Derek Holt: check if modules already stored. */ 
       if not assigned G`modrepinfo then G`modrepinfo := [* *]; end if;
       for entry in G`modrepinfo do
            if assigned entry`field and entry`field cmpeq K then
               //information has already been computed
               return entry`absirreds;
            end if;
       end for;
    end if;

    if Alg eq "Schur" or (Alg eq "Default" and Type(K) ne FldFin) then
        if Type(K) in {FldRat, FldCyc, FldFin} then
          X := func<|[ M : M in AbsolutelyIrreducibleModulesSchur(G, K) ]>();
          if Raw then
            return X;
          end if;
          if Type(K) in {FldRat, FldCyc} then
            X := func<|[ InternalAbsoluteModuleOverMinimalField(x)[1] : x in X]>();
          end if;
        elif ISA(Type(K), FldAlg) then
          X := func<|[ M : M in AbsolutelyIrreducibleModules(G, Rationals():Alg := Alg) ]>();
          X := [WriteGModuleOverExtensionOf(x, K) : x in X];
	else
	    error "Unable to compute modules over given field";
        end if;
        return X;
    elif  Alg eq "Burnside" or (Alg eq "Default" and Type(K) eq FldFin) then
       if Type(K) eq FldFin then
	    return AbsolutelyIrreducibleModulesBurnside(G, K);
       else
            error "\n   At present the Burnside algorithm is available only for finite fields\n";
       end if;
    else
	error "Unable to compute modules over given field";
    end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic AbsolutelyIrreducibleModules(G::GrpPerm, K::Fld : Alg := "Default") -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n   *** Error in parameter: Unknown algorithm specified.\n";

    if Type(K) eq FldFin then
 /* Derek Holt: check if modules already stored. */ 
       if not assigned G`modrepinfo then G`modrepinfo := [* *]; end if;
       for entry in G`modrepinfo do
            if assigned entry`field and entry`field cmpeq K then
               //information has already been computed
               return entry`absirreds;
            end if;
       end for;
    end if;

    if IsSoluble(G) then

        if Alg eq "Schur" or (Alg eq "Default" and Type(K) ne FldFin) then
	    P, f := PCGroup(G);
            return LiftModules(AbsolutelyIrreducibleModules(P, K:Alg := "Schur"), f);
        else 
            // Use Burnside 
            if Type(K) eq FldFin then
	        return AbsolutelyIrreducibleModulesBurnside(G, K);
            else
                error "\n   At present the Burnside algorithm is available only for finite fields\n";
            end if;

        end if;

    else // G is non-soluble

        if Alg in { "Default", "Burnside"} then
             if Type(K) eq FldFin then
	         return AbsolutelyIrreducibleModulesBurnside(G, K);
             else
                 error "\n   At present, in the case of non-soluble groups, irreducible modules may only be computed over finite fields.\n";
             end if;
        else
    	     error "\n   The Schur algorithm is not applicable to non-soluble groups.\n";
        end if;

   end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic AbsolutelyIrreducibleModules(G::GrpMat, K::Fld : Alg := "Default") -> .
{Determine the irreducible G-modules over the field K. The algorithm employed 
may be specified by means of the parameter Alg}

    require good_ring(K): FIELD_MSG;
    require Alg in { "Default", "Burnside", "Schur"} : "\n   *** Error in parameter: Unknown algorithm specified.\n";

    if Type(K) eq FldFin then
 /* Derek Holt: check if modules already stored. */ 
       if not assigned G`modrepinfo then G`modrepinfo := [* *]; end if;
       for entry in G`modrepinfo do
            if assigned entry`field and entry`field cmpeq K then
               //information has already been computed
               return entry`absirreds;
            end if;
       end for;
    end if;

    if IsSoluble(G) then

        if Alg eq "Schur" or (Alg eq "Default" and Type(K) ne FldFin) then
	    P, f := PCGroup(G);
            return LiftModules(AbsolutelyIrreducibleModules(P, K:Alg := "Schur"), f);
        else 
            // Use Burnside 
            if Type(K) eq FldFin then
	        return AbsolutelyIrreducibleModulesBurnside(G, K);
            else
                error "\n   At present the Burnside algorithm is available only for finite fields\n";
            end if;

        end if;

    else // G is non-soluble

        if Alg in { "Default", "Burnside"} then
             if Type(K) eq FldFin then
	         return AbsolutelyIrreducibleModulesBurnside(G, K);
             else
                 error "\n   At present, in the case of non-soluble groups, irreducible modules may only be computed over finite fields.\n";
             end if;
        else
    	     error "\n   The Schur algorithm is not applicable to non-soluble groups.\n";
        end if;

   end if;

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////////

intrinsic CanChangeRing(M::Mtrx, P::RngOrdIdl) -> BoolElt, ModGrp
{Tries to map the matrix into the residue class field of P.}
  F, mF := ResidueClassField(P);
  t := [];
  R := Order(P);
  for xx in Eltseq(M) do
    if not xx in R and Valuation(xx, P) lt 0 then
      return false, _;
    end if;
    Append(~t, xx @mF);
  end for;
  return true, Matrix(Nrows(M), Ncols(M), t);
end intrinsic;


intrinsic CanChangeRing(M::ModGrp, P::RngOrdIdl) -> BoolElt, ModGrp
{Tries to map the GModule into the residue class field of P. The module is NOT conjugated to ensure this is going to work.}
  F, mF := ResidueClassField(P);
  A := ActionGenerators(M);
  n := Ncols(A[1]);
  a := [GL(n, F)|];
  for x in A do
    t := [];
    for xx in Eltseq(x) do
      if Valuation(xx, P) lt 0 then
        return false, _;
      end if;
      Append(~t, xx @mF);
    end for;
    Append(~a, t);
  end for;
  return true, GModule(a);
end intrinsic;

intrinsic CanChangeRing(M::ModGrp, R::Rng) -> BoolElt, ModGrp
{Tries to change the coefficient ring of M to be R. The module is NOT conjugated to ensure this is going to work.}
  A := ActionGenerators(M);
  n := Dimension(M);
  a := [MatrixRing(R, n) | ];
  for x in A do
    fl, m := CanChangeRing(x, R);
    if not fl then
      return false, _;
    end if;
    Append(~a, m);
  end for;
  R := GModule(Group(M), a: Check := false);
  if assigned M`Character then
    R`Character := M`Character;
  end if;
  return true, R;
end intrinsic;

intrinsic ChangeRing(M::ModGrp, m::Map) -> BoolElt, ModGrp
{Tries to change the coefficient ring through the use of the map m. The module is NOT conjugated to ensure this is going to work.}
  A := ActionGenerators(M);
  n := Ncols(A[1]);
  a := [];
  for x in A do
    Append(~a, Matrix(Nrows(x), Ncols(x), [m(y) : y in Eltseq(x)]));
  end for;
  R := GModule(Group(M), a:Check := false);
  if assigned M`Character then
    R`Character := M`Character;
  end if;
  return R;
end intrinsic;

intrinsic ChangeRing(M::ModGrp, P::RngOrdIdl) -> ModGrp
{Tries to change the coefficient ring of M to be the residue class field of P}
  f, m := CanChangeRing(M, P);
  require f : "Cannot change the ring, bad denominators";
  return m;
end intrinsic;

intrinsic ChangeRing(M::Mtrx, P::RngOrdIdl) -> Mtrx
{Tries to change the coefficient ring of M to be the residue class field of P}
  f, m := CanChangeRing(M, P);
  require f : "Cannot change the ring, bad denominators";
  return m;
end intrinsic;

intrinsic ChangeRing(M::ModGrp, R::Rng) -> ModGrp
{Tries to change the coefficient ring of M to be R.}
  f, m := CanChangeRing(M, R);
  require f : "Cannot change the ring";
  return m;
end intrinsic;

intrinsic InternalpIntegralModule(L::[Mtrx], S::[RngOrdIdl]) -> .
  {}

  K := Parent(L[1][1][1]);
  n := Ncols(L[1]);
  q,w,M := InternalMakeIntegral(L);
  res := [];
  bM := PseudoBasis(M);
  I := [x[1] : x in bM];
  for p in S do
     lv := [Valuation(i, p) : i in I];
     if forall{i : i in lv | i eq 0} then
       Append(~res, IdentityMatrix(K, n));
     end if;
     x, pi := TwoElementNormal(p);
     assert x eq Minimum(p);
     T := DiagonalMatrix(K, [pi^i : i in lv]);
     Append(~res, T);
  end for;
  return q, w, res;
end intrinsic;

intrinsic InternalSIntegralModule(L::[Mtrx], S::[RngOrdIdl]) -> .
  {}
  K := Parent(L[1][1][1]);
  n := Ncols(L[1]);
  q,w,M := InternalMakeIntegral(L);
  res := [];
  bM := PseudoBasis(M);
  I := [x[1] : x in bM];
  if #S eq 0 then
    res := [K|1 : i in I];
  else
    for i in I do
      Append(~res, WeakApproximation(S, [Valuation(i, p) : p in S]));
    end for;
  end if;
  return q, w, DiagonalMatrix(K, res);
end intrinsic;


intrinsic Evaluate(M::Mtrx[FldAlg[FldRat]], p::PlcNumElt) -> Mtrx
  {Evaluates all matrix entries at p}
  return Matrix(Nrows(M), Ncols(M), [Evaluate(x, p) : x in Eltseq(M)]);
end intrinsic;

intrinsic Evaluate(M::Mtrx[FldAlg[FldRat]], p::RngOrdIdl) -> Mtrx
  {Evaluates all matrix entries at p}
  return ChangeRing(M, p);
end intrinsic;

intrinsic pIntegralGModule(M::ModGrp, p::RngOrdIdl) -> ModGrp, Mtrx
  {Given a G-module M over a number field and a prime ideal of that field, return an equivalent module that is p-integral and the transformation matrix}
  L := ActionGenerators(M);
  q,w,e := InternalpIntegralModule(L, [p]);
  q := e[1]*q;
  w := w*e[1]^-1;
  L := [q*x*w : x in L];
  return GModule(Group(M), L), q;
end intrinsic;

intrinsic pIntegralGModule(M::ModGrp, S::[RngOrdIdl]) -> ModGrp, Mtrx
  {Given a G-module M over a number field and a list of prime ideals of that field, return an equivalent module that is p-integral and the transformation matrix}
  L := ActionGenerators(M);
  q,w,e := InternalSIntegralModule(L, S);
  q := e*q;
  w := w*e^-1;
  L := [q*x*w : x in L];
  return GModule(Group(M), L), q;
end intrinsic;

intrinsic InvariantModule(M::ModGrp) -> PMat, Mtrx, Mtrx
  {Given a G-module M over a number field find a Dedekind module (a PMat) that M acts on}
  if assigned M`PMat then
    return M, i, i where i := 
              IdentityMatrix(K, n) where n, K := BasicParameters(M);
    return M`PMat;
  end if;
  L := ActionGenerators(M);
  q,w,m := InternalMakeIntegral(L);

  pm := PseudoMatrix(m:Generators);
  c := CoefficientIdeals(pm);
  d := [];
  for i in [1..#c] do
    fl, g := ClassRepresentative(c[i]);
    Append(~d, g);
    c[i] := fl;
  end for;
  d := DiagonalMatrix(d);
  q := d*q;
  w := w*d^-1;
  P := PseudoMatrix(c, Matrix(pm));
  M`PMat := P;
  return M`PMat, q, w;
end intrinsic;

declare attributes ModGrp: PMat, InvForm;

intrinsic AlmostIntegralGModule(M::ModGrp) -> ModGrp, Mtrx, Mtrx
  {Given a G-module M over a number field find a Dedekind module (a PMat) that M acts on and return this action}
  if assigned M`PMat then
    return M, i, i where i := 
              IdentityMatrix(K, n) where n, K := BasicParameters(M);
  end if;
  L := ActionGenerators(M);
  q,w,m := InternalMakeIntegral(L);

  pm := PseudoMatrix(m:Generators);
  c := CoefficientIdeals(pm);
  d := [];
  for i in [1..#c] do
    fl, g := ClassRepresentative(c[i]);
    Append(~d, g);
    c[i] := fl;
  end for;
  d := DiagonalMatrix(d);
  q := d*q;
  w := w*d^-1;
  L := [q*x*w : x in L];
  N := GModule(Group(M), L);
  if  assigned M`Character then
    N`Character := M`Character;
  end if;
  N`PMat := PseudoMatrix(c, Matrix(pm));
  return N, q, w;
end intrinsic;

intrinsic CanMakeIntegralGModule(M::ModGrp:UseSteinitz := false) -> BoolElt, ModGrp, Mtrx, Mtrx
  {Try to make the GModule (the underlying rep.) integral. Will always succeed if the field has class number 1.}

    
  L := ActionGenerators(M);
  q,w,m := InternalMakeIntegral(L:St := UseSteinitz);

  pm := PseudoMatrix(m:Generators);
  c := CoefficientIdeals(pm);
  d := [];
  for i in c do
    fl, g := IsPrincipal(i);
    if not fl then
      return false, _, _;
    end if;
    Append(~d, g);
  end for;
  d := DiagonalMatrix(d);
  q := d*q;
  w := w*d^-1;
  L := [q*x*w : x in L];

  N := GModule(Group(M), L);
  if  assigned M`Character then
    N`Character := M`Character;
  end if;
  N`PMat := PseudoMatrix(c, Matrix(pm));

  return true, N, q, w;
end intrinsic;

intrinsic ModuleToZModule(P::PMat) -> Mtrx
  {Given a PMat, representing a module over some maximal order, return the isomorphic Z-module}

  I := CoefficientIdeals(P);
  a := Matrix(P);
  l := [];
  for i in [1..#I] do
    e := a[i];
    B := Basis(I[i]);
    for b in B do
      f := e*b;
      Append(~l, &cat [Eltseq(x) : x in Eltseq(f)]);
    end for;
  end for;
  return Matrix(l);
end intrinsic;

intrinsic GModule(M::ModGrp, Q::FldAlg) -> ModGrp
  {For a GModule over some number field, return an isomorphic Q represenation where Q is a subfield}

  if Type(CoefficientRing(M)) cmpeq Q then
    return M;
  end if;

  require ISA(Type(CoefficientRing(M)), FldAlg):
    "representation must be defined over a number field";

  require IsSubfield(Q, CoefficientRing(M)):
    "field must be a subfield of the coefficient ring of the module";

  _, m := Algebra(CoefficientRing(M), Q);
  L := ActionGenerators(M);
  g := [];
  n := Nrows(L[1]);
  for X in L do
    Append(~g, VerticalJoin([
      HorizontalJoin([RepresentationMatrix((X[i][j]) @ m) : j in [1..n]])
        : i in [1..n]]));
  end for;

  return GModule(Group(M), g);
end intrinsic;
 
intrinsic GModule(M::ModGrp, Q::FldRat) -> ModGrp
  {"} // "

  if Type(CoefficientRing(M)) eq FldRat then
    return M;
  elif Type(CoefficientRing(M)) eq RngInt then
    return GModule(Group(M), [Matrix(Rationals(), x) : x in ActionGenerators(M)]);
  end if;

  require ISA(Type(CoefficientRing(M)), FldAlg) :
    "Representation must be over a number field or Q";

  L := ActionGenerators(M);
  g := [];
  n := Nrows(L[1]);
  for X in L do
    Append(~g, VerticalJoin([
      HorizontalJoin([AbsoluteRepresentationMatrix(X[i][j]) : j in [1..n]])
        : i in [1..n]]));
  end for;

  return GModule(Group(M), g);
end intrinsic;
         

intrinsic GModule(M::ModGrp, R::RngInt) -> ModGrp
  {For a GModule over some number field, return an isomorphic Z-representation.}

  L := ActionGenerators(M);
  if Type(CoefficientRing(M)) eq RngInt then
    return M;
  elif Type(CoefficientRing(M)) eq FldRat then
    return IntegralModule(M);
  end if;

  require ISA(Type(CoefficientRing(M)), FldAlg) :
    "Representation must be over a number field or Q";

  q,w,Mo := InternalMakeIntegral(L);

  I := PseudoGenerators(Mo);
  B := [];
  for i in I do
    for b in Basis(i[1]) do
      Append(~B, i[2]*b);
    end for;
  end for;
  L := [q*x*w : x in L];
  g := [];
  S := LatticeWithBasis(Matrix([ &cat [Eltseq(x) : x in Eltseq(y)] : y in B]));
  for X in L do
    Y := [];
    for b in B do
      c := Matrix(CoefficientRing(X), b)*X;
      c := Matrix(CoefficientRing(b), c);
      c := &cat [Eltseq(x) : x in Eltseq(c)];
      Append(~Y, Eltseq(Coordinates(S!c)));
    end for;
    Append(~g, Matrix(Y));
  end for;
  return GModule(Group(M), g);
end intrinsic;


intrinsic Evaluate(M::ModGrp, p::RngOrdIdl) -> ModGrp
  {Returns an equivalent module defined over the residue class field of p.}
  
  L := ActionGenerators(M);
  q,w,e := InternalpIntegralModule(L, [p]);
  q := e[1]*q;
  w := w*e[1]^-1;
  L := [q*x*w : x in L];
  return GModule(Group(M), [Evaluate(x, p) : x in L]);
end intrinsic;

intrinsic Evaluate(M::ModGrp, S::[RngOrdIdl]) -> []
  {For each p in S, this functions returns an equivalent module defined over the residue class field at p.}
  
  L := ActionGenerators(M);
  q,w,e := InternalpIntegralModule(L, S);
  res := [];
  for i in [1..#S] do
    LL := [e[i]*q*x*w*e[i]^-1 : x in L];
    Append(~res, GModule(Group(M), [Evaluate(x, S[i]) : x in LL]));
  end for;
  return res;
end intrinsic;
