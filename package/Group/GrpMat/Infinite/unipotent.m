freeze;

function Support(V, P)
    return sub<V | {v - v * p : v in Basis(V), p in Generators(P)}>;
end function;

function UnipotentFlag(P) 
    V := VectorSpace(P);
    supports := [];
    VP := V;
    repeat
	Append(~supports, VP);	
	VP := Support(VP, P);
    until Dimension(VP) eq 0;
    return supports;
end function;

intrinsic UnipotentBasis(P :: GrpMat) -> GrpMatElt
{P is a unipotent subgroup of GL(d, F), where F is an exact field.
 Return a change-of-basis matrix g in GL(d, F) such that P^g is upper unitriangular}

    F := BaseRing (P);
    error if not IsField (F) and IsExact (F), "Group must be defined over exact field";
    V := VectorSpace(P);

    supports := UnipotentFlag (P);
    
    basis := [];
    for i in Reverse([1 .. #supports]) do
	U := supports[i];
	W := sub<V | basis>;

	// Add basis elements from subspace
	for v in Basis(U) do
	    if v notin sub<V | W, basis> then
		Append(~basis, V ! v);
	    end if;
	end for;
    end for;

    Reverse (~basis);
    conj := Generic(P) ! Matrix(F, Degree(P), Degree(P), basis);
    return conj^(-1);
end intrinsic;

intrinsic IsUnipotent (G:: GrpMat) -> BoolElt, GrpMatElt 
{If matrix group G is unipotent, then return true, else false;
 if G is unipotent and defined over an exact field F, also return a 
 change-of-basis matrix c in GL(Degree (G), F) such that G^c is upper unitriangular}

    F := BaseRing (G);
    error if not IsExact(F), "Matrix group must be over an exact ring.";
    error if not HasEchelonForm(F), "Matrix group must be over a ring which allows computation of echelon forms.";
    if IsTrivial (G) then return true, Identity (G); end if;

    n := Degree (G);
    F := BaseRing (G);
    MA := MatrixAlgebra (F, n);

    U := Identity (MA);
    X := [(MA!G.i) - U : i in [1..Ngens (G)]];

    V := RSpace (F, n);
    U := V;
    repeat
        W := U;
        B := Basis (W);
        U := sub <V | [b * x: b in B, x in X]>;
    until Dimension (U) in {0, Dimension (W)};

    flag := Dimension (U) eq 0;
    if flag then 
       if IsField (F) then 
          return true, UnipotentBasis (G); 
       else 
          return true, _; 
       end if;
    else
       return false, _;
    end if;
end intrinsic;
