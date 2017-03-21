freeze;

//$Id:: tensor.m 2306 2012-05-31 01:59:25Z eobr007                         $:

ScalarMultiple := function (g, lambda)
   P := Parent (g);
   F := BaseRing (P);
   d := Degree (P);
   return lambda * MatrixAlgebra (F, d) ! g;
end function;

intrinsic ScaleMatrix(g :: Mtrx) -> BoolElt, Mtrx, FldFinElt 
{g is an invertible matrix. If a scalar multiple m of g has 
determinant 1, then return true, m, and the scalar, 
else return false.}

    det := Determinant(g); 
    require det ne 0: "Element must be invertible";

    if det eq 1 then return true, g, 1; end if;
    m := Nrows(g);

    flag, lambda := IsPower(det, m);
    if flag eq false then return false, _, _; end if;
    
    l := lambda^(-1);
    h := ScalarMultiple(g, l);
    return true, Generic (Parent (g)) ! h, l;
end intrinsic;

intrinsic TensorProduct(G :: GrpMat, H :: GrpMat) -> GrpMat
    { Construct the tensor product P <= GL(d * e, p^t) of the two matrix groups
    G <= GL(d, p^r) and H <= GL(e, p^s), where t = lcm(r, s).}

    FG := CoefficientRing(G);
    FH := CoefficientRing(H);
    
    require Characteristic(FG) eq Characteristic(FH) :
	"G and H must be over fields of the same characteristic";

    FF := CommonOverfield(FG, FH);
    GE := ExtendField(G, FF);
    HE := ExtendField(H, FF);

    return sub<GL(Degree(G) * Degree(H), FF) |
        [TensorProduct(GE.i, Id(H)) : i in [1..NumberOfGenerators(GE)]]
    cat [TensorProduct(Id(G), HE.j) : j in [1 ..NumberOfGenerators(HE)]]>;
end intrinsic;

intrinsic DecomposeKronecker(X :: Setq, blockSize :: RngIntElt) -> BoolElt, <>
{ Decide whether or not the collection of matrices X is composed
  of blocks size blockSize which differ only by scalars;
  if so, return true and the decomposition of each matrix, else false.
}

    require Category(Universe(X)) in {GrpMat, AlgMat} and #X gt 0 :
	"Argument 1 must be non-empty";
    
    F := CoefficientRing(Universe(X));
    d := Degree(Universe(X));
    flag, nBlocks := IsDivisibleBy(d, blockSize);
    if not flag then
	return false, _;
    end if;
    
    MB := MatrixAlgebra(F, blockSize);
    MS := MatrixAlgebra(F, nBlocks);
    decompositions := [* *];
    
    for g in X do
	components := [* *];
	scalars := [];
	
	for row in [1 .. nBlocks] do
	    for col in [1 .. nBlocks] do
		top  := (row - 1) * blockSize + 1;
		left := (col - 1) * blockSize + 1;
		
		block := Submatrix(g, top, left, blockSize, blockSize);
		if IsZero(block) then
		    Append(~scalars, F ! 0);
		else
		    normalised, scalar := Normalise(block);
		    
		    if #components eq 0 then
			Append(~components, MB ! normalised);
		    else
			if normalised ne components[1] then
			    return false, _;
			end if;
		    end if;
		    
		    Append(~scalars, scalar);
		end if;
	    end for;
	end for;

	// All blocks zero?
	if #components eq 0 then
	    return false, _;
	end if;
	Append(~components, MS ! scalars);
	assert KroneckerProduct(components[2], components[1]) eq g;
	
	Append(~decompositions, <x : x in Reverse(components)>);
    end for;

    return true, <x : x in decompositions>;
end intrinsic;

// This comes from Eamonn O'Brien
function ScaleFactor(G)
    /* G \leq GL(d, q) and for each generator g of G, \det(g) is a power of d.
    Return a scaled version of G, where each generators has been scaled to have
    determinant 1.

    Also returns true or false depending on whether or not any scaling was
    necessary.
    */
    local  K, m, new, U, scale, det, flag, lambda;
    
   K := BaseRing(G);
   m := Degree(G);
   new := [Identity(GL (m, K))];
   U := UserGenerators(G);
   scale := false;
   
   for i in [1 .. #U] do
       flag, g, det := ScaleMatrix(U[i]);
       error if not flag, "Error in ScaleFactor";
       
       new[i] := g;
       if det gt 1 then
	   scale := true;
       end if;  
   end for;
   
   if scale then
       S := sub<GL(m, K) | new>;
       S`UserGenerators := new;
       return S, true;
   else
      return G, false;
   end if;
end function;

// This comes from Eamonn O'Brien
function ScaledTensorFactors(G, b) 
    /* G \leq GL(d, q) is a tensor product of two matrix groups of degrees n
    and d/n, b[1] is TensorBasis(G) and b[2] is n or d/n.
    Return the tensor factors of G, scaled so that both are contained in
    SL(n, q) and SL(d/n, q), as well as the unscaled factors. */
    local K, U, x, y, gens, First, Second, n;
    
    K := BaseRing(G);
    U := UserGenerators(G);
    x, y := AreProportional([U[i]^b[1] : i in [1 .. #U]], b[2]);

    m := Nrows(y[1][1]);
    gens := [y[i][1] : i in [1 .. #y]];  
    First := sub<GL(m, K) | [y[i][1] : i in [1 .. #y]]>;  
    First`UserGenerators := gens;
    
    n := Nrows(y[1][2]);
    gens := [y[i][2] : i in [1 .. #y]];  
    Second := sub<GL(n, K) | [y[i][2] : i in [1 .. #y]]>;
    Second`UserGenerators := gens;
    
    return ScaleFactor(First), ScaleFactor(Second), First, Second;
end function;
