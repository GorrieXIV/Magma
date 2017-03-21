freeze;

/* By Dan */
intrinsic AdamsOperator(R::RootDtm, n::RngIntElt, v::SeqEnum) -> LieRepDec
{ The decomposition polynomial of the virtual module obtained by applying
  the n-th Adams operator }

	wts, mps := DominantCharacter(R, v);
	wts := [ n*w : w in wts ];
	return VirtualDecomposition( LieRepresentationDecomposition(R, wts, mps) );
end intrinsic;

intrinsic AdamsOperator(R::RootDtm, n::RngIntElt, v::ModTupRngElt) -> LieRepDec
{ The decomposition polynomial of the virtual module obtained by applying  the n-th Adams operator }
    return AdamsOperator(R, n, Eltseq(v));
end intrinsic;

intrinsic AdamsOperator(D::LieRepDec, n::RngIntElt) -> LieRepDec
{ The decomposition polynomial of the virtual module obtained by applying
  the n-th Adams operator }
    
    D2 := DominantCharacter(D);
    Wts,Mps := Explode(D2`WtsMps);
	nwts := [ n*w : w in Wts ];
	return VirtualDecomposition( LieRepresentationDecomposition(RootDatum(D), nwts, Mps) );
end intrinsic;

function SymmetricAlternatingPower(R, n, D, Alt) //->LieRepDec
/* Symmetric or Alternating Tensor, depending on the value of Alt

  We use the recursion: sym_tensor(n,l) = 
	 1/n sum_k=1^n tensor(sym_tensor(n-k, l), Adams(k, l))
*/

	dim := Dimension(R);

	if (n eq 0) then return LieRepresentationDecomposition(R, [ 0 : i in [1..dim] ]); end if;
	if (n eq 1) then return D; end if;

	Wts, Mps := Explode(D`WtsMps);

	AdamsResult := [ AdamsOperator(D, k) : k in [1..n] ];
	SAResult := [ LieRepresentationDecomposition(R, [ 0 : i in [1..dim] ]) ];

	for k in [1..n] do
		SAResult[k + 1] := TensorProduct( D, SAResult[k] );
		for i in [2..k] do
			c := (Alt and ((i-1) mod 2) eq 1) select -1 else 1;
			AddRepresentation( ~(SAResult[k+1]), TensorProduct(AdamsResult[i], SAResult[k-i+1]), c );
		end for;

        SAResult[k+1] /:= k;
	end for;

	return SAResult[n+1];
end function;

intrinsic SymmetricPower(D::LieRepDec, n::RngIntElt) -> LieRepDec
{ The decomposition polynomial of S^n (V_D), i.e. the n-th symmetric
	tensor power of V_D }
	return SymmetricAlternatingPower(RootDatum(D), n, D, false);
end intrinsic;
intrinsic SymmetricPower(R::RootDtm, n::RngIntElt, v::SeqEnum) -> LieRepDec
{ The decomposition polynomial of S^n (V_v), i.e. the n-th symmetric
	tensor power of V_v }
	return SymmetricAlternatingPower(R, n, LieRepresentationDecomposition(R, v), false);
end intrinsic;
intrinsic SymmetricPower(R::RootDtm, n::RngIntElt, v::ModTupRngElt) -> LieRepDec
{ " }
	return SymmetricAlternatingPower(R, n, LieRepresentationDecomposition(R, v), false);
end intrinsic;


intrinsic AlternatingPower(D::LieRepDec, n::RngIntElt) -> LieRepDec
{ The decomposition polynomial of \Lambda^n (V_D), i.e. the n-th alternating
	tensor power of D, aka the n-th exterior power }
	return SymmetricAlternatingPower(RootDatum(D), n, D, true);
end intrinsic;
intrinsic AlternatingPower(R::RootDtm, n::RngIntElt, v::SeqEnum) -> LieRepDec
{ The decomposition polynomial of \Lambda^n (V_v), i.e. the n-th alternating
	tensor power of V_v, aka the n-th exterior power }
	return SymmetricAlternatingPower(R, n, LieRepresentationDecomposition(R, v), true);
end intrinsic;
intrinsic AlternatingPower(R::RootDtm, n::RngIntElt, v::ModTupRngElt) -> LieRepDec
{ " }
	return SymmetricAlternatingPower(R, n, LieRepresentationDecomposition(R, v), true);
end intrinsic;



intrinsic Plethysm(D::LieRepDec, lambda::SeqEnum) -> LieRepDec
{ The decomposition polynomial of the plethysm of V_D corresponding
  to the partition lambda

  We use the recursion on page 72 of the LiE manual:

  plethysm(l, p) := 1/n! sum_k in partitions(n) class_ord(k) * sym_char(l, k) * DirectSum_i=1tol(k) Adams(ki, m)
   where n = &+l and l(k) the number of non-zero parts k_i of k.
}
    R := RootDatum(D);
	dim := Dimension(R);

	n := &+lambda;

	if (n eq 0) then return LieRepresentationDecomposition(R, [0 : i in [1..dim]]); end if;
	if (n eq 1) then return D; end if;

	AdamsResult := [ AdamsOperator(D, i) : i in [1..n] ];
	ChrValues, Clss := SymmetricCharacterValues(lambda);

	PResult := LieRepresentationDecomposition(R);

	for i in [1..#Clss] do
		Mu := CycleStructureToSeq(Clss[i]);
		prod := AdamsResult[Mu[1]];
		for j in [2..#Mu] do
			prod := TensorProduct(prod, AdamsResult[Mu[j]]);
		end for;
        
        AddRepresentation(~PResult, prod, Integers()!(ChrValues[i]*ConjugationClassLength(Mu)));
        //tao := PResult`WtsMps; print i, ": interm: ", Hash(Seqset(tao[1])), Hash(Seqset(tao[2]));
	end for;

    PResult /:= Factorial(n);
	return PResult;
end intrinsic;

intrinsic Plethysm(R::RootDtm, lambda::SeqEnum, mu::ModTupRngElt) -> LieRepDec
{ The decomposition polynomial of the plethysm of V_mu corresponding to the partition lambda.}
	return Plethysm(LieRepresentationDecomposition(R, mu), lambda);
end intrinsic;

intrinsic Plethysm(R::RootDtm, lambda::SeqEnum, mu::SeqEnum) -> LieRepDec
{ " }
	return Plethysm(LieRepresentationDecomposition(R, mu), lambda);
end intrinsic;
