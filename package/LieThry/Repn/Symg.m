freeze;

/* By Dan */
intrinsic ConjugationClassLength( l::SeqEnum ) -> RngIntElt
{ The order of the conjugation class of Sym_n of permutations of cycle type l, n = &+l }
	mps := [ #[ i : i in l | i eq j ] : j in Seqset(l) ];
	r := Multinomial(&+l, l) / &*[Factorial(i) : i in mps];
	r *:= &*[ Factorial(i-1) : i in l ];
	return r;
end intrinsic;

intrinsic CycleStructureToSeq( l::SeqEnum : PadZeroes := false) -> SeqEnum
{ Convert Magma cycle structure to Lie cycle structure }
	ret := [];
	for bl in l do
		for i in [1..(bl[2])] do
			Append(~ret, bl[1]);
		end for;
	end for;

	if (PadZeroes) then
		n := &+ret;
		while (#ret lt n) do Append(~ret, 0); end while;
	end if; 

	return ret;
end intrinsic;

intrinsic SymmetricCharacterValues( l::SeqEnum ) -> SeqEnum, SeqEnum
{ SymmetricCharacterValue for every class of Sym(&+l) }
	return SymmetricCharacter(l), [ CycleStructure(k[3]) : k in Classes(Sym(&+l)) ];
end intrinsic;

intrinsic LiESymmetricCharacterValue( l::SeqEnum, m::SeqEnum) -> RngIntElt
{ A slightly adjusted version of SymmetricCharacterValue(SeqEnum, GrpPermElt) }
	n := &+l; cnt := 1; S := Sym(n);

	if (Type(m[1]) eq Tup) then
		m := CycleStructureToSeq(m);
	end if;
	m := [ m0 : m0 in m | m0 ne 0 ];

	/* from here on we assume that the cycle structure is in LiE format,
	without trailing zeroes, i.e [3,2,2,1] rather than [<3,1>,<2,2>,<1,1>] */

	/* construct a permutation prm with CycleStructure m, then return
	for the regular SymmetricCharacterValue */
	prm := S!1;
	for bl in m do
		tprm := [1..n];
		for i in [cnt..(cnt+bl-2)] do
			tprm[i] := i+1;
		end for;
		tprm[cnt+bl-1] := cnt;
		prm *:= S!tprm;
		cnt +:= bl;
	end for;

	return SymmetricCharacterValue(l, prm);
end intrinsic;


intrinsic PartitionToWeight( lambda::SeqEnum ) -> SeqEnum
{ Let n be the number of parts of lambda (trailing zeroes are 
  significant), then this function returns the weight for a 
  group of type A_(n-1); corresponding to lambda, expressed
  on the basis of fundamental weights }
  
	return [ lambda[i] - lambda[i+1] : i in [1..(#lambda - 1)] ];
end intrinsic;

intrinsic PartitionToWeight( lambda::ModTupRngElt ) -> ModTupRngElt
{ " }
  
  return ChangeRing(Vector(PartitionToWeight(Eltseq(lambda))), BaseRing(lambda));
end intrinsic;

intrinsic WeightToPartition( v::SeqEnum ) -> SeqEnum
{ v is interpreted as a weight for a group of type A_n 
  (where n is size(v)); the expression of that weight in
  n+1 partition coordinates is returned. When v is dominant, 
  this is a partition with n+1 parts.
}
	sum := 0;
	ret := [ 0 : i in [1..#v+1] ];
	i := #v;
	while (i ge 1) do
		sum +:= v[i];
		ret[i] := sum;
		i -:= 1;
	end while;
	return ret;
end intrinsic;

intrinsic WeightToPartition( v::ModTupRngElt ) -> ModTupRngElt
{ " }
    return ChangeRing(Vector(WeightToPartition(Eltseq(v))), BaseRing(v));
end intrinsic;

intrinsic TransposePartition( lambda::SeqEnum ) -> SeqEnum
{ The transpose partition of lambda }
	if (#lambda eq 0) then return []; end if;

	ret := [ 0 : i in [1..lambda[1]] ];
	j := 1;
	for i := #lambda to 1 by -1 do
		while (j le lambda[i]) do
			ret[j] := i;
			j +:= 1; 
		end while;
	end for;
	return ret;
end intrinsic;

intrinsic TransposePartition( lambda::ModTupRngElt ) -> ModTupRngElt 
{ " }
    return ChangeRing(Vector(TransposePartition(Eltseq(lambda))), BaseRing(lambda));
end intrinsic;



procedure Swap( ~prm, i, j )
	h := prm[i];
	prm[i] := prm[j];
	prm[j] := h;
end procedure;


intrinsic NextPermutation( ~prm::ModTupRngElt )
{ Finds the next permutation of the vector prm.  }
	/* Do not call this procedure with a permutation of size 1 or less */

	N := NumberOfColumns(prm);

	//First, find last ascent
	i := N - 1;
	prmi := prm[i];
	prmip1 := prm[i+1];
	while (prmi ge prmip1) do 
		i -:= 1;
		if (i eq 0) then prm := false; return; end if;
		prmip1 := prmi; prmi := prm[i];
	end while;

	//Then, find maximal j > i st prm[i] < prm[j]
	j := N;
	prmi := prm[i];
	while (prmi ge prm[j]) do
		j -:= 1;
	end while;

	/* Construct next permutation by first swapping the
		i-th and j-th position, and then reversing 
 		prm[i+1..N] */
	Swap(~prm, i, j);
	i +:= 1;
	j := N;
	while (i lt j) do
		Swap(~prm, i, j);
		i +:=1; j -:= 1;
	end while;
end intrinsic;
