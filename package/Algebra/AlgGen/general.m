freeze;


/////////////////////////////////////////////////////
// Misc basic things for general algebras
// Steve Donnelly, August  2010
/////////////////////////////////////////////////////

intrinsic VectorSpace(A::Alg) -> ModTupFld, Map
{The vector space corresponding to A}

  require HasSignature("Dimension", [Type(A)]):
      "Not currently supported for this kind of algebra";

  V := VectorSpace(BaseRing(A), Dimension(A));
  AtoV := map< A -> V | a :-> V!Eltseq(a),
                        v :-> A!Eltseq(v) >;
  return V, AtoV;
end intrinsic;

intrinsic VectorSpaceOverQ(A::Alg) -> ModTupFld, Map
{For an algebra over a number field, returns the underlying vector space over Q}
  K := BaseRing(A);
  dK := Degree(K);
  dA := Dimension(A);
  if Type(K) eq FldRat then return VectorSpace(A); end if;
  require ISA(Type(K),FldAlg) and BaseRing(K) eq Rationals() :
         "A should be defined over an absolute number field";
  V := VectorSpace(Rationals(), dA*dK);
  AtoV := map< A -> V | a :-> V! &cat[Eltseq(c) : c in Eltseq(a)],
                        v :-> A! [K! vv[1+(j-1)*dK..j*dK] : j in [1..dA]] where vv is Eltseq(v) >;
  return V, AtoV;
end intrinsic;

