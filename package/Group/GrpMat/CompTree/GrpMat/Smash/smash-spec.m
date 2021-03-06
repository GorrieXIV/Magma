freeze;

Nmr := 10;
NmrTries := 100;

SeedLength := 10; NumberMultiplications := 100;

declare attributes GrpMat:
Seed, NormalSeed, BlockNumbers, BlockSizes, NmrOfBlocks, BlocksImage,
BlockSystem, ImprimitiveFlag, TensorProductFlag, TensorFactors, 
TensorBasis, Generators,
ExtraSpecialFlag, ExtraSpecialGroup, ExtraSpecialParameters,
ExtraSpecialBasis, ExtraSpecialGenerators, ExtraSpecialNormaliser,
SemiLinearFlag, DegreeOfFieldExtension, LinearPart, CentralisingMatrix, 
FrobeniusAutomorphisms, 
SmallerFieldChangeOfBasis, SmallerField,
TensorInducedImageBasis, TensorInducedFlag, TensorInducedFactors, 
TensorInducedPermutations, TensorInducedBasis; 

declare attributes ModGrp: 
Seed, BlockNumbers, BlockSizes, NmrOfBlocks, BlocksImage,
BlockSystem, ImprimitiveFlag, TensorProductFlag, TensorFactors, 
TensorBasis, Generators,
ExtraSpecialFlag, ExtraSpecialGroup, ExtraSpecialParameters,
ExtraSpecialBasis, ExtraSpecialGenerators, ExtraSpecialNormaliser,
SemiLinearFlag, DegreeOfFieldExtension, LinearPart, CentralisingMatrix, 
FrobeniusAutomorphisms, 
TensorInducedFlag, TensorInducedFactors, 
TensorInducedPermutations, TensorInducedBasis; 

declare attributes AlgMat: Seed, Generators;

declare attributes GrpPerm: Seed, Generators, NormalSeed;

intrinsic GModule (S::SeqEnum[Mtrx]) -> ModGrp

{ Return G-module generated by sequence of matrices }

  require #S ne 0 : "Sequence of matrices must be non-empty";
  P := Parent (Rep (S));
  if Type(P) eq MtrxSprsStr then
    d := Ncols(S[1]);
    require forall{x : x in S | Ncols(x) eq d and Nrows(x) eq d} :
      "Matrices must be square";
    S := [Matrix(x) : x in S];
    F := CoefficientRing(S[1]);
  else
    d, F := BasicParameters (P);
  end if;  

  G := sub < GL (d, F) | S >;

  return GModule (G);
end intrinsic;

intrinsic GModule (S::SetEnum[Mtrx]) -> ModGrp
{ Return G-module generated by set of matrices }

  require #S ne 0 : "Set of matrices must be non-empty";
  P := Parent (Rep (S));
  if Type(P) eq MtrxSprsStr then
    d := Ncols(S[1]);
    require forall{x : x in S | Ncols(x) eq d and Nrows(x) eq d} :
      "Matrices must be square";
    S := [Matrix(x) : x in S];
    F := CoefficientRing(S[1]);
  else
    d, F := BasicParameters (P);
  end if;  

  G := sub < GL (d, F) | S >;

  return GModule (G);

end intrinsic;

intrinsic Dimension (G::GrpMat) -> RngIntElt
{ Return degree of matrices of G }
  return Degree (G);
end intrinsic;

intrinsic GeneratorsSequence(G::GrpMat) -> []
{The sequence of group generators.}
  return [G.i : i in [1..Ngens(G)]];
end intrinsic;

intrinsic BasicParameters (G::GrpMat) -> RngIntElt, RngIntElt
{Return the dimension and field for G }
  return Dimension (G), BaseRing (G);
end intrinsic;

intrinsic BasicParameters (G::AlgMat) -> RngIntElt, RngIntElt
{Return the dimension and field for G }
  return Degree (G), BaseRing (G);
end intrinsic;

intrinsic BasicParameters (M::ModGrp) -> RngIntElt, RngIntElt
{Return the dimension and field for the G-module M }
  return Dimension (M), BaseRing (M);
end intrinsic;

intrinsic GroupGenerators (M::AlgMat) -> SeqEnum
{Return a sequence containing generators of the underlying group}

    if assigned M`Generators then
        if Type (M`Generators) eq SeqEnum then
          return M`Generators;
        else
          return SetToSequence (M`Generators);
        end if;
    else
        return [G.i: i in [1..Ngens (G)]] where G := Group(M);
    end if;

end intrinsic;

intrinsic GroupGenerators (M::ModGrp) -> SeqEnum
{Return a sequence containing generators of the underlying group}

    if assigned M`Generators then
        if Type (M`Generators) eq SeqEnum then
          return M`Generators;
        else
          return SetToSequence (M`Generators);
        end if;
    else
        return [G.i: i in [1..Ngens (G)]] where G := Group(M);
    end if;


end intrinsic;

intrinsic GroupGenerators (G::GrpMat) -> SeqEnum
{Return as a sequence the generators of the group G}

return [G.i: i in [1..Ngens (G)]];

end intrinsic;
