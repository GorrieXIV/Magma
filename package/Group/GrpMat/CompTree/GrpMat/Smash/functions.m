
freeze;

import "misc.m": FormCommutators;
import "random.m": InitialiseSeed;
import "smash-spec.m": SeedLength, NumberMultiplications; 

/* initialise block sizes */

procedure InitialiseBlockSizes (M)
   M`BlockSizes := Set (Divisors (Dimension (M))) diff {Dimension (M)};
end procedure;

/* initialise block numbers */

procedure InitialiseBlockNumbers (M)
   M`BlockNumbers := Set (Divisors (Dimension (M))) diff {1};
end procedure;

procedure SetBlockSizes (M, value)

   M`BlockSizes := value;

end procedure;

procedure SetBlockNumbers (M, value)

   M`BlockNumbers := value;

end procedure;

procedure SetBlockSystem (M, value)

   M`BlockSystem := value;

end procedure;

BlockNumbers := function (M)

   if assigned M`BlockNumbers then return M`BlockNumbers; end if; 
   return "unknown"; 

end function;

BlockSizes := function (M)

   if assigned M`BlockSizes then return M`BlockSizes; end if; 
   return "unknown"; 

end function;

/* The block system of G */
function BlockSystem(G)
   if assigned G`BlockSystem then return G`BlockSystem; end if; 
   return "unknown"; 
end function;

procedure SetImprimitiveFlag (M, value)

   M`ImprimitiveFlag := value;

end procedure;

ImprimitiveFlag := function (M)

   if assigned M`ImprimitiveFlag then return M`ImprimitiveFlag; end if; 
   return "unknown"; 

end function;

TensorProductFlag := function (M)

   if assigned M`TensorProductFlag then return M`TensorProductFlag; end if; 
   return "unknown"; 

end function;

procedure SetTensorProductFlag (M, value)

   M`TensorProductFlag := value;

end procedure;

procedure SetSemiLinearFlag (M, value)

   M`SemiLinearFlag := value;

end procedure;

SemiLinearFlag := function (M)

   if assigned M`SemiLinearFlag then return M`SemiLinearFlag; end if; 
   return "unknown"; 

end function;

ExtraSpecialGenerators := function (G)

   if assigned G`ExtraSpecialGenerators then 
      return G`ExtraSpecialGenerators; end if; 
   return "unknown"; 

end function;

intrinsic ExtraSpecialParameters (G::GrpMat) -> SeqEnum
{Return prime and exponent of the extraspecial or symplectic subgroup normalised by G}

   if assigned G`ExtraSpecialParameters then 
      return G`ExtraSpecialParameters; end if; 
   return "unknown"; 

end intrinsic;

intrinsic ExtraSpecialBasis (G::GrpMat) -> GrpMatElt
{Return change-of-basis matrix for extraspecial subgroup normalised by G}

   if assigned G`ExtraSpecialBasis then 
      return G`ExtraSpecialBasis; end if; 
   return "unknown"; 

end intrinsic;

intrinsic ExtraSpecialGroup (G::GrpMat) -> GrpMat
{Return the extraspecial or symplectic normal subgroup of G}

   if assigned G`ExtraSpecialGroup then return G`ExtraSpecialGroup; end if; 
   return "unknown"; 

end intrinsic;

intrinsic ExtraSpecialNormaliser (G::GrpMat) -> SeqEnum
{Return the action of generators of G on its normal extraspecial or symplectic
 subgroup as a sequence of matrices}

   if assigned G`ExtraSpecialNormaliser then return G`ExtraSpecialNormaliser; end if; 
   return "unknown"; 

end intrinsic;

ExtraSpecialFlag := function (M)

   if assigned M`ExtraSpecialFlag then return M`ExtraSpecialFlag; end if; 
   return "unknown"; 

end function;

procedure SetTensorFactors (M, value)

   M`TensorFactors := value;

end procedure;

procedure SetExtraSpecialGroup (M, value)

   M`ExtraSpecialGroup := value;

end procedure;

procedure SetExtraSpecialGenerators (M, value)

   M`ExtraSpecialGenerators := value;

end procedure;

procedure SetExtraSpecialBasis (M, value)

   M`ExtraSpecialBasis := value;

end procedure;

procedure SetExtraSpecialNormaliser (M, value)

   M`ExtraSpecialNormaliser := value;

end procedure;

procedure SetExtraSpecialParameters (M, value)

   M`ExtraSpecialParameters:= value;

end procedure;

procedure SetExtraSpecialFlag (M, value)

   M`ExtraSpecialFlag:= value;

end procedure;

procedure SetTensorBasis (M, value)

   M`TensorBasis := value;

end procedure;

intrinsic TensorFactors(M::ModGrp) -> Tup
{The tensor factors of M}

   if assigned M`TensorFactors then return M`TensorFactors; end if;
   return "unknown";

end intrinsic;

intrinsic TensorFactors (G::GrpMat) -> Tup
{The tensor factors of G}

   if assigned G`TensorFactors then return G`TensorFactors; end if; 
   return "unknown"; 

end intrinsic;
   
intrinsic TensorBasis (G::GrpMat) ->  AlgMatElt
{Return the change of basis matrix which exhibits the 
 tensor decomposition of G};

   if assigned G`TensorBasis then return G`TensorBasis; end if; 
   return "unknown"; 

end intrinsic;

intrinsic TensorBasis (M::ModGrp) -> AlgMatElt
{Return the change of basis matrix which exhibits the
 tensor decomposition of M};

   if assigned M`TensorBasis then return M`TensorBasis; end if;
   return "unknown";

end intrinsic;
   
BlockFlag := function (B)

   if assigned B`Block then return B`Block; end if; 
   return "unknown"; 

end function;

procedure SetGenerators (M, value)

   M`Generators := value;

end procedure;

procedure SetFrobeniusAutomorphisms (M, value)

   M`FrobeniusAutomorphisms := value;

end procedure;

procedure SetCentralisingMatrix (M, value)

   M`CentralisingMatrix := value;

end procedure;

procedure SetLinearPart (M, value)

   M`LinearPart := value;

end procedure;

procedure SetDegreeFieldExtension (M, value)

   M`DegreeOfFieldExtension := value;

end procedure;

procedure SetSemiLinearFlag (M, value)

   M`SemiLinearFlag := value;

end procedure;

SemiLinearFlag := function (M)

   if assigned M`SemiLinearFlag then return M`SemiLinearFlag; end if; 
   return "unknown"; 

end function;

intrinsic DegreeOfFieldExtension (G::GrpMat) -> RngIntElt
{The degree of the field extension of G}

   if assigned G`DegreeOfFieldExtension then return G`DegreeOfFieldExtension;end if; 
   return "unknown"; 

end intrinsic;

LinearPart := function (M)

   if assigned M`LinearPart then return M`LinearPart; end if; 
   return "unknown"; 

end function;

intrinsic CentralisingMatrix (M::ModGrp) -> AlgMatElt
{The centralising matrix of M}

   if assigned M`CentralisingMatrix then return M`CentralisingMatrix; end if; 
   return "unknown"; 

end intrinsic;

intrinsic CentralisingMatrix (G::GrpMat) -> AlgMatElt
{The centralising matrix of G}

   if assigned G`CentralisingMatrix then return G`CentralisingMatrix; end if; 
   return "unknown"; 

end intrinsic;

intrinsic FrobeniusAutomorphisms (G::GrpMat) -> AlgMatElt
{The Frobenius automorphisms of G}

   if assigned G`FrobeniusAutomorphisms then
       return G`FrobeniusAutomorphisms;
   end if; 
   return "unknown"; 

end intrinsic;

procedure SetTensorInducedFlag (M, value)

   M`TensorInducedFlag := value;

end procedure;

TensorInducedFlag := function (M)
 
   if assigned M`TensorInducedFlag then return M`TensorInducedFlag; end if;
   return "unknown";
 
end function;                                                                   
procedure SetTensorInducedFactors (M, value)

   M`TensorInducedFactors := value;

end procedure;

procedure SetTensorInducedBasis (M, value)

   M`TensorInducedBasis := value;

end procedure;

procedure SetTensorInducedImageBasis (M, value)

   M`TensorInducedImageBasis := value;

end procedure;

procedure SetTensorInducedPermutations (M, value)

   M`TensorInducedPermutations := value;

end procedure;

/* tensor induced factors of G */
TensorInducedFactors := function (G) 

   if assigned G`TensorInducedFactors then return G`TensorInducedFactors; end if; 
   return "unknown"; 

end function;

intrinsic TensorInducedBasis (G::GrpMat) -> AlgMatElt
{Return the change of basis matrix which exhibits that G is 
 tensor-induced}

   if assigned G`TensorInducedBasis then return G`TensorInducedBasis; end if; 
   return "unknown"; 

end intrinsic;

/* return the tensor induced image basis of G */
TensorInducedImageBasis := function (G) 

   if assigned G`TensorInducedImageBasis then return G`TensorInducedImageBasis; end if; 
   return "unknown"; 

end function;

intrinsic TensorInducedPermutations (G::GrpMat) -> SeqEnum
{Return the permutations of the factors induced by the 
 generators of G}

   if assigned G`TensorInducedPermutations then 
      return G`TensorInducedPermutations; end if; 
   return "unknown"; 

end intrinsic;

procedure SetBlocksImage (M, value)

   M`BlocksImage := value;

end procedure;

intrinsic BlocksImage (G::GrpMat) -> GrpPerm
{The permutation group induced by action of G on blocks of imprimitivity}
   if assigned G`BlocksImage then return G`BlocksImage; end if; 
   return "unknown"; 
end intrinsic;

intrinsic Blocks (G::GrpMat) -> SeqEnum
{The blocks of imprimitivity of the matrix group G} 
   if assigned G`BlockSystem then return G`BlockSystem`Blocks; end if; 
   return "unknown"; 
end intrinsic;

procedure SetMatrixSeed (M, value)

   M`Seed := value;

end procedure;

MatrixSeed := function (M)

   if assigned M`Seed then return M`Seed; end if; 

   InitialiseSeed (M, SeedLength, NumberMultiplications);

   return M`Seed;

end function;

procedure DeleteMatrixSeed (M)

  delete M`Seed;

end procedure;
