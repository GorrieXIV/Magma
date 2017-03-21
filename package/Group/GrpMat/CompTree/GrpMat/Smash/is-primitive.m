freeze;

import "functions.m": BlockFlag;
import "functions.m": BlockNumbers;
import "stabiliser-test.m": BlockStabiliserTest;
import "functions.m": BlockSizes;
import "charpol-test.m": CharPolStructure;
import "minblocks.m": GroupActionOnBlocks;
import "functions.m": ImprimitiveFlag, ExtraSpecialFlag,
                 SetTensorInducedFactors, TensorInducedFlag;
import "functions.m": InitialiseBlockNumbers;
import "functions.m": InitialiseBlockSizes;
import "numbers.m": InverseSet;
import "minblocks.m": MinBlocks, NumberBlocks;
import "order-test.m": OrderOfElement;
import "random.m": RandomElement;
import "misc.m": FormCommutators;
import "functions.m": SemiLinearFlag;
import "functions.m": SetBlockNumbers;
import "functions.m": SetBlocksImage;
import "functions.m": SetBlockSizes;
import "functions.m": SetBlockSystem;
import "functions.m": BlockSystem;
import "functions.m": SetGenerators;
import "functions.m": SetImprimitiveFlag, MatrixSeed;
import "functions.m": SetTensorInducedFlag, SetExtraSpecialFlag;
import "smash.m": SmashModule; 
import "induced.m": UndoTensorProductFlags;
import "functions.m": TensorProductFlag, SetTensorProductFlag,
    SetTensorBasis, SetTensorFactors, SetSemiLinearFlag, 
    TensorInducedFactors;
import "../Tensor/is-tensor.m": SetTypes;

forward StartPrimitivityTest;

/* M has a tensor decomposition with first component TensorFactor, which 
   is imprimitive; use the stored block for its block system to write 
   down a block under the action of M */ 

ConstructBlock := function (M, TensorFactor)

   /* dimension of second factor */
   e := Dimension (TensorFactors(M)[2]);

   /* dimension of first factor */
   f := Dimension (TensorFactor);

   /* natural basis for the decomposition */
   B := TensorBasis (M);

   /* extract block system for action of M on second tensor factor */
   SmallBlockSystem := BlockSystem (TensorFactor);

   /* the stored representative block for the small system */
   SmallBlock := BlockFlag (SmallBlockSystem);

   /* number of blocks in small system */
   r := NumberBlocks (SmallBlockSystem);

   /* size of each block in the small system */
   s := f div r;

   /* now use this small block to construct block for larger system */
   LargeBlock := [];
   for i in [1..s] do
      for k in [1..e] do
         el := &+[SmallBlock[i][j] * B[(j - 1)* e + k] : j in [1..f]];
         Append (~LargeBlock, el);
      end for;
   end for;

   return LargeBlock;

end function;

/* M has a tensor decomposition found by SmashModule; check whether 
   first component of tensor product is imprimitive; if so, use the 
   block found for the first component to construct a block for M, 
   hand this block to MinBlocks (this is strictly unnecessary but 
   the call sets up proper fields in M), and set Result to TRUE; if 
   primitive set Result to FALSE; if unknown set Result to "unknown" */

ResolveTensor := function (M)

   TensorFactor := TensorFactors (M)[1];

   vprint Smash: "** About to call StartPrimitivityTest again **";

   Result := StartPrimitivityTest (TensorFactor, false);

   if (Result cmpeq false) then

      vprint Smash: "ResolveTensor found component is imprimitive";

      /* use block under first factor to construct a block under 
         action of M  */

      LargeBlock := ConstructBlock (M, TensorFactor);

      /* now call MinBlocks and set appropriate flags for M  */
      V := VectorSpace (BaseRing (M), Dimension (M));
      S := sub < V | LargeBlock >;
      LargeBlock := Basis (S);

      SetBlockSystem (M, MinBlocks (M, LargeBlock));

      // temporary code -- remove later
      if (LargeBlock ne BlockFlag (BlockSystem (M))) then
         error "Blocks are not equal in ResolveTensor\n";
      end if;

      SetBlockSizes (M, {NumberBlocks (BlockSystem (M))});
      SetBlockNumbers (M, InverseSet (Dimension (M), BlockSizes (M)));

      return true;

   elif (Result cmpeq true) then 
      return false;
   else 
      return Result;
   end if;

end function;

/* index in Queue of element of smallest rank */
   
IndexMinimumRankElement := function (Queue)

   if #(Queue) eq 0 then return 0; end if;
   t := [Queue[i][2]: i in [1..#Queue]];
   m, index :=  Minimum (t);
   return index;

end function; 

/* examine results of Smash; if report is true, vprint Smash: result  */

ExamineSmashResult := function (M, report)

   /* the following are possible outcomes from the call to SmashMatGp: 
    
    (a) all commutators of generators are scalar (so the group must 
        be central by abelian) and SmashModule exits with an error 
    (b) group is imprimitive
    (c) group is a tensor product
    (d) group is semilinear 
    (e) the commutator subgroup acts absolutely irreducibly 
    
    (a) may result in an Error; 
    if (b) we return true; 
    if (c) we return false; 
    if (d) we return "unknown"
    (e) has no impact and we return false; */

   if ImprimitiveFlag (M) cmpeq true then
      if report then 
         vprint Smash: "Matrix group is imprimitive";
      end if;
      return true;
   elif TensorProductFlag (M) cmpeq true then 
      if report then 
         vprint Smash: "Module is a tensor product";
      end if;
      return false;
   elif SemiLinearFlag (M) cmpeq true then 
      if report then 
         vprint Smash: "Module is semilinear";
      end if;
      return "unknown";
   end if;

   return false;

end function;

/* call Smash with TestElement;
   if TensorTest is true, we are carrying out test for tensor product;

   if SmashModule finds system of imprimitivity, return true;
   if SmashModule finds a tensor product, then it may discover that the 
   first component is semilinear -- in this case return "unknown";
   else return false */
   
SmashElement := function (M, TestElement, TensorTest) 

   Result := false;

   if Type (TestElement) eq GrpMatElt then 
      Elts := [TestElement]; 
   else
      Elts := TestElement;
   end if;

   if TensorTest eq false then flag := "PartialSmash"; else flag := ""; end if;
   SmashModule (M, ~Elts, flag);

   /* SmashModule may find system of imprimitivity or a tensor product 
      or it may find that the module is semilinear and hence
      we return "unknown" */

   if ImprimitiveFlag (M) cmpeq true then 
      SetBlockSizes (M, {NumberBlocks (BlockSystem (M))});
      return true;
   elif TensorProductFlag (M) cmpeq true then 

      if TensorTest eq true then return "unknown"; end if;

      Result := ResolveTensor (M);

       /* if our recursive call to PrimitiveTest found that the second
       component of the tensor decomposition is imprimitive, then 
       our group is imprimitive; alternately, we may have obtained 
       semilinear as the result; in either case, we set flag */

      if not (Result cmpeq false) then
         SetImprimitiveFlag (M, Result); 
      end if;
 
      return Result;

   elif SemiLinearFlag (M) cmpeq true then 
      return "unknown";
   end if;

   return false;

end function;

/* remove flags */
procedure UndoFlags (G)

   SetImprimitiveFlag (G, "unknown");
   SetTensorProductFlag (G, "unknown");
   SetTensorInducedFlag (G, "unknown");
   SetExtraSpecialFlag (G, "unknown");
   SetSemiLinearFlag (G, "unknown");
   
end procedure;

intrinsic SearchForDecomposition (G::GrpMat, E::SeqEnum: Report := true,
                                             NoSymTens := false) -> BoolElt
{Attempt to decompose G wrt normal closure in G of E} 

   /* reset to unknown */
   UndoFlags (G);

   SmashModule (G, ~E, true : NoSymTens := NoSymTens);

   if ImprimitiveFlag (G) cmpeq true then
      if Report then 
         "Smash: G is imprimitive";
      end if;
      return true;
   elif TensorProductFlag (G) cmpeq true then 
      if Report then 
         "Smash: G is a tensor product";
      end if;
      SetTypes (G);
      return true;
   elif SemiLinearFlag (G) cmpeq true then 
      if Report then 
         "Smash: G is semilinear";
      end if;
      return true;
   elif ExtraSpecialFlag (G) cmpeq true then 
      if Report then 
         parm := ExtraSpecialParameters (G);
         r := parm[1]; n := parm[2];
         s := r eq 2 and IsEven (n) select "symplectic " else "extraspecial ";
         str := s cat IntegerToString (r) cat "-group";
         "Smash: G is normaliser of", str;
      end if;
      return true;
   elif TensorInducedFlag (G) cmpeq true then 
      if Report then 
         "Smash: G is tensor-induced";
      end if;
      factors := TensorInducedFactors (G);
      SetTensorInducedFactors (G, [Group (M): M in factors]); 
      return true;
   end if;

   if Report then "Smash: No decomposition found"; end if;
   return false;

end intrinsic;

/* call Smash with TestElement;
   if SmashModule finds system of imprimitivity, return true;
   else return false */

CallSmashModule := function (M, TestElement, t) 

   Result := SmashElement (M, TestElement, false);

   /* SmashElement may find system of imprimitivity or 
      may not be able to settle case */

   if (Result cmpeq true) then return Result; end if;

   /* if SmashModule did not find system and did not 
      conclude "semilinear", we rule out all block sizes > t */
   if Result cmpeq false then 
      SizesOfBlocks := {x : x in BlockSizes (M) | x le t};
      SetBlockSizes (M, SizesOfBlocks);
   end if;

   return false;

end function;

/*  carry out tests for basic reductions of the module M */

BasicReductionTests := function (M)

   // is the module irreducible?
   if IsIrreducible (M) eq false then
      vprint Smash: "Module is not irreducible\n";
      return true;
   end if;

   // is the module absolutely irreducible?
   if IsAbsolutelyIrreducible (M) eq false then
      vprint Smash: "Module is not absolutely irreducible\n";
      return true;
   end if;

   return false;
   
   // test for semilinearity
//    SemiLinearTest (M);

   Result := ExamineSmashResult (M, true);

   if TensorProductFlag (M) cmpeq true then
      Result := ResolveTensor (M);

      /* if our recursive call to PrimitiveTest found that a component of
         the tensor decomposition is imprimitive, we can deduce that our
         group is imprimitive; alternately, it may have found that the
         associated module is semilinear */

      if not (Result cmpeq false) then
         SetImprimitiveFlag (M, Result);
      end if;

   end if;

   return Result;

end function;

/*  if there is an element of rank < the smallest remaining block size, 
    then finish the computation by calling SmashModule;
    even if this is not so, if ProcessLeast is true, then call SmashModule 
    with minimum rank element from SmashModule Queue;
    set appropriate flags; return true if block system found or
    primitivity proved, else false */

FinishComputation := function (M, Queue, ProcessLeast)

   SizesOfBlocks := BlockSizes (M);

   /* do we already know the answer? */
   Result := ImprimitiveFlag (M);
   if Result cmpeq true or Result cmpeq false then
      return true; 
   end if;

   if #SizesOfBlocks ne 0 then 

      /* note index position of element of least rank in SmashModule queue */
      Index := IndexMinimumRankElement (Queue);

      /* if this is smaller than remaining valid block sizes or
        ProcessLeast is true, call SmashModule */

      if Index ne 0 then 
         t := Queue[Index][2];
         if ProcessLeast or (Minimum (SizesOfBlocks) gt t) then 

            vprint Smash: "Possible block sizes are currently ", SizesOfBlocks;
            vprint Smash: "\nCall SmashModule with element of rank ", t;

            TestElement := Queue[Index][1];
            Result := CallSmashModule (M, TestElement, t); 

            SetBlockNumbers (M, InverseSet (Dimension (M), BlockSizes (M)));
            vprintf Smash: "\nAfter Smash call, possible block sizes are %o\n", 
                  BlockSizes (M);
            if Result eq true then return true; end if;
         end if;
      end if;

   end if;

   if #(BlockSizes (M)) eq 0 then 
      SetImprimitiveFlag (M, false);
      return true; 
   end if;

   return false; 

end function; 
  
/* have we eliminated all valid block sizes?
    can we settle computation via a single call to SmashModule?
    if either is the case, return true, else return false */
  
SettleComputation := function (M, Queue)

   SizesOfBlocks := BlockSizes (M);
   if #SizesOfBlocks eq 0 then return true; end if;

   /* note index position of element of least rank in SmashModule queue */
   Index := IndexMinimumRankElement (Queue);

   /* is this smaller than existing valid block sizes? */
   if Index ne 0 then 
      return (Minimum (SizesOfBlocks) gt Queue[Index][2]);
   end if;

   return false;

end function;

procedure PrimitiveTest (M, NmrElements)
 
   d := Dimension (M);

   Elts := []; Orders := [];  ProjectiveOrders := [];
   Queue := []; NmrElts := 0;

   repeat 
      g := RandomElement (M);
      NmrElts +:= 1;
      o, verified := Order (g : Proof := false);
      if verified and not (o in Orders) and (o ne 1) then 
         vprint Smash: "\nElement has order ", o;

         OrderOfElement (M, o);
         SetBlockSizes (M, InverseSet (d, BlockNumbers (M)));

         if FinishComputation (M, Queue, false) then return; end if;

         CharPolStructure (M, g, o, ~Queue);
         SetBlockNumbers (M, InverseSet (d, BlockSizes (M)));

         if FinishComputation (M, Queue, false) then return; end if;

         if not IsScalar (g) then 
            Append (~Elts, g);
            Append (~Orders, o);
            Append (~ProjectiveOrders, ProjectiveOrder (g));
         end if;

      end if;

   until NmrElts eq NmrElements;

   /* eliminate all block sizes > minimum value of rank */

   if FinishComputation (M, Queue, true) then return; end if;

   /* we need to deal with composite order elements here */

   SetBlockSizes (M, InverseSet (d, BlockNumbers (M)));

   /* for each remaining number r of blocks, apply BlockStabiliserTest 
      to either find blocks or show that there are no block systems 
      of r blocks */

   NumbersOfBlocks := BlockNumbers (M);
   vprintf Smash: "\nPossible numbers of blocks is now %o\n", NumbersOfBlocks;

   for r in NumbersOfBlocks do 
      vprintf Smash: "\nSeeking to eliminate block number %o\n", r;
      BlockStabiliserTest (M, ~Elts, ~ProjectiveOrders, r, ~Result);
      if Result cmpeq true then
          vprintf Smash: "Successfully eliminated block number %o\n", r;
          SetBlockNumbers (M, BlockNumbers (M) diff {r});
      elif Result cmpeq false then
          n := NumberBlocks (BlockSystem (M));
          SetBlockNumbers (M, {n});
          SetBlockSizes (M, {d div n});
          SetImprimitiveFlag (M, true);
          return;
      elif Result cmpeq "unknown" then
         vprintf Smash: "BlockStabiliser: failed to complete\n";
         return;
      else
          /* SmashModule call found module is semilinear */
          vprintf Smash: "BlockStabiliser: Module is semilinear\n";
          // return; 
      end if;
   end for;

   SetBlockSizes (M, InverseSet (d, BlockNumbers (M)));

   flag := FinishComputation (M, Queue, false);

end procedure;

/* delete components from M */

procedure DeletePrimitivityComponents (M)

   delete M`BlockNumbers;
   delete M`BlockSizes;
end procedure;

/* have we discovered that M is (im)primitive?  */

ReportResult := function (M, PrintFlag)

   // is the group imprimitive?
   Result := ImprimitiveFlag (M);

   // do we know the answer?
   if Type (Result) ne BoolElt then return Result; end if;

   // is the group primitive?
   Result := not Result;

   if PrintFlag then 
      if Result eq false then 
         vprintf Smash: "Number of blocks is %o\n", 
            NumberBlocks (BlockSystem (M));
      end if;
      vprintf Smash: "Group primitive? %o\n", Result;
   end if;

   return Result;

end function; 

StartPrimitivityTest := function (M, PrintFlag: BlockSizes := [])

   blocksizes := BlockSizes;
   d := Dimension (M);

   // can we reduce the problem?
   if (BasicReductionTests (M) cmpeq true) then 
      Result := ReportResult (M, PrintFlag);
      return Result;
   end if;

   // initialise these components 
   if BlockNumbers (M) cmpeq "unknown" then
      if blocksizes cmpeq [] then 
         InitialiseBlockSizes (M);
      else
         M`BlockSizes := blocksizes;
      end if;
   end if;

   if BlockNumbers (M) cmpeq "unknown" then 
      M`BlockNumbers := [d div x : x in M`BlockSizes];
   end if;

   // now test for (im)primitivity
   NmrElements := 20;
   PrimitiveTest (M, NmrElements);

   Result := ReportResult (M, PrintFlag);

   return Result;

end function;

/* is G primitive? */

function IsPrimitiveMain (G: BlockSizes := [])

   blocksizes := BlockSizes;

   flag := ImprimitiveFlag (G);

   if Type (flag) cmpeq BoolElt then 
      return not flag;
   end if;

   if Type (G) eq GrpMat then 
      SetGenerators (G, GroupGenerators (G));
   elif Type (G) eq ModGrp then 
      SetGenerators (G, GroupGenerators (Group (G)));
   else 
      error "IsPrimitive expects a group or a G-module";
   end if;

   /* is G a tensor product */
   if TensorProductFlag (G) cmpeq true then 
      Store := [* TensorProductFlag (G), TensorBasis (G), TensorFactors (G) *];
      UndoTensorProductFlags (G);
   else 
      Store := [];
   end if;

   d, F := BasicParameters (G);
   vprintf Smash: "\nDimension = %o F is %o\n", d, F;
   if blocksizes ne [] then 
      blocksizes := [x : x in blocksizes | d mod x eq 0];
      if #blocksizes eq 0 then return true; end if;
   end if;

   Result := StartPrimitivityTest (G, true: BlockSizes := blocksizes);

   if Result cmpeq false then 
      B := BlockSystem (G);
      SetBlocksImage (G, GroupActionOnBlocks (B));
      /* do we know G is a tensor product? if so, reset flags */
      if #Store gt 0 then 
         SetTensorProductFlag (G, Store[1]);
         SetTensorBasis (G, Store[2]);
         SetTensorFactors (G, Store[3]);
      end if;
      return Result;
   end if; 

   /* we may have only checked some of the possible block sizes */
   if #BlockSizes eq 0 and Result cmpeq true then
      SetImprimitiveFlag (G, false);
   else 
      SetImprimitiveFlag (G, "unknown");
   end if;

   // delete those components now unnecessary 
   DeletePrimitivityComponents (G);

   return Result;

end function;

intrinsic ImprimitiveBasis (G::GrpMat) -> GrpMatElt
{Change-of-basis which exhibits block structure for imprimitive group}
   if ImprimitiveFlag (G) cmpeq true then 
      blocks := Blocks (G);
      d := Degree (G);
      F := BaseRing (G);
      B := &cat[&cat[Eltseq (blocks[i].j): j in [1..Dimension (blocks[1])]]:
         i in [1..#blocks]];
      return GL(d, F) ! B;
   else
      return "unknown";
   end if;
end intrinsic;

intrinsic ImprimitiveAction (G::GrpMat, g::GrpMatElt) -> GrpPermElt
{Action of g on blocks of imprimitivity of G}
   if ImprimitiveFlag (G) cmpeq true then 
      blocks := Blocks (G);
      n := #blocks;
      S := Sym (n);
      list := [Position (blocks, blocks[i]^g): i in [1..#blocks]];
      if Set (list) eq {1..n} then
         return S!list;
      end if;
   else 
      return "unknown"; 
   end if;
end intrinsic;

intrinsic IsPrimitive(G::GrpMat: BlockSizes := []) -> BoolElt
{Return true if G is primitive, false if G is imprimitive, otherwise "unknown"}
    if Degree (G) eq 1 then return true; end if;
    if Degree (G) gt 4 and RecogniseClassical (G) cmpeq true then return true; end if;
    try 
       return IsPrimitiveMain (G: BlockSizes := BlockSizes);
    catch err
       return "unknown";
    end try;
end intrinsic;

/* 
intrinsic IsPrimitive(M::ModGrp) -> BoolElt
{True iff M is primitive}
    return IsPrimitiveMain (M);
end intrinsic;
*/
