freeze;

//Attach("../CompTree/GrpMat/Smash/minblocks.m");
//Attach("../CompTree/GrpMat/Smash/functions.m");
import "../CompTree/GrpMat/Smash/minblocks.m":
       MinBlocks, GroupActionOnBlocks, NumberBlocks;
import "../CompTree/GrpMat/Smash/functions.m":
       SetImprimitiveFlag, SetBlockSystem, SetBlockSizes, SetBlocksImage,
       ImprimitiveFlag, SetBlockNumbers;

StabBlock := function(G,H)
  //Is subgroup H in LH a stabiliser of a block of imprimitivity of G?
  assert IsIrreducible(G);
  d := Degree(G);
  nb := LMGIndex(G,H);
  if nb gt 1 and d mod nb eq 0 then
    bs := d div nb;
    M := GModule(H);
    CS := [ s : s in Submodules(M) | Dimension(s) eq bs ]; 
    V := VectorSpace(G);
    for sm in CS do
      inj := Morphism(sm,M);
      W := sub< V | [ V!inj(sm.i) : i in [1..Dimension(sm)] ] >;
      if #Orbit(G,W) eq nb then
      //store imprimitivity info
        vprint LMG,1: "found block system";
        module := GModule(G);
        basis := Basis(W);
        blocks := MinBlocks (module, basis);
        SetImprimitiveFlag (G, true);
        SetBlockSystem (module, blocks);
        G`BlockSystem := blocks;
        SetBlocksImage(G, GroupActionOnBlocks(blocks));
        SetBlockNumbers(G, {nb});
        SetBlockSizes(G, {bs});
        return true;
      end if;
    end for;
  end if;
  return  false;
end function;
