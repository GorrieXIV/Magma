freeze;
 
// functions for constructing a subgroup chain

forward SmallExtension;

/////////////////////////////////////////////////////////////////////////////
function RefineUsingStabilizers(H, G, bound)

  if G eq H then return [ G ]; end if;
  T := G;
  B := H;
  Chain := [ B ];
  while Index(T,B) gt bound and not IsMaximal(T, B) do
     phi := CosetAction(T, B);
     Im := Image(phi);
     blk := MinimalBlocks(Im: Limit := 1);
     stab := Stabilizer(Im, blk);
     B := stab@@phi; 
     Append(~Chain, B);
  end while;
     Append(~Chain, G);
     return Chain;

end function;

/////////////////////////////////////////////////////////////////////////////
intrinsic SubgroupChain(G::GrpPerm, H::GrpPerm) -> SeqEnum[GrpPerm]
{A chain of subgroups from G down to its subgroup H}

   require H subset G:"second argument must be subgroup of first";

   zeit := Cputime();
   chain :=[ H ];
   bound := 2000;

   B := H;
   T := G;
   while B ne T and Index(T, B) gt bound do

      N := Normalizer(G, B);
      vprint DoubleCosets, 1: "Normalizer:", #N;
      if N ne T and #N gt #B then
         Append(~chain, N);
         B := N;
         continue;
      end if;

      N := Centralizer(T, Centre(B));
      vprint DoubleCosets, 1: "Centralizer:", #N;
      if N ne T and #N gt #B then
         Append(~chain, N);
         B := N;
         continue;
      end if;

      N := SmallExtension(T, B, 10000);
      vprint DoubleCosets, 1: "SmallExtension:", #N;
      if #N gt #B then
         Append(~chain, N);
         B := N;
         continue;
      end if;

  end while;
  if G ne chain[#chain] then Append(~chain, G); end if;
  // chain;

  ref_chain := [H];
  for i := 2 to #chain do
    Remove( ~ref_chain, #ref_chain );  
    ref_chain := ref_chain cat 
	    RefineUsingStabilizers(chain[i-1], chain[i], bound);
  end for;
  // ref_chain;
  vprint DoubleCosets, 1: "Time taken to find chain is", Cputime(zeit);
  // [ #chain[1]] cat [ Index(chain[i], chain[i-1]) : i in [2..#chain] ];
  Reverse(~ref_chain);
  return ref_chain;

end intrinsic;


/////////////////////////////////////////////////////////////////////////////
SmallExtension := function (G, H, bound);

    // Extension by a random element

     success := false;
     if IsNormal(G, H) then

        j := 0;
        best := 10^7;
        NN := G;
        while not success and j lt 10 do
           j +:= 1;
           repeat g := Random(G); until g notin H;
           N := sub< G | H, g >;
           if N ne G and Index(N, H) le bound then
              success := true;
              break;
           else
              if Index(N, H) lt best then
                 best := Index(N, H);
                 NN := N;
              end if;
           end if;
        end while;

     if success then 
        return N;
     else 
        return G;
     end if;

   else

  // Self-normalizing subgroup

     success := false;
     j := 0;
     best := 10^7;
     NN := G;
     while not success and j lt 10 do 
        j +:= 1;
        repeat g := Random(G); until g notin H;
         gens := GeneratorsSequence(H);
         for i := 1 to #gens do
            if gens[i]^g notin H then
                x := gens[i]^g;
                N := sub< G | H, x >;
                vprint DoubleCosets, 1: "Order:", #N;
                if N ne G and Index(N, H) le bound then
                   vprint DoubleCosets, 1: "Index:", Index(N, H);
                   success := true;
                   break;
                else
                   if Index(N, H) lt best then
                       best := Index(N, H);
                       NN := N;
                   end if;
                end if;
             end if;
         end for;
         if success then break; end if;
     end while;

   if success then 
        return N;
     else 
        return NN;
   end if;

end if;

end function;

/////////////////////////////////////////////////////////////////////////////

intrinsic DoubleCosetRepresentatives(G::GrpPerm,A::GrpPerm,B::GrpPerm : Chain := 0) -> SeqEnum, SeqEnum
{Compute representatives and lengths of the (A,B)-double cosets in G}

  // We want A to be fairly big
  if Chain cmpeq 0 and 5*#A lt 4*#B then
    b := A;
    a := B;
    switch := true;
    vprint DoubleCosets, 1: "DoubleCosets: exchanged subgroups\n";
  else
    a := A;
    b := B;
    switch := false;
  end if;

  if Index(G,a) eq 1 then
    return [Id(G)],[#G];
  end if;

  zeit := Cputime();
  if Chain cmpeq 0 then
      chain := SubgroupChain(G, a);
  else
      chain := Chain;
  end if;
  vprintf DoubleCosets, 1: "DoubleCosets: subgroup chain orders: %o, time: %o\n", 
			[#x:x in chain], Cputime(zeit);
  R, L := DoubleCosetRepresentatives(G, a, b, chain, switch);
  return R, L;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////

intrinsic NumberOfDoubleCosets(G::GrpPerm, H::GrpPerm, K::GrpPerm) -> RngIntElt
{The number of H-K double cosets in G, where H and K are subgroups of G.
Uses Frobenius' formula, and computes conjugacy classes in G, H and K.}
    require H subset G: "H is not a subset of G";
    require K subset G: "K is not a subset of G";

    cm := ClassMap(G);
    Hfusion := [0:c in Classes(G)];
    Kfusion := [0:c in Classes(G)];
    cl := Classes(H);
    for c in cl do Hfusion[cm(c[3])] +:= c[2]; end for;
    cl := Classes(K);
    for c in cl do Kfusion[cm(c[3])] +:= c[2]; end for;
    cl := Classes(G);
    res  := &+[ Hfusion[i]*Kfusion[i]/cl[i,2] : i in [1..#cl]];
    res  := (#G*res) / (#H*#K);
    fl, res := IsCoercible(Integers(), res);
    assert fl;
    return res;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
