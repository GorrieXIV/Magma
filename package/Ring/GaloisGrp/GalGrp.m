freeze;
//



function MyWreathProduct(B)
// Compute wreath product S_l wr S_m corresponding to given block system
  l:=#Representative(B);
  m:=#B;

  H1:=SymmetricGroup(l);
  H2:=SymmetricGroup(m);
  W := WreathProduct(H1, H2);
  L:= &cat B;
  g:=SymmetricGroup(m*l) ! L;
  return W^g;
end function;




/* Given a list of blocksystems, this function computes the largest group that has them.
   I.e. we compute the intersection of the corresponding wreath products. */
intrinsic IntersectionOfWreathProducts(BlockSysList :: SeqEnum) -> GrpPerm
{BlockSysList is sequence of sequences of sequences of integers, encoding block systems of a permutation group.
 This function returns the largest permutation group having all these block systems.} 

 partl := BlockSysList;

 assert #{&join [Set(b) : b in a] : a in partl} eq 1;

// Trivial case: Only one blocksystem
 if #partl eq 1 then
  return MyWreathProduct(partl[1]);
 end if;

 bs := [#Representative(a) : a in partl];
 ParallelSort(~bs, ~partl);
 rep := [ [b : b in a | 1 in b][1] : a in partl];

// Exactly one minimal partition: recursive approach
 if &and [rep[1] subset rep[j] : j in [2..#rep]] then
  g1 := MyWreathProduct(partl[1]);
  phi := Action(g1,GSet(g1,{Set(a) : a in partl[1]}));
  bg,pi := StandardGroup(Image(phi));
  ll := Labelling(Image(phi));
// Blocksystems of the pi \circ phi image of the starting group
  block_image := [ [ [i : i in [1..#ll] | ll[i] subset a]  : a in partl[j]]  : j in [2..#partl]];
  return (IntersectionOfWreathProducts(block_image) @@ pi) @@ phi;
 end if;

/* General case. Use graphs.
   Represent a block system by a tree 
   Leaves: Points
   Vertices in the 1st layer: Blocks
   Vertex in the 2nd layer: The blocksystem
  
   Total graph: Union on trees. */
  
 n := bs[1] * #partl[1];
 n1 := &+[#a : a in partl]; // Total number of blocks
 n2 := #partl;              // Number of blocksystems 
 es := {};
 bl_sys_label := []; // Vertices that represent a block system
 aux := n + 1;
 for i := 1 to #partl do
  for act_block in partl[i] do 
   for a in act_block do  // The vertex aux represents the block partl[i][j]
    Include(~es,{a,aux}); 
   end for;
   aux := aux + 1;
  end for;
  for j := 1 to #partl[i] do 
   Include(~es,{aux - j,aux});
  end for;
  Append(~bl_sys_label, aux);
  aux := aux + 1;
 end for;  
 gra := Graph<n+n1+n2 | es>;
 ver :=  VertexSet(gra);
 for a in bl_sys_label do
  AssignLabel(~gra, ver!a, a); 
 end for;

 g0 := AutomorphismGroup(gra);
 assert {1} eq {#Orbit(g0,a) : a in bl_sys_label}; // Blocksystems should be invariant because of vertex-coloring.
// g0 := Stabilizer(g0, bl_sys_label); // The group found may swap the block-systems
 phi := Action(g0,GSet(g0,{1..n}));
 bg := Image(phi);
// assert &and [a eq MinimalPartition(bg:Block  := Representative(a)) : a in partl];
 return bg;
end intrinsic;



intrinsic IsEven(G::GrpPerm) -> BoolElt
{Tests if G leq  A_n}

  if forall(x){x : x in Generators(G) |IsEven(x)} then
     return true;
  end if;
  return false;
end intrinsic;

intrinsic WreathProduct(B::GSet :  SubAlt:=false, NormalAlt:=false) ->GrpPerm, GrpPerm, GrpPerm
{Compute wreath product S_l wr S_m corresponding to given block system}

  l:=#Representative(B);
  m:=#B;

  if NormalAlt then
     //"Warning: be careful when applying this (sorting of roots!!!)";
     H1:=AlternatingGroup(l);
  else
     H1:=SymmetricGroup(l);
  end if;

  if SubAlt then
     H2:=AlternatingGroup(m);
  else
     H2:=SymmetricGroup(m);
  end if;

  W,ll,f1:=WreathProduct(H1, H2);
  kern:=sub<W|[Image(x):x in ll]>;
  comp:=Image(f1);
  L:=[];
  for a in B do
    for b in a do
      Append(~L,b);
    end for;
  end for;
  g:=SymmetricGroup(m*l) ! L;
  return W^g, kern^g, comp^g;
end intrinsic;

intrinsic InternalWreathProductSm(B::GSet) ->GrpPerm
{invariant under Sm}

  if assigned B`WreathSm then
     return B`WreathSm;
  end if;

  l:=#Representative(B);
  m:=#B;
  W,ker,H:=WreathProduct(B);
  A:=ker meet AlternatingGroup(m*l);

  U:=sub<W|H,A>;

  B`WreathSm:=U;
  return U;
end intrinsic;

intrinsic InternalWreathProductD(B::GSet) ->GrpPerm
{invariant under D}

  if assigned B`WreathD then
     return B`WreathD;
  end if;

  W:=WreathProduct(B:SubAlt:=true);
  B`WreathD:=W;
  return W;
end intrinsic;

intrinsic InternalWreathProductS1(B::GSet) ->GrpPerm
{invariant under S1}

  if assigned B`WreathS1 then
     return B`WreathS1;
  end if;

  W:=WreathProduct(B:NormalAlt:=true);
  B`WreathS1:=W;
  return W;
end intrinsic;

intrinsic InternalSubgroupSum(G::Grp, H1::Grp, H2::Grp) -> Grp
{H1 and H2 are subgroups of index 2 in G. Computes third subgroup of index 2}

  assert H1 ne H2;
  HH:=H1 meet H2;
  cnt := 0;
  repeat
    h1 := Random(G);
    cnt +:= 1;
  until h1 notin H1 and h1 notin H2;
  vprint GaloisGroup, 3: "used ", cnt , " random elements";

  H3 := sub<G|HH, h1>;
  assert #G/#H3 eq 2;
  assert H3 ne H1 and H3 ne H2;
  return H3;

  Q,f:=quo<G|HH>;
  t:=Subgroups(Q:OrderEqual:=2);
  t:=[x`subgroup:x in t];
  t:=[x:x in t| x ne f(H1) and x ne f(H2)];
  assert #t eq 1;
  return t[1] @@f;

end intrinsic;

intrinsic InternalWreathProductDSm(B::GSet) ->GrpPerm
{invariant under DSm}

  if assigned B`WreathDSm then
     return B`WreathDSm;
  end if;


  W:=WreathProduct(B);
  W1:=InternalWreathProductD(B);
  W2:=InternalWreathProductSm(B);
  // W/(W1 meet W2) has index 4. Compute third intermediate group

  B`WreathDSm:=InternalSubgroupSum(W,W1,W2);
  return B`WreathDSm;
end intrinsic;

intrinsic InternalWreathProductS2(B::GSet) ->GrpPerm
{invariant under S2}

  if false and assigned B`WreathS2 then
     return B`WreathS2;
  end if;

  W:=WreathProduct(B);
  W1:=WreathProduct(B:NormalAlt:=true);
  L:=[SetToSequence(x):x in B];
  g:=&*[W ! (x[1],x[2]):x in L]; //is odd for all blocks! 
  U:=sub<W|W1,g>;
  B`WreathS2:=U;

  return U;
end intrinsic;

