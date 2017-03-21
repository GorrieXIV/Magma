freeze;
//

intrinsic WreathProduct(G::GrpPerm, B::GSet) -> GrpPerm,GrpPerm,GrpPerm
{Compute the smallest wreath product W to the block system B of G
 such that G subseteq W. Also return the complement as a subgroup of W.
 The third parameter is a subgroup which is isomorphic to the action
 within a block
}
 
 assert IsTransitive(G);
 n:=Degree(G);
 m:=#B;
 d:=n div m;
 f, subG, ker:= BlocksAction(G, B);
 BB:=Representative(B);
 ReduceGenerators(~subG);
 S:=Stabilizer(G,BB);
 g,relG:=OrbitAction(S,BB);

 Sn:=Sym(n);
 genr:={Sn|};
 gen:={Sn|};
 for a in Generators(relG) do
   b:=a @@ g;
   L:=CycleDecomposition(b);
   L:=[x:x in L|Random(x) in BB];
   b:=Sn ! L;
   Include(~genr,b);
 end for;
 R:=RightTransversal(G, S);
 RR:=[Identity(G):x in [1..#R]];
 B:=SetToSequence(B);
 for i in [1..#R] do
   b:=Random(B[1])^R[i];
   for j in [1..#R] do
     if b in B[j] then
        RR[j]:=R[i];
        break;
     end if;
   end for;
 end for;


 BBB:=Sort(SetToSequence(BB));
 D:=[BBB^x:x in RR];
 for a in Generators(subG) do
   //The action on subG is only conjugate to the action on B!!!!
   aa:=a @@ f;
   L:=[Position(B,x^aa):x in B];
   aa:=Sym(m)! L;//correct action
   L:=CycleDecomposition(aa);
   L:=[x:x in L |#x gt 1];
   newcyc:=[];
   for i in [1..d] do
     for b in L do
       new:={@ @};
       for c in b do
         Include(~new, D[c][i]);
       end for;
       Append(~newcyc, new);
     end for;
   end for;
   b:=Sn ! newcyc;
   Include(~gen,b);
 end for;
 H:=sub<Sn|gen>;
 N:=sub<Sn|genr>;
 W:=sub<Sn|H,N>;
 
 assert G subset W;
 assert #W eq #relG^m*#subG;
 return W,H,N;
end intrinsic;

intrinsic InternalWreathProductSm(G::GrpPerm, B::GSet) -> SeqEnum
{Compute index 2 subgroups of the smallest wreath product W to the block system B of G
 such that G subseteq W}
 
 assert IsTransitive(G);
 n:=Degree(G);
 m:=#B;
 d:=n div m;
 W,H,N:=WreathProduct(G,B);
 NN:=NormalSubgroups(N:OrderEqual:=#N div 2);
 NN:=[x`subgroup:x in NN];
 listW:=[];
 for sub in NN do
  g:=Random({x:x in Generators(N)|not x in sub});
  b:={g^x: x in Generators(H)};
  bb:={x:x in b|#(Support(x) meet Support(g)) eq 0};
  bb:={g*x:x in bb};
  WW:=sub<W|H,sub,bb>;
  assert Index(W,WW) eq 2;
  Append(~listW,<WW,sub>);
 end for;

// assert G subset W;
// assert #W eq #relG^m*#subG;
 return listW;
end intrinsic;

