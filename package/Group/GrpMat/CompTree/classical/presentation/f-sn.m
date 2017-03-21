freeze;

//$Id:: f-sn.m 1112 2008-10-14 02:53:47Z jbaa004                             $:

//  presentation for Z_2 wr Sym (d) 

FSN := function (d)
   F := FreeGroup (3);

   U := F.(1);   // Permutation matrix for the short cycle (1, 2)
   V := F.(2);   // Permutation matrix for the long cycle (1, 2, ..., d)
   L := F.(3);   // Flip-flop matrix diag(-1, 1, 1, ..., 1)

   Rels := []; 
   // use the standard (Coxeter) presentation 
   // of the symmetric group Sym(d) in terms of the short cycle 
   // U = (1, 2) and the long cycle V = (1, 2, ..., d)
   Append (~Rels, 1=U^2);
   Append (~Rels, 1=V^d);
   Append (~Rels, 1=(U*V)^(d-1));
   Append (~Rels, 1=(U, V)^3);
   for i in [2..(d div 2)] do Append (~Rels, 1=(U, V^i)^2); end for;

   // Relations for flip-flop matrix
   Append (~Rels, 1 = L^2);
   Append (~Rels, 1 = (L, L^U));
   Append (~Rels, (L, U^V) = 1);
   Append (~Rels, (L, V * U) = 1);

   return quo < F | Rels >;
end function;

/* index 2 subgroup of Z_2 wr Sym (d) */

Index2 := function (d: SLP := true)
  
   F := FreeGroup (2);
   U := F.(1);   // Permutation matrix for the short cycle (1, 2)
   V := F.(2);   // Permutation matrix for the long cycle (1, 2, ..., d)

   Q := FSN (d);
   u := Q.1; v := Q.2; l := Q.3;
   if IsEven (d) then 
      G := sub<Q | u*l, v*l, l*v>;
      images := [U, V, V * U^2];
   else 
      // use second set of generators since it's much faster for Rewrite 
      // G := sub<Q | u*l, v, l*v*l>; 
      G := sub<Q | u*l, v, u*v*u>; 
      images := [U, V, U * V * U];
   end if; 
   Rewrite (Q, ~G: Simplify:=false);

   tau := hom<G -> F | images>;
   Rels := [tau (r): r in Relations (G)];

   if SLP then 
      S := SLPGroup (2);
      tau := hom <F-> S | [S.1, S.2]>;
      Rels := [LHS (r) * RHS (r)^-1: r in Rels];
      Rels := [tau (r): r in Rels];
      return S, Rels;
   else
      Q := quo <F | Rels>;
      return Q, _;
   end if;

end function;

/* symmetric group of degree d */

PresentationForSn := function (d: SLP := true)
   F := FreeGroup (2);
   U := F.1;  // (1, 2) 
   V := F.2;  // (1,2, ..., d)
   Rels := [];
   Append (~Rels, 1=U^2);
   if d eq 1 then 
      return quo< F | U, V>;
   elif d eq 2 then
      return quo< F | U = V, U^2>;
   else 
      Append (~Rels, 1=V^d);
      Append (~Rels, 1=(U*V)^(d-1));
      Append (~Rels, 1=(U, V)^3);
   end if;
   for i in [2..(d div 2)] do Append (~Rels, 1=(U, V^i)^2); end for;
   if SLP eq false then 
      return quo< F | Rels>, _;
   else 
      S := SLPGroup (2);
      tau := hom <F-> S | [S.1, S.2]>;
      Rels := [LHS (r) * RHS (r)^-1: r in Rels];
      Rels := [tau (r): r in Rels];
      return S, Rels;
   end if;
end function;
