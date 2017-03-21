freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                   GENUS SYMBOLS FOR LATTICES                   //
//                          David Kohel                           // 
//                      Created January 2000                      //
//                     Last modified May 2000                     //
//                                                                // 
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////

declare type SymGen;
declare attributes SymGen:
   Representative,
   IsSpinor,
   LocalGenera,
   Representatives;

declare type SymGenLoc;
declare attributes SymGenLoc:
   Prime,       
   ScaleFactors,
   JordanComponents;

////////////////////////////////////////////////////////////////////
//                     Accessory Function                         //
////////////////////////////////////////////////////////////////////

function UnitSquareClass(u,p)
   // PRE: u is a unit mod p and p is prime 
   // POST: Returns the smallest positive integer in the 
   // same square class as u.
   if p eq 2 then
     return (u mod 8);
   elif KroneckerSymbol(u,p) eq 1 then
     return 1;
   else
     c := 2;
     while KroneckerSymbol(c,p) eq 1 do
        c +:= 1;
     end while;
     return c;
   end if;
end function;

////////////////////////////////////////////////////////////////////
//                                                                // 
//                          Coercion                              // 
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(G::SymGen,S::.) -> BoolElt, .
   {internal}
   return false, "No coercion possible";
end intrinsic;

intrinsic IsCoercible(G::SymGenLoc,S::.) -> BoolElt, .
   {internal}
   return false, "No coercion possible";
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////

forward JordanDecomposition;

intrinsic Genus(G::SymGen) -> SymGen
   {The genus of G}
   if not G`IsSpinor then
      return G;
   end if;
   H := HackobjCreateRaw(SymGen);
   H`Representative := G`Representative;
   H`IsSpinor := false;
   H`LocalGenera := G`LocalGenera;
   return H;
end intrinsic;

intrinsic Genus(L::Lat) -> SymGen
   {The genus of L.}
   G := HackobjCreateRaw(SymGen);
   G`Representative := L;
   G`IsSpinor := false;
   S := [ ];    
   for p in [ q[1] : q in Factorization(2*Determinant(L)) ] do
      Gp := HackobjCreateRaw(SymGenLoc);
      Gp`Prime := p;
      J := pAdicDiagonalization(L,p);
      Gp`JordanComponents, Gp`ScaleFactors 
         := JordanDecomposition(J,p);
      Append(~S,Gp); 
   end for;
   G`LocalGenera := S; 
   return G;
end intrinsic;

intrinsic SpinorGenus(L::Lat) -> SymGen
   {The spinor genus of L}
   G := HackobjCreateRaw(SymGen);
   G`Representative := L;
   G`IsSpinor := true;
   S := [ ];    
   for p in [ q[1] : q in Factorization(2*Determinant(L)) ] do
      Gp := HackobjCreateRaw(SymGenLoc);
      Gp`Prime := p;
      J := pAdicDiagonalization(L,p);
      Gp`JordanComponents, Gp`ScaleFactors 
         := JordanDecomposition(J,p);
      Append(~S,Gp); 
   end for;
   G`LocalGenera := S; 
   return G;
end intrinsic;

intrinsic SpinorGenera(G::SymGen) -> SeqEnum
   {The spinor genera in the genus G}
   if G`IsSpinor then
      return [ G ];
   end if;
   S := SpinorGenerators(G);
   genera := [ ]; 
   V := VectorSpace(GF(2),#S);
   for e in V do
      I := [ k : k in [1..#S] | e[k] ne 0 ]; 
      L := G`Representative;
      for k in I do
         L := CoordinateLattice(Neighbors(L,S[k])[1]);
      end for;
      H := HackobjCreateRaw(SymGen);
      H`Representative := L;
      H`IsSpinor := true;
      H`LocalGenera := G`LocalGenera;
      Append(~genera,H);
   end for;
   return genera;
end intrinsic;

function JordanDecomposition(L,p)
   n := Rank(L);
   M := GramMatrix(L);
   if p ne 2 then
      D := [ M[i,i] : i in [1..n] ];
      F := [ ];
      ScaleVals := {@ Valuation(a,p) : a in D @};
      for i in ScaleVals do
         q := p^i; 
         Di := [ a/q : a in D | Valuation(a,p) eq i ];
         Li := LatticeWithGram(
            DiagonalMatrix(MatrixAlgebra(Integers(),#Di),Di) );
         Append(~F,Li);
      end for;   
      return F, [ p^i : i in ScaleVals ];
   end if;
   F := [ ];
   I := [ IntegerRing() | ]; 
   i := 1;
   while i le n do
      if i lt n and M[i,i+1] ne 0 then
         k := Valuation(M[i,i+1],2);
         q := 2^k;
         r := Max([0] cat [ j : j in [1..#I] | I[j] le k ]);
         Insert(~I,r+1,k);
         Insert(~F,r+1,
            LatticeWithGram( MatrixAlgebra(Integers(),2)!
               [ M[i,i]/q, M[i,i+1]/q, M[i+1,i]/q, M[i+1,i+1]/q ] ) );
         i +:= 2; 
      else
         k := Valuation(M[i,i],2);
         q := 2^k;
         Append(~I,k);
         Append(~F,
            LatticeWithGram( MatrixAlgebra(Integers(),1)!
               [ IntegerRing() | M[i,i]/q ]) );
         i +:= 1; 
      end if;
   end while;
   ScaleVals := {@ i : i in I @};
   return [ DirectSum([ F[j] : j in [1..#F] | I[j] eq i ]) 
      : i in ScaleVals ], [ 2^i : i in ScaleVals ];
end function;

////////////////////////////////////////////////////////////////////
//                                                                //
//                           Printing                             //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Print(G::SymGenLoc)
   {internal}
   printf "%o-adic genus of %o", G`Prime, Representative(G);
end intrinsic;

intrinsic Print(G::SymGen)
   {internal}
   if G`IsSpinor then
      printf "Spinor genus of %o", G`Representative;
   else
      printf "Genus of %o", G`Representative;
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                        Equality testing                        //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic 'eq' (G1::SymGenLoc,G2::SymGenLoc) -> BoolElt
   {}
   return G1`Prime eq G2`Prime and
          G1`ScaleFactors eq G2`ScaleFactors and 
          G1`JordanComponents eq G2`JordanComponents;
end intrinsic;

intrinsic 'eq' (G1::SymGen,G2::SymGen) -> BoolElt
   {}
   spinor := G1`IsSpinor;
   require G2`IsSpinor eq spinor :
      "Arguments must be both genera or both spinor genera.";
   P := [ L`Prime : L in G1`LocalGenera ];
   Q := [ L`Prime : L in G2`LocalGenera ];
   if P ne Q then return false; end if;
   if not &and[ G1`LocalGenera[k] eq 
                G2`LocalGenera[k] : k in [1..#P] ] then
      return false;
   end if; 
   if spinor then
      if assigned G2`Representatives then
         L := G1`Representative;
         for M in Representatives(G2) do
            if IsIsometric(L,M) then return true; end if;
         end for;
         return false;
      else 
         L := G2`Representative;
         for M in Representatives(G1) do
            if IsIsometric(L,M) then return true; end if;
         end for;
         return false;
      end if; 
   end if;
   return true;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                   Attribute Access Functions                   //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic InternalRepresentative(G::SymGen) -> Lat
   {A representative lattice of G.}
   require assigned G`Representative : "No representative is known";
   return G`Representative;
end intrinsic;

intrinsic IsGenus(G::SymGen) -> BoolElt
   {True if and only if G is a genus.}
   return not G`IsSpinor;
end intrinsic;

intrinsic IsSpinorGenus(G::SymGen) -> BoolElt
   {True if and only if G is a spinor genus.}
   return G`IsSpinor;
end intrinsic;

intrinsic Primes(G::SymGen) -> RngIntElt
   {The primes of the local genus symbols.}
   return [ Gp`Prime : Gp in G`LocalGenera ];
end intrinsic;

intrinsic Prime(G::SymGenLoc) -> RngIntElt
   {The prime of the genus symbol.}
   return G`Prime;
end intrinsic;

intrinsic Determinant(G::SymGenLoc) -> RngIntElt
   {The p-adic determinant of G.}
   p := G`Prime;
   if p eq 2 then
      return ( &*[ Determinant(J) mod 8 : 
         J in G`JordanComponents ] mod 8 ) * &*G`ScaleFactors;  
   else
      // Reduce the unit part to canonical square class.
      return UnitSquareClass( &*[ Determinant(J) mod p : 
         J in G`JordanComponents ] mod p ) * &*G`ScaleFactors;  
   end if;
end intrinsic;

intrinsic Determinant(G::SymGen) -> RngIntElt
   {The determinant of G.}
   return Determinant(G`Representative);
end intrinsic;

intrinsic Dimension(G::SymGen) -> RngIntElt
   {The rank of the genus.}
   return Rank(Representative(G));
end intrinsic;

intrinsic Rank(G::SymGen) -> RngIntElt
   {The rank of the genus.}
   return Rank(Representative(G));
end intrinsic;

intrinsic Dimension(G::SymGenLoc) -> RngIntElt
   {The rank of the genus.}
   return &+[ Rank(N) : N in G`JordanComponents ];
end intrinsic;

intrinsic Rank(G::SymGenLoc) -> RngIntElt
   {The rank of the genus.}
   return &+[ Rank(N) : N in G`JordanComponents ];
end intrinsic;

/*
intrinsic Dimension(G::SymGenLoc,k::RngIntElt) -> RngIntElt
   {The dimension of the local genus symbol.}
   require k in [1..#G] : "Invalid range for argument 2";
   return Rank(G`JordanComponents[k]);
end intrinsic;

intrinsic Dimensions(G::SymGenLoc) -> RngIntElt
   {The dimension of the local genus symbol.}
   return [ Rank(N) : N in G`JordanComponents ];
end intrinsic;

intrinsic ScaleFactor(G::SymGenLoc,k::RngIntElt) -> RngIntElt
   {The scale factor of the k-th Jordan component.}
   require k in [1..#G] : "Invalid range for argument 2";
   return G`ScaleFactors[k];
end intrinsic;

intrinsic ScaleFactors(G::SymGenLoc) -> RngIntElt
   {The scale factors of the Jordan components.}
   return G`ScaleFactors;
end intrinsic;

intrinsic Sign(G::SymGenLoc,k::RngIntElt) -> SeqEnum
   {The sign of the k-th factor.}
   require k in [1..#G] : "Invalid range for argument 2";
   p := G`Prime;
   D := Determinant(G`JordanComponents[k]);
   return KroneckerSymbol(D,p);
end intrinsic;

intrinsic Signs(G::SymGenLoc) -> SeqEnum
   {The signs of the Jordan components.}
   p := G`Prime;
   return [ KroneckerSymbol(Determinant(J),p) 
      : J in G`JordanComponents ];
end intrinsic;

intrinsic JordanComponent(G::SymGenLoc,k::RngIntElt) -> SeqEnum
   {The k-th Jordan component of G.}
   require k in [1..#G] : "Invalid range for argument 2";
   return G`JordanComponents[k];
end intrinsic;

intrinsic JordanComponents(G::SymGenLoc) -> SeqEnum
   {The Jordan components of G.}
   return G`JordanComponents;
end intrinsic;
*/

intrinsic InternalRepresentative(G::SymGenLoc) -> Lat
   {A canonical representative for the p-adic genus, in Jordan form.}
   return DirectSum( [ ScaledLattice(
      G`JordanComponents[i], G`ScaleFactors[i] ) 
         : i in [1..#G`ScaleFactors] ]);
end intrinsic;

/*
intrinsic NumberOfComponents(G::SymGenLoc) -> RngIntElt
   {The number of Jordan components.}
   return #G`ScaleFactors;
end intrinsic;

intrinsic '#'(G::SymGenLoc) -> RngIntElt
   {The number of Jordan components.}
   return #G`ScaleFactors;
end intrinsic;

intrinsic LocalGenus(G::SymGen,p::RngIntElt) -> SeqEnum
   {The local genus symbol of G at p.}
   prms := Primes(G);
   require p in prms : 
      "Argument 2 is not a divisor of the determinant";
   return G`LocalGenera[Index(prms,p)];
end intrinsic;
*/

intrinsic LocalGenera(G::SymGen) -> SeqEnum
   {The local genus symbols.}
   return G`LocalGenera;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                         Functionality                          //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Representatives(G::SymGen) -> SeqEnum
   {A sequence of representatives for the genus of G.}  
   if not assigned G`Representatives then
      if G`IsSpinor then
         G`Representatives := SpinorRepresentatives(G`Representative);
      else 
         G`Representatives := GenusRepresentatives(G`Representative);
      end if;
   end if;
   return G`Representatives;
end intrinsic;

intrinsic '#'(G::SymGen) -> RngIntElt
   {The number of genus representatives.}
   return #Representatives(G);
end intrinsic;

