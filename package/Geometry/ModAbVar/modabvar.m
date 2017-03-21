freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: modabvar.m
   DESC: Basic ModAbVar functionality.

   2004-10-24: Added Tseno Tselkov's update to IsIsogenous and MinimalIsogeny.
      
 ***************************************************************************/


import "complements.m":
   FindHomologyDecompositionOfSubspaceUsingDecomposition;

import "endo_alg.m":
   Decide_If_Quaternionic;

import "elt.m": 
   Create_ModAbVarElt,
   Create_ModAbVarElt_Zero;

import "homology.m": 
   BasisChange_Rational_to_Lattice,
   Create_ModAbVarHomol,
   Create_ModAbVarHomol_Quotient,
   Create_ModAbVarHomol_Subspace,
   HomologySignZeroDimension;

import "inner_twists.m":
   Compute_Inner_Twists_Over_K;

import "linalg.m":
   HorizontallyStackMatrices,
   Intersect_Vector_Space_With_Lattice,
   LatticeDirectSum,
   MakeLattice,
   RestrictionOfScalars,
   VerticallyStackMatrices;

import "misc.m":
   FactorPrint,
   NoSpaces,
   OddPart;

import "morphisms.m": 
   Copy_MapModAbVar,
   Create_MapModAbVar,
   Create_MapModAbVar_MultiplyToMorphism;

import "rings.m": 
   CC, QQ, Qbar, RR, 
   CommonFieldOfDefinition,
   CommonBaseRing,
   RingName,
   IsDefnField,
   IsNumberField,
   OverCompositum,
   OverRing;

import "torsion.m":
   ComputeSize;

forward 
   AllCharactersTrivial,
   Can_Compute_Inner_Twists,
   Copy_ModAbVar,
   Create_ModAbVar,
   Create_ModAbVar_AssociatedToModularSymbolsSubspace,
   Create_ModAbVar_ModSym,
   InCreation,
   MStoHom_Coercion,
   Name,
   SetName,
   ShortDesc,
   Verbose;



declare verbose ModAbVar, 4;

declare type ModAbVar [ModAbVarElt];

declare attributes ModAbVar:
   base_ring,              // ring over which A is defined
   associated_abvar_over_Q, // if A is a base extension of something over Q, this is it.
   component_group_order,  // order of component group of A, when base char p
   conductor,		   // conductor of A as an abvar
   dimension,		   // dimension of A as an abvar
   endomorphism_ring,	   // ring over Z of endomorphisms of A
   endomorphism_algebra,   // algebra over Q of endomorphisms of A
   hecke_algebra,          // hecke algebra
   field_of_definition,	   // a minimal (as far as we know) field of defn of A
   frobpolys,              // cached charpolys of frobenius.
   homology,		   // the real, rational, and integral homology of A
   inner_twists,           
   weights,                // weights of modular forms spaces corr. to A
   num_rational_points,    // number of rational points.
   cm_twists,
   isogeny_decomp,         // full decomposition of A up to isogeny; a refinement
                           // of isogeny_newform_decomp. 
   tamagawa_numbers,       // Tamagawa numbers 
   decomposition,          // similar to isogeny_decomp, but subvarieties and different format.
   is_simple,	   // true <==> A is simple up to isogeny
   is_selfdual,	           // true if A is known to be self-dual, e.g., A = JZero(N), JOne(N), or JH(N).
   is_Af,                  // true if and only if A is an abvar of the form A_f.
   is_quaternionic,        
   is_only_motivic,        // attached to modular forms of weight bigger than 2.
   newform_number,
   newform, 
   modular_param,	   // if a surj. map from modular jacobian
			   // to A is known, it is stored here.
   modular_embedding,	   // if a finite-kernel map to a modular jacobian
			   // is known, it is stored here.
   modular_degree,
   embeddings,             // * A list of morphisms from A into abelian varieties,
                           //   which are used in making sense of intersections, sums, etc.
   only_maximal_newform_blocks,  // if in newform decomp of A the newform blocks are as big as possible.
   level,                  
   point_precision,        // used when deciding equality of points in real homology mod integral homology. 
   name;		   // a helpful name to remember what A is, e.g.,"JZero(37)"
   

intrinsic JZero(N::RngIntElt : Sign := 0) -> ModAbVar
{Create the modular abelian variety J_0(N), i.e., the Jacobian
 of the modular curve X_0(N).}
   return JZero(N,2 : Sign := Sign);
end intrinsic;

intrinsic JZero(N::RngIntElt, k::RngIntElt, Sign::RngIntElt) -> ModAbVar
{Create the modular abelian variety J_0(N) of weight k>=2.}
   requirege k, 2;
   require Sign in {-1,0,1} : 
       "Optional sign must be -1, 0, or 1."; 
   return JZero(N,k:Sign := Sign);
end intrinsic;

intrinsic JZero(N::RngIntElt, k::RngIntElt: Sign := 0) -> ModAbVar
{Create the modular abelian variety J_0(N) of weight k>=2.}
   Verbose("JZero",Sprintf("Creating JZero(%o,%o,%o).",N,k,Sign),"");
   requirege k, 2;
   if IsOdd(k) then
      return ZeroModularAbelianVariety(k);
   end if;
   require Sign in {-1,0,1} : 
       "Optional sign must be -1, 0, or 1."; 
   name := Sprintf("JZero(%o%o)",N,k eq 2 select "" else Sprintf(",%o",k));
   J := Create_ModAbVar_ModSym(name, ModularSymbols(N,k,Sign));
   J`is_selfdual := true;
   J`weights := {k};
   return J;
end intrinsic;

intrinsic JOne(N::RngIntElt : Sign := 0) -> ModAbVar
{Same as JOne(N,2)}
   return JOne(N,2 : Sign := Sign);
end intrinsic;

intrinsic JOne(N::RngIntElt, k::RngIntElt, Sign::RngIntElt) -> ModAbVar
{Create the modular abelian variety J_1(N) of weight k, i.e., the Jacobian
of the modular curve X_1(N).}
   requirege k,2;
   return JOne(N,k : Sign := Sign);
end intrinsic;

intrinsic JOne(N::RngIntElt, k::RngIntElt: Sign := 0) -> ModAbVar
{"} // "
/* SOLUTION:
    Create JOne as below, then make *another* modular abelian variety 
    which has the correct lattice, but is not associated to modular 
    symbols.   That is, make prod J(eps) and construct JOne(N)
    as an abvar isogenous to J(eps) with this modular param.
*/

   Verbose("JOne",Sprintf("Creating JOne(%o,%o,%o).",N,k,Sign),"");

   requirege k,2;
   J := Js(N, k: Sign := Sign);
   if Dimension(J) eq 0 then
      name := Sprintf("JOne(%o)",N); 
      SetName(J,name);
      J`weights := {k};
      return J;
   end if;

   // Find sub-lattice L of H_1(J,Z) generated by images of integral
   // Modular symbols for Gamma1(N).  These are symbols of the
   // form X^i*Y^(k-2-i){0,gamma(0)}, where i=0,...,k-2 and
   // gamma runs through generators for Gamma1(N).  Fortunately,
   // Helena Verrill implemented an excellent algorithm for listing
   // a quite small generating set for Gamma1(N), so it is reasonable
   // to use this algorithm in practice!

   t := Cputime();
   R := PolynomialRing(QQ,2);
   X := R.1;
   Y := R.2;
   Gamma1Gens := Generators(Gamma1(N));
   symbols := [ <X^i*Y^(k-2-i), [Cusps()|0,g*0]> : 
                               i in [0..k-2], g in Gamma1Gens];

   L := MakeLattice([ModularSymbolToRationalHomology(J,s) : s in symbols]);

   embed_morphism := IdentityMatrix(QQ,Dimension(Homology(J)));
   name := Sprintf("JOne(%o%o)",N,k eq 2 select "" else Sprintf(",%o",k));
   K := QQ;
   R := QQ;
   H := Create_ModAbVarHomol(L);
   J1N := Create_ModAbVar(name, H, K, R, <J, embed_morphism, false>);
   J1N`weights := {k};
   J1N`is_selfdual := true;
   return J1N;
end intrinsic;

intrinsic JH(N::RngIntElt, gens::[RngIntElt] : Sign := 0) -> ModAbVar
{Create the Jacobian of the curve X_H(N), i.e. the quotient of X_1(N)
by a subgroup H of the integers modulo N generated by gens};
   requirege N,1;
   require #[d : d in gens | GCD(N,d) ne 1] eq 0 : 
                   "Arguments 1 and 2 must be coprime.";
    return JH(N, 2, gens : Sign := Sign);
end intrinsic;

intrinsic JH(N::RngIntElt, k::RngIntElt, gens::[RngIntElt]: Sign:=0) -> ModAbVar
{Create the Jacobian of the curve X_H(N), i.e. the quotient of X_1(N)
by a subgroup H of the integers modulo N generated by gens};
   requirege N,1;
   require #[d : d in gens | GCD(N,d) ne 1] eq 0 : 
                   "Arguments 1 and 2 must be coprime.";
   require k ge 2 : 
       "Argument 2 must be an integer >= 2.";
   require Sign in {-1,0,1} : 
       "Optional sign must be -1, 0, or 1."; 

   F := CyclotomicField(EulerPhi(N));
   D := DirichletGroup(N,F);
   X := [ModularSymbols(MinimalBaseRingCharacter(eps),k,Sign) : 
                  eps in GaloisConjugacyRepresentatives(D) | 
                    #[d : d in gens | Evaluate(eps,d) ne 1] eq 0];
   name := Sprintf("J_H(%o)",N);
   J := Create_ModAbVar_ModSym(name, X);
   J`weights := {k};
   J`is_selfdual := true;
   return J;
end intrinsic;

intrinsic JH(N::RngIntElt, d::RngIntElt : Sign := 0) -> ModAbVar
{Create the Jacobian of the curve X_H(N), i.e. the quotient of X_1(N)
by a subgroup H of the integers modulo N such that ((Z/N Z)^*)/H has order d}
   requirege d, 1;
   require EulerPhi(N) mod d eq 0 : 
           "Argument 2(",d,") must divide",EulerPhi(N);
    return JH(N, 2, d : Sign := Sign);
end intrinsic;

intrinsic JH(N::RngIntElt, k::RngIntElt, d::RngIntElt : Sign := 0) -> ModAbVar
{Create the Jacobian of the curve X_H(N), i.e. the quotient of X_1(N)
by a subgroup H of the integers modulo N such that ((Z/N Z)^*)/H has order d}
   requirege d, 1;
   requirege k, 2;
   require EulerPhi(N) mod d eq 0 : 
           "Argument 2(",d,") must divide",EulerPhi(N);
   ord := EulerPhi(N) div d;
   if ord eq 1 then
      return Js(N, k  :  Sign := Sign);
   elif ord eq EulerPhi(N) then
      return JZero(N, k : Sign := Sign);      
   end if;
   U,phi := UnitGroup(IntegerRing(N));
   for u in U do
      if Order(u) eq ord then
         return JH(N, k, [Integers()|phi(u)] : Sign := Sign);
      end if;
   end for;
   msg := Sprintf("There is no cyclic subgroup of (Z/%oZ)^* of order %o\n", N, ord);
   require false : msg;
end intrinsic;

intrinsic Js(N::RngIntElt, k::RngIntElt :  Sign := 0) -> ModAbVar
{A modular abelian variety that is Q-isogenous to the weight k version
of J_1(N).}
   requirege k, 2;
   name := Sprintf("Js(%o%o)",N,k eq 2 select "" else Sprintf(",%o",k));

   F := CyclotomicField(EulerPhi(N));
   D := DirichletGroup(N,F);
   X := [ModularSymbols(MinimalBaseRingCharacter(eps),k) : 
                        eps in GaloisConjugacyRepresentatives(D) | 
                        DimensionCuspForms(eps,k) ne 0 and 
                        (IsEven(eps) and IsEven(k)) or (IsOdd(eps) and IsOdd(k))];
   if #X eq 0 then
      return JZero(N, k : Sign := Sign);
   end if;
   J := Create_ModAbVar_ModSym(name, X);
   J`weights := {k};
   return J;
end intrinsic;


intrinsic Js(N::RngIntElt : Sign := 0) -> ModAbVar
{Same as Js(N,2)}
   return Js(N,2 : Sign := Sign);
end intrinsic;

intrinsic Newform(A::ModAbVar) -> ModFrmElt
{A newform f such that A is isogenous to the newform abelian variety A_f. } 
   if not assigned A`newform then
      Verbose("Newform",Sprintf("Finding newform attached to %o.",A),"");
      t, Af := IsAttachedToNewform(A);
      require t : "Argument 1 must be attached to a newform.";
      e := DirichletCharacter(ModularSymbols(Af)[1]);
      S := CuspForms(e,Weight(ModularSymbols(Af)[1]));
      f := Newform(S,Af`newform_number);
      A`newform := f;
   end if;
   return A`newform;
end intrinsic;


intrinsic ModularAbelianVariety(f::ModFrmElt) -> ModAbVar
{The abelian variety attached to the newform f.}
   require IsNewform(f) : "Argument 1 must be a newform.";
   Verbose("ModularAbelianVariety",Sprintf("Finding modular abelian variety attached to %o.",f),"");
   A := Create_ModAbVar_AssociatedToModularSymbolsSubspace("Af", ModularSymbols(f));
   A`weights := {Weight(f)};
   A`newform := f;
   return A;
end intrinsic;

intrinsic ModularAbelianVariety(eps::GrpDrchElt : Sign := 0) -> ModAbVar
{Same as ModularAbelianVariety(eps,2)}
   Verbose("ModularAbelianVariety",
     Sprintf("Modular abelian variety with character %o and sign %o.",eps, Sign),"");
   eps := MinimalBaseRingCharacter(eps);
   return ModularAbelianVariety(CuspidalSubspace(ModularSymbols(eps,2,Sign)));
end intrinsic;

intrinsic ModularAbelianVariety(eps::GrpDrchElt, k::RngIntElt : 
      Sign := 0) ->  ModAbVar
{The abelian variety associated to eps.  This corresponds to the space
of modular forms of weight k and character any Galois conjugate of eps.}
   eps := MinimalBaseRingCharacter(eps);
   Verbose("ModularAbelianVariety",
     Sprintf("Modular abelian variety of weight %o with character %o and sign %o.",k,eps, Sign),"");
   return ModularAbelianVariety(CuspidalSubspace(ModularSymbols(eps,k,Sign)));
end intrinsic;

intrinsic ModularAbelianVariety(X::[ModFrm] : Sign := 0) -> ModAbVar
{The abelian variety attached to the sequence X of modular forms spaces. }

   Verbose("ModularAbelianVariety",
     Sprintf("Modular abelian variety associated to modular forms spaces %o.",X), "");
   if #X eq 0 then
      return ZeroModularAbelianVariety();
   end if;
   return ModularAbelianVariety([ModularSymbols(M, Sign): M in X]);
end intrinsic;

intrinsic ModularAbelianVariety(M::ModFrm : Sign := 0) -> ModAbVar
{The abelian variety attached to the modular forms space M.}
   Verbose("ModularAbelianVariety",
     Sprintf("Modular abelian variety associated to %o.",M),"");
   return ModularAbelianVariety(ModularSymbols(M, Sign));
end intrinsic;


intrinsic ModularSymbols(A::ModAbVar) -> SeqEnum
{A sequence of spaces of modular symbols associated to A.}
   Verbose("ModularSymbols", 
     Sprintf("Modular symbols spaces attached to %o.",A),"");
   if IsAttachedToModularSymbols(A) then
      return (A`homology)`modsym;
   end if;
   if Type(BaseRing(A)) eq FldRat then
      return &cat[ModularSymbols(Af[1]) : Af in Factorization(A)];
   end if;
   require false :  "Argument 1 must be associated to modular symbols or defined over Q.";
end intrinsic;


intrinsic ModularAbelianVariety(M::ModSym) -> ModAbVar
{The abelian variety attached to the modular symbols space M.} 
   Verbose("ModularAbelianVariety", 
     Sprintf("Modular abelian variety attached to %o.",M),"");

   if not IsMultiChar(M) then
      eps := DirichletCharacter(M);   
      require BaseField(M) cmpeq BaseRing(Parent(MinimalBaseRingCharacter(eps))) :
           "Must have base field equal the field generated the character values.";
   end if;
   return Create_ModAbVar_AssociatedToModularSymbolsSubspace("",M);
end intrinsic;

intrinsic ModularAbelianVariety(X::[ModSym]) -> ModAbVar
{The abelian variety attached to the sequence X of modular 
 symbols spaces.}
   Verbose("ModularAbelianVariety", 
     Sprintf("Modular abelian variety attached to %o.",X),"");
   if #X eq 0 then
      return ZeroModularAbelianVariety();
   end if;
   sign := Sign(X[1]);
   require #Set([Sign(M) : M in X]) eq 1 : 
               "The signs must all be the same.";
   Y := [];
   has_multichar := &or[IsMultiChar(M) : M in X];
   if has_multichar and #X gt 1 then
      X1 := [M : M in X | not IsMultiChar(M)];
      X2 := [M : M in X | IsMultiChar(M)];
      A1 := ModularAbelianVariety(X1);
      A2 := [ModularAbelianVariety(M) : M in X2];
      A := DirectSum([A1] cat A2);
      return A;
   end if;

   for M in X do 
      require Sign(M) eq sign : 
            "The modular symbols spaces must all have the same sign.";
      require Type(BaseField(M)) in {FldRat, FldCyc} : 
            "Each modular symbols space must be defined over"*
             " the rationals or a cyclotomic field.";
      if IsMultiChar(M) then
         for MM in MultiSpaces(M) do
            Append(~Y,CuspidalSubspace(MM));
         end for;
      else
         eps := DirichletCharacter(M);   
         require BaseField(M) cmpeq 
              BaseRing(Parent(MinimalBaseRingCharacter(eps))) :
             "Each modular symbols space must have base field the " *
             "field generated the character values.";
         Append(~Y,CuspidalSubspace(M));
      end if;
   end for;
   name := "";
   if #Y eq 1 and Y[1] eq CuspidalSubspace(AmbientSpace(Y[1])) then
      eps := DirichletCharacter(Y[1]);
      if IsTrivial(eps) then
         name := Sprintf("JZero(%o)",Level(Y[1]));
      else
         name := Sprintf("J[%o,%o]", Level(Y[1]), NoSpaces(Sprintf("%o",Eltseq(eps))));
      end if;
   end if;
   A := Create_ModAbVar_ModSym(name, Y);
   if has_multichar then
      /* Because one of the modular symbols spaces is a multicharacter space,
         the lattice that defines A is not correct.  What we have to do
         is construct a B which has the correct lattice, which is the 
         sublattice of the lattice that defines A generated by integral
         basis for each homology space, and make the modular embedding the 
         natural inclusion map to A.

         Also, not that by what we did above, we may assume at this point
         that the sequence Y is just the factors of a single multicharacter
         space.
       */
       assert #X eq 1;
       t := Cputime();
       I := IntegralBasis(CuspidalSubspace(X[1]));
       G := [MStoHom_Coercion(A,MultiTuple(x)) : x in I];
       L := MakeLattice(G);
       embed_morphism := IdentityMatrix(QQ,Dimension(Homology(A)));
       K := QQ;
       R := QQ;
       H := Create_ModAbVarHomol(L);
       H`sign := sign;
       B := Create_ModAbVar(name, H, K, R, <A, embed_morphism, false>);
       B`weights := {Weight(X[1])};
       return B;

   end if;
   return A;
end intrinsic;


intrinsic ZeroModularAbelianVariety(k::RngIntElt) -> ModAbVar
{The zero-dimensional abelian variety of weight k.}
   requirege k,2;
   A := ModularAbelianVariety(ZeroSubspace(ModularSymbols(1,k)));
   SetName(A,"ZERO");
   return A;
end intrinsic;

intrinsic ZeroModularAbelianVariety() -> ModAbVar
{The zero-dimensional abelian variety.}
   A := ZeroModularAbelianVariety(2);
   SetName(A,"ZERO");
   return A;
end intrinsic;

intrinsic ZeroSubvariety(A::ModAbVar) -> ModAbVar
{Creates the zero subvariety of A}
   Verbose("ZeroSubvariety",
     Sprintf("Creating zero subvariety of %o.",A),"");

   e := ModularEmbedding(A);
   J := Codomain(e);
   V := RationalHomology(A);
   W := sub<V|[V!0]>;
   H,embed := Create_ModAbVarHomol_Subspace(Homology(A),W);
   emb := embed*Matrix(e);
   Z := Create_ModAbVar("ZERO", H, FieldOfDefinition(A), BaseRing(A), 
                 <J, emb, Transpose(emb)>);
   return Z;
end intrinsic;

intrinsic DefinesAbelianSubvariety(A::ModAbVar, V::ModTupFld) -> 
                            BoolElt, ModAbVar
{True if and only if the subspace V of rational homology defines an abelian
subvariety of A.  If true, also returns the abelian subvariety.}
   require IsField(BaseRing(A)) : "Argument 1 must be over a field.";
   require Characteristic(BaseRing(A)) eq 0 : "Argument 1 must be over a field of characteristic 0.";
   require Type(BaseRing(V)) eq FldRat : "Argument 2 must be over the rational numbers.";
   require V subset RationalHomology(A) : 
              "Argument 1 must be contained in the rational homology of argument 1.";
   if Dimension(V) eq 0 then
      return ZeroSubvariety(A);
   end if;
      
   D, SUM, full_only := FindHomologyDecompositionOfSubspaceUsingDecomposition(A, V);
   if #D eq 0 then
      return false, _;
   end if;
   return true, SUM;
end intrinsic;


function CremonaCurve(s)
   return true, EllipticCurve(CremonaDatabase(),s);
/*   for i in [1..#s] do
      if s[i] in {"k", "K"} and i lt #s and not (s[i+1] in {"k","K"}) then
         if s[i+1] ne "2" then
            return false;
         end if;
     end if;
   end for;
*/
end function;

function CreateFromLabel(s, Cremona, sign)
   Verbose("ModularAbelianVariety", Sprintf(
       "Creating modular abelian variety from label '%o'.",s), 
       Sprintf("sign = %o, Cremona = %o", sign, Cremona));
   if Cremona then
      t, E := CremonaCurve(s);
      if t then
         return true, ModularAbelianVariety(E: Sign := sign);
      end if;
   end if;
   M := ModularSymbols(s, sign);
   A := Create_ModAbVar_AssociatedToModularSymbolsSubspace(s,M);
   return true, A;
end function;

intrinsic ModularAbelianVariety(s::MonStgElt : 
    Cremona := false  ) -> ModAbVar
{The abelian variety defined by the string s.}
   t, A := CreateFromLabel(s, Cremona, 0);
   require t : "No abelian variety with label",s;
   return A;
end intrinsic;

intrinsic ModularAbelianVariety(s::MonStgElt, Sign::RngIntElt : 
    Cremona := false ) -> ModAbVar
{The abelian variety with sign Sign defined by the string s.}
   require Sign in {-1,0,1} : 
       "Sign must be -1, 0, or 1."; 
   t, A := CreateFromLabel(s, Cremona, Sign);
   require t : "No abelian variety with label",s;
   return A;
end intrinsic;

function Copy_ModAbVar(A)
   B := New(ModAbVar);
   if assigned A`base_ring then B`base_ring := A`base_ring; end if;
   if assigned A`associated_abvar_over_Q then B`associated_abvar_over_Q := A`associated_abvar_over_Q; end if;
   if assigned A`component_group_order then B`component_group_order := A`component_group_order; end if;
   if assigned A`conductor then B`conductor := A`conductor; end if;
   if assigned A`dimension then B`dimension := A`dimension; end if;
   if assigned A`endomorphism_ring then B`endomorphism_ring := A`endomorphism_ring; end if;
   if assigned A`endomorphism_algebra then B`endomorphism_algebra := A`endomorphism_algebra; end if;
   if assigned A`hecke_algebra then B`hecke_algebra := A`hecke_algebra; end if;
   if assigned A`field_of_definition then B`field_of_definition := A`field_of_definition; end if;
   if assigned A`frobpolys then B`frobpolys := A`frobpolys; end if;
   if assigned A`homology then B`homology := A`homology; end if;
   if assigned A`inner_twists then B`inner_twists := A`inner_twists; end if;
   if assigned A`weights then B`weights := A`weights; end if;
   if assigned A`num_rational_points then B`num_rational_points := A`num_rational_points; end if;
   if assigned A`cm_twists then B`cm_twists := A`cm_twists; end if;
   if assigned A`isogeny_decomp then B`isogeny_decomp := A`isogeny_decomp; end if;
   if assigned A`tamagawa_numbers then B`tamagawa_numbers := A`tamagawa_numbers; end if;
   if assigned A`decomposition then B`decomposition := A`decomposition; end if;

   if assigned A`is_simple then B`is_simple := A`is_simple; end if;
   if assigned A`is_selfdual then B`is_selfdual := A`is_selfdual; end if;
   if assigned A`is_Af then B`is_Af := A`is_Af; end if;
   if assigned A`is_quaternionic then B`is_quaternionic := A`is_quaternionic; end if;
   if assigned A`is_only_motivic then B`is_only_motivic := A`is_only_motivic; end if;
   if assigned A`newform_number then B`newform_number := A`newform_number; end if;
   if assigned A`newform then B`newform := A`newform; end if;
   if assigned A`modular_param then B`modular_param := Copy_MapModAbVar(A`modular_param); end if;
   if assigned A`modular_embedding then B`modular_embedding := Copy_MapModAbVar(A`modular_embedding); end if;
   if assigned A`modular_degree then B`modular_degree := A`modular_degree; end if;
   if assigned A`embeddings then B`embeddings := A`embeddings; end if;
   if assigned A`only_maximal_newform_blocks then B`only_maximal_newform_blocks := A`only_maximal_newform_blocks; end if;
   if assigned A`level then B`level := A`level; end if;
   if assigned A`point_precision then B`point_precision := A`point_precision; end if;
   if assigned A`name then B`name := A`name; end if;

   return B;
end function;

function InCreation(A)
   if not assigned A`modular_embedding or not assigned A`modular_param then
      return true;
   end if;   
   return false;
end function;

function Create_ModAbVar(name, H, K, R, J)
   Verbose("Create_ModAbVar", 
         Sprintf("Creating %o of dimension %o", 
         name eq "" select "ModAbVar" else name, Dimension(H)), "");
   assert Type(name) eq MonStgElt;
   assert Type(H) eq ModAbVarHomol;
   assert IsDefnField(K);
   assert Type(J) in {Tup, BoolElt};
   // If J is a tup, then it must be a three-tuple: 
   //            < J, matrix_embed, matrix_param >,
   //  where J is a modular abelian variety such that
   //  IsAttachedToModularSymbols(J) is true, 
   //  matrix_embed defines a map from H1(A,Q) to H1(J,Q), 
   //  matrix_param defines a map from H1(J,Q) to H1(A,Q), 
   //  and the product of matrix_embed and matrix_param is
   //  multiplication by an integer.   These maps don't have
   //  to preserve integral homology -- they will be scaled 
   //  to do so.
   // ** If exactly one of matrix_embed or matrix_param
   //    is equal to the boolean false, then it is computed
   //    from the other using inverse morphisms

   A := New(ModAbVar);
   A`name := name;
   A`homology := H;
   A`field_of_definition := K;
   A`base_ring := R;
   A`point_precision := 10;   // a default.
   if Type(J) eq BoolElt then  // identity map is modular param.
      assert assigned H`modsym;
      A`modular_param := nIsogeny(A,1);
      A`modular_embedding := nIsogeny(A,1);
   else
      assert Type(J) eq Tup;
      assert #J eq 3;
      J, matrix_embed, matrix_param := Explode(J);
      assert Type(J) eq ModAbVar;
      J := ChangeRing(J,R);
      assert {Type(matrix_embed), Type(matrix_param)}
                      subset {BoolElt, AlgMatElt, ModMatFldElt};
      if Type(matrix_embed) eq BoolElt then
     assert Type(matrix_param) ne BoolElt;
         assert Nrows(matrix_param) eq Dimension(Homology(J));
         assert Ncols(matrix_param) eq Dimension(Homology(A));
         A`modular_param := Create_MapModAbVar_MultiplyToMorphism(J, A, matrix_param, K);
         A`modular_embedding := LeftInverseMorphism(A`modular_param);
      elif Type(matrix_param) eq BoolElt then
         assert Type(matrix_embed) ne BoolElt;
         assert Nrows(matrix_embed) eq Dimension(Homology(A));
         assert Ncols(matrix_embed) eq Dimension(Homology(J));
         A`modular_embedding := Create_MapModAbVar_MultiplyToMorphism(A, J, matrix_embed, K);
         A`modular_param := RightInverseMorphism(A`modular_embedding);
      else
         A`modular_embedding := Create_MapModAbVar_MultiplyToMorphism(A, J, matrix_embed, K);
         assert Nrows(matrix_param) eq Dimension(Homology(J));
         assert Ncols(matrix_param) eq Dimension(Homology(A));
         A`modular_param := Create_MapModAbVar_MultiplyToMorphism(J, A, matrix_param, K);
      end if;
      // optimize the modular parameterization somewhat (i.e., if one is 2*phi, replace it with phi).
      // We are not making the parameterizations "optimal" in sense of connected kernel.
      A`modular_embedding := DivideOutIntegers(A`modular_embedding);
      A`modular_param := DivideOutIntegers(A`modular_param);
   end if;
   return A;
end function;



function Create_ModAbVar_ModSym(name, X) 
   Verbose("Create_ModAbVar_ModSym", "",
         Sprintf("Creating %o from %o", name, X));
   // The modular abelian variety associated to the spaces in the 
   // sequence X of  modular symbols.  The modular symbols
   // spaces need *not* be of weight 2.  If any space has 
   // weight bigger than 2, there is an abelian variety, but it
   // is only defined over the real numbers.    
   if Type(X) eq ModSym then
      X := [X];
   end if;
   assert Type(X) eq SeqEnum and #X gt 0 and Type(X[1]) eq ModSym;
   sign := Sign(X[1]);
   K := QQ;  // min field of definition
   is_only_motivic := false;
   for i in [1..#X] do
      M := X[i];     
      assert not IsMultiChar(M);
      if not IsCuspidal(M) then
         M := CuspidalSubspace(M);
         X[i] := M;
      end if;
      assert Sign(M) eq sign ;
      eps := DirichletCharacter(M);
      assert BaseField(M) cmpeq BaseRing(Parent(MinimalBaseRingCharacter(eps)));
      // as a motive it *is* over Q, and lots of stuff makes sense, so we'll 
      // just formally work as in weight 2 case, with same constraints...
      if Weight(M) ne 2 then 
         is_only_motivic := true;
      end if;
   end for;
   H := Create_ModAbVarHomol(X);
   A := Create_ModAbVar(name, H, K, K, true);
   A`is_only_motivic := is_only_motivic;
   return A;
end function;


function Create_ModAbVar_AssociatedToModularSymbolsSubspace(name, M);
   assert Type(name) eq MonStgElt;
   assert Type(M) eq ModSym;
   M := CuspidalSubspace(M);

   S := CuspidalSubspace(AmbientSpace(M));
   N := Level(M);
   J := ModularAbelianVariety([S]);

   /* Write subspace with respect to basis for S and restrict down to Q. */
   VS := VectorSpace(S);
   W := VectorSpace(BaseField(S),Dimension(S));
   V := VectorSpaceWithBasis([W|Coordinates(VS, b) : b in Basis(VectorSpace(M))]);
   V := RestrictionOfScalars(V);

   H,embed := Create_ModAbVarHomol_Subspace(Homology(J),V);
   A := Create_ModAbVar(name, H, QQ, QQ, <J, embed, false>);
   return A;
end function;



intrinsic Weights(A::ModAbVar) -> Set
{The set of weights of A.}
   if not assigned A`weights then
      A`weights := Set(&cat[
          [Weight(M) : M in ModularSymbols(Af[1])] : Af in Factorization(A)]);
   end if;
   return A`weights;
end intrinsic;


intrinsic Level(A::ModAbVar) -> RngIntElt
{An integer N so that A is a quotient of a power of J_1(N).  }
   if not assigned A`level then
      if IsAttachedToModularSymbols(A) then
         A`level := LCM([Level(M) : M in A`homology`modsym]);
      else
         A`level := Level(Domain(ModularParameterization(A)));
      end if;
   end if;
   return A`level;
end intrinsic;
      

intrinsic FieldOfDefinition(A::ModAbVar) -> Fld
{The best known field of definition of A.}
   return A`field_of_definition;
end intrinsic;

intrinsic DirichletCharacter(A::ModAbVar) -> GrpDrchElt
{If A = A_f is attached to a newform, then this returns the Nebentypus
character of f.  }
   t, Af := IsAttachedToNewform(A);
   require t:"Argument 1 must be of the form A_f for a newform f.";
   M := Homology(Af)`modsym[1];
   return DirichletCharacter(M);
end intrinsic;

intrinsic DirichletCharacters(A::ModAbVar) -> List
{All Dirichlet characters of spaces of modular symbols associated with
the modular symbols abelian variety that parameterizes A.}
   J := Domain(ModularParameterization(A));
   M := ModularSymbols(J);
   ans := [* *];
   for m in M do 
      Append(~ans,DirichletCharacter(m));
   end for;
   return ans;
end intrinsic;


intrinsic Dimension(A::ModAbVar) -> RngIntElt
{The dimension of A.}
   if not assigned A`dimension then
      H := Homology(A);
      A`dimension := HomologySignZeroDimension(H);
   end if;
   return A`dimension;
end intrinsic;

intrinsic BaseRing(A::ModAbVar) -> Rng
{The ring over which A is defined.}
   return A`base_ring;
end intrinsic;


function ShortDesc(A) 
   assert Type(A) eq ModAbVar;
   if A`name eq "" then
      return Sprintf("modular abelian variety of dimension %o",Dimension(A));
   else
      return A`name;
   end if;
end function;


intrinsic Sign(A::ModAbVar) -> RngIntElt
{The sign of A, which is either 0, -1, or +1.  }
   return Homology(A)`sign;
end intrinsic;


function Name(A)
   // A short string that describes A.
   // We skip type checking, so this function can apply to objects
   // of other types (e.g., when imported into decomp.m).
   return A`name;
end function;

procedure SetName(A, name) 
   // Set the name of A.
   A`name := name;
end procedure;


/***************************************************************************

 << Conductor >>

 ***************************************************************************/

intrinsic Conductor(A::ModAbVar) -> RngIntElt
{The conductor of the abelian variety A, where A
is defined over Q.  }
   // TODO: Extend this for abelian varieties not necessarily over Q.
   // Is this easy?
   require BaseRing(A) cmpeq QQ : "Argument 1 must be defined over Q.";
   if not assigned A`conductor then
      if not IsAttachedToNewform(A) then
         D := Factorization(A);
         A`conductor := &*[Conductor(X[1])^#X[2] : X in D];
      else
         A`conductor := Level(A)^Dimension(A);
      end if;
   end if;
   return A`conductor;
end intrinsic;

/***************************************************************************

 << Number of Points >>


 ***************************************************************************/

intrinsic NumberOfRationalPoints(A::ModAbVar) -> RngIntElt, RngIntElt
{Divisor and multiple of the cardinality of A(K),  where A is a modular abelian 
 variety defined over a field K.  }
   return ComputeSize(A);
end intrinsic;

intrinsic '#'(A::ModAbVar) -> RngIntElt
{NumberOfRationalPoints, if an exact value known}
   require IsAbelianVariety(A) : "Argument 1 must be an abelian variety.";
   l, u := ComputeSize(A);
   if l eq u then
    return l;
   else 
    require false : "An exact value is not known";
   end if;
end intrinsic;



/***************************************************************************

  << Inner Twists and Complex Multiplication >>

 ***************************************************************************/

intrinsic CMTwists(A::ModAbVar : Proof := false) -> SeqEnum
{The CM inner twists characters of the newform abelian variety A = A_f 
that are defined over the base ring of A.  }
   if not assigned A`cm_twists then
      Verbose("CMTwists", Sprintf("Computing CM twists of %o.", A),
              Sprintf("Proof = %o", Proof));
      t, A0 := CanChangeRing(A,QQ);
      require t : "Argument 1 must be base extension of abelian variety over Q.";
      t, A0 := IsAttachedToNewform(A0);
      require t : "Argument 1 must be attached to a newform.";
      dummy := InnerTwists(A : Proof := Proof);
      require assigned A`cm_twists : "Argument 1 must be attached to a newform.";
   end if;
   return A`cm_twists;
end intrinsic;

intrinsic InnerTwists(A::ModAbVar : Proof := false) -> SeqEnum
{The inner twists characters of the newform abelian variety A = A_f
that are defined over the base ring of A.  WARNING: Even if Proof is
True, the program does not prove that every twist returned is in fact
an inner twist (though they are up to precision 0.00001).}

   K := BaseRing(A);
   require IsField(K) : "Argument 1 must be over a field.";
   require Characteristic(K) eq 0 : "Argument 1 must be over a field of characteristic 0.";
   if not assigned A`inner_twists then
      Verbose("InnerTwists", Sprintf("Computing inner twists of %o.", A),
              Sprintf("Proof = %o", Proof));
      if Type(K) eq FldRat then
         A`inner_twists := [];
         A`cm_twists := [];
         return [];
      end if;
      t, A0 := CanChangeRing(A,QQ);
      require t : "Argument 1 must be base extension of abelian variety over Q.";
      t, A0 := IsAttachedToNewform(A0);
      require t : "Argument 1 must be attached to a newform.";
       A`inner_twists, A`cm_twists := 
            Compute_Inner_Twists_Over_K(ModularSymbols(A0)[1],BaseRing(A), Proof);         
   end if;
   return A`inner_twists;
end intrinsic;



/***************************************************************************

  << Predicates >>

 ***************************************************************************/

intrinsic IsQuaternionic(A::ModAbVar) -> BoolElt
{True if and only if some simple factor of A over the base ring 
has quaternionic multiplication.}
/*TODO: This will currently always return false, since the
function decomp.m:Create_Af_and_Homs always sets it to
false, since I haven't programmed deciding whether multiplication
is quaternionic in general.
*/
   if not assigned A`is_quaternionic then
      A`is_quaternionic := Decide_If_Quaternionic(A);
   end if;
   return A`is_quaternionic;
end intrinsic;

intrinsic IsSimple(A::ModAbVar) -> BoolElt
{True if and only if A has no proper abelian subvarieties over
 BaseRing(A).}
   if not assigned A`is_simple then
      X := Factorization(A);
      A`is_simple := #X eq 1 and #X[1][2] eq 1;
   end if;
   return A`is_simple;
end intrinsic;

intrinsic IsAttachedToNewform(A::ModAbVar) -> BoolElt, ModAbVar, MapModAbVar
{True if A is isogenous to a newform abelian variety A_f in which case
the abelian variety A_f is also returned.}
   if not assigned A`is_Af then
      if not assigned A`is_Af then
         D := Factorization(A);
         if #D eq 0 then
            A`is_Af := false;
         elif #D gt 1 or #D[1][2] gt 1 then
            A`is_Af := false;
         else
            A`is_Af := <D[1][1], D[1][2][1]>;
         end if;
      end if;
   end if;
   if Type(A`is_Af) eq BoolElt then
      if A`is_Af then
         return true,  A, IdentityMap(A);
      else
         return false, _, _;
      end if;
   end if;
   return true, A`is_Af[1], A`is_Af[2];
end intrinsic;

intrinsic CanDetermineIsomorphism(A::ModAbVar, B::ModAbVar) -> BoolElt, BoolElt, MapModAbVar
{True if we can determine whether or not A and B are isomorphic.  }

   require Sign(A) eq Sign(B) : "Arguments 1 and 2 must have the same sign.";
   Verbose("CanDetermineIsomorphism", Sprintf("Isomorphism between %o and %o?",A, B),""); 
   // print "Isogenous?";
   if not IsIsogenous(A,B) then
      Verbose("CanDetermineIsomorphism", "","   * Not even isogenous.");
      return true, false, "", 1;
   end if;
   if A eq B then
      Verbose("CanDetermineIsomorphism", "","   * Equal.");
      return true, true, IdentityMap(A), 2;
   end if;
   // print "Simple?";
   if IsSimple(A) and IsSimple(B) then
      Verbose("CanDetermineIsomorphism", "","   * Both simple.");
      f := NaturalMap(B,A);
      deg := Degree(f);
      Verbose("CanDetermineIsomorphism", "",  Sprintf("* Natural map has degree",deg));
    
      is_field, K, K_to_End, End_to_K := IsField(BaseExtend(End(A),QQ));
      if not is_field then
         return false, false, "", 3; 
      //      "Isomorphism testing not programmed when endomorphism rings are not fields", _;
      end if;

      // The endomorphism algebra is a field. 
      if Degree(K) eq Dimension(A) then
         t, d := IsSquare(deg);
         if not t then   // Since deg(K) = Dim(A), the
                         // degrees of endomorphisms are perfect squares
                         // since they are the squares of norms.
                         // This uses that the dimension of the endomorphism
                         // algebra equals the dimension of A, and that
                         // the endomorphism algebra is a field.
                         // (See Page 126, Prop 12.12 of Milne's 
                         // "Abelian Varieties" in [Cornell-Silverman].)
            return true, false, "", 4;
         end if;
      end if;

      // There is an isomorphism if and only if Hf contains
      // an element of degree deg.  We try to decide this by mapping
      // to the field Hom_0(A,A) and solving a norm equation.
      H := Hom(A,B);    // all homomorphism from A to B.  
      Hf := Pullback(H, f);  // subspace of End(A,A).


      Verbose("CanDetermineIsomorphism", "", 
              Sprintf("Looking for an element of norm", d));
      // Find all elements with norm d in K.
      if Type(K) eq FldRat then
         X := [d, -d];
         t := true;
      else
         // These two lines are commented out, since they would only be
         // useful if End(A) were maximal, and it usually isn't.
         // Fortunately, MAGMA solves Diophantine norm equations in
         // orders, so we don't have a problem. 
         // O_K := MaximalOrder(K);
         // t, X := NormEquation(O_K,d : All := true);
         G := [End_to_K(f) : f in Generators(End(A))];
         // print "Computing order";
         O := Order(G);
         // print "Solving norm equation";
         t, X := NormEquation(O,d : All := true);
         t1, Y := NormEquation(O,-d : All := true);
         // print "Solving done";
         if t then
            X := [K!a : a in X];
         end if;
	 if t1 then
	    for y in Y do
		Append(~X, K!y);
	    end for; 
	 end if;
      	 // print "Appending done";
      end if;
      // This is changed because of +/- business.
      if not (t or t1) then
         return true, false, "", 5;
      end if;
      // Now lift each of the elements of X back to the endomorphism
      // ring of A, and check to see if any lie in Hf.  One does if
      // A is isomorphic to B.
      for x in X do
         // print x;
         g := K_to_End(x);
         // print g;
         if g in Hf then   // g has degree deg and g = psi*f for some
                           // psi in Hom(A,B) and f has degree deg, 
                           // so psi=g*f^(-1) is an explicit isomorphism.
            // print "Good solution";
            return true, true, g*f^(-1), 6;
         end if;
      end for;
      // print "None of the solution worked";
      return true, false, "", 6;
   end if;
   f := NaturalMap(A,B);
   if IsIsogeny(f) then
      G := ComponentGroupOfKernel(f);
      if #G eq 1 then
         return true, true, f;
      end if;
      I := Invariants(G);
      if Sign(A) ne 0 then
         I := [Integers() |OddPart(n) : n in I | OddPart(n) ne 1];
      end if;
      if #I eq 2*Dimension(A) and #Set(I) eq 1 then
         return true, true, (1/I[1])*f;
      end if;
      /* We generalize prop 12.12 from Milne's article again (see above)
         to deduce that the degree of f must be a square, so long as 
            1) each factor in a simple decomposition of A has multiplicity 1.  
            2) the endomorphism algebra of each simple factor is a field
               of dimension equal to the degree of the factor.
         The proof is as follows.  Suppose, for simplicity that 
                              g:A-->C x D
         is an isogeny and that C and D are
         non-isogenous simple abelian varieties.  Suppose also that
         End_0(C) and End_0(D) are fields of degree equal to the dimension
         of C and D, respectively.  Let h be the complementary morphism
         to g, so that g*h = h*g = [deg(g)].   If phi:C --> C is a surjective
         endomorphism, then deg(h*phi*g) = deg(phi)*deg(g)^(2*dim(A)).
         Since h*phi*g is an endomorphism of C x D, it is a cross product of
         an endomorphism of C and an endomorphism of D.  As such, its
         degree is the product of two squares (by Milne), hence a square.
         Since deg(g)^(2*dim(A)) is a square, it follows that phi must 
         have degree a square as well.
      */
      if HasMultiplicityOne(A) then
         small_fields := true;
         if Type(BaseRing(A)) ne FldRat then
            for F in Decomposition(A) do 
               is_field, K, K_to_End, End_to_K := IsField(BaseExtend(End(F[1]),QQ));
               if not is_field or is_field and Degree(K) ne Dimension(F[1]) then
                  small_fields := false;
                  break;
               end if;
            end for;
         end if;
         if small_fields then
            t, _ := IsSquare(Degree(f));
            if not t then
               return true, false, _;
            end if;
         end if;
      end if;
   end if;
   return false, "All tests failed to decide whether A and B are isomorphic.", _;
end intrinsic;

intrinsic MinimalIsogeny(A::ModAbVar, B::ModAbVar) -> BoolElt, MapModAbVar, RngIntElt
{True if A and B are isogenous. In that case returns the minimal degree of an isogeny
between A and B and an explicit isogeny of that degree. False if A and B are not isogenous.  
If A and B are simple and defined over Q, then it is always possible to 
the minimal degree of an isogeny.}

   require Sign(A) eq Sign(B) : "Arguments 1 and 2 must have the same sign.";
   Verbose("MinimalIsogeny", Sprintf("Minimal isogeny between %o and %o?",A, B),""); 
   
   if not IsIsogenous(A,B) then
      Verbose("MinimalIsogeny", "","   * Not even isogenous.");
      return false, "", 0;
   end if;
   if A eq B then
      Verbose("MinimalIsogeny", "","   * Equal.");
      return true, IdentityMap(A), 1;
   end if;
   if IsSimple(A) and IsSimple(B) then
      Verbose("MinimalIsogeny", "","   * Both simple.");
      f := NaturalMap(B,A);
      deg := Degree(f);
      a, b := SquarefreeFactorization(deg);
      Verbose("MinimalIsogeny", "",  Sprintf("* Natural map has degree",deg));
    
      is_field, K, K_to_End, End_to_K := IsField(BaseExtend(End(A),QQ));
      if not is_field then
         return false, "", 0; 
      //      "Minimal isogeny testing not programmed when endomorphism rings are not fields", _;
      end if;

      // The endomorphism algebra is a field. 

      i := 0;
      while true do	
         i := i+1;

         // There is an isogeny of degree a*i^2 if and only if Hf contains
         // an element of degree a^2*b^2*i^2.  We try to decide this by mapping
         // to the field Hom_0(A,A) and solving a norm equation.
         H := Hom(A,B);    // all homomorphism from A to B.  
         Hf := Pullback(H, f);  // subspace of End(A,A).

         Verbose("MinimalIsogeny", "", 
                 Sprintf("Looking for an element of norm", a*b*i));
         // Find all elements with norm a*b*i in K.
         //Ask William about this!
         //if Type(K) eq FldRat then
         //   X := [d];
         //   t := true;
         //else
         // These two lines are commented out, since they would only be
         // useful if End(A) were maximal, and it usually isn't.
         // Fortunately, MAGMA solves Diophantine norm equations in
         // orders, so we don't have a problem. 
         // O_K := MaximalOrder(K);
         // t, X := NormEquation(O_K,d : All := true);
         G := [End_to_K(f) : f in Generators(End(A))];
         O := Order(G);
         t, X := NormEquation(O,a*b*i : All := true);
         t1, Y := NormEquation(O,-a*b*i : All := true);
         if t then
            X := [K!a : a in X];
	 else
	    X := [];
         end if;
   	 if t1 then
   	    for y in Y do
   		Append(~X, K!y);
   	    end for; 
   	 end if;
         finito := false;
         if not (t or t1) then
   	    finito := true;
         end if;
         if not finito then
            // Now lift each of the elements of X back to the endomorphism
            // ring of A, and check to see if any lie in Hf.  One does if
            // A is isogenous B with an isogeny of degree a*i^2.
            for x in X do
               g := K_to_End(x);
               if g in Hf then   // g has degree a^2*b^2*i^2 and g = psi*f for some
                                 // psi in Hom(A,B) and f has degree a*b^2, 
                                 // so psi=g*f^(-1) is an explicit isogeny of degree a*i^2.
                  return true, g*f^(-1), a * i^2;
               end if;
            end for;
         end if;
      end while;  
   end if;
end intrinsic;


intrinsic HasMultiplicityOne(A::ModAbVar) -> BoolElt
{True if the simple factors of A appear with multiplicity one.}
   for F in Factorization(A) do
      if #F[2] gt 1 then
         return false;
      end if;
   end for;
   return true;
end intrinsic;

intrinsic IsIsomorphic(A::ModAbVar, B::ModAbVar) -> BoolElt, MapModAbVar
{True if A and B are isomorphic.  If true, also returns an explicit
isomorphism.}

   t, iso, map := CanDetermineIsomorphism(A,B);
   require t : iso;
   if not iso then
      return iso, _;
   end if;
   return iso, map;
end intrinsic;


intrinsic IsIsogenous(A::ModAbVar, B::ModAbVar) -> BoolElt
{True if A and B are isogenous.}
   require BaseRing(A) cmpeq BaseRing(B) : 
        "Arguments 1 and 2 must be over the same base field.";
   if Dimension(A) ne Dimension(B) then
      return false;
   end if;
   if not IsSimple(A) then
      if IsSimple(B) then
         return false;
      end if;
      // Neither isogeny simple.
      DA := Factorization(A);
      DB := Factorization(B);
      // Pair off factors.
      for C in DA do 
         fail := true;
         for i in [1..#DB] do 
            if IsIsogenous(DB[i][1],C[1]) then 
               if #DB[i][2] ne #C[2] then
                  return false;
               end if;
               Remove(~DB,i);
               fail := false;
               break;
            end if;
         end for;
         if fail then
            return false;
         end if;
      end for;
      return true;
   end if;
   if not IsSimple(B) then
      return false;
   end if;
   // Both are isogeny simple. 
   A := Factorization(A)[1][1];
   B := Factorization(B)[1][1];
   if BaseRing(A) cmpeq QQ then
      // Since base is Q, these are newform abelian varieties, 
      // so can decide isogeny using degeneracy maps.
      f := NaturalMap(A,B,1);   
      return not IsZero(f);
   end if;
   if IsAttachedToModularSymbols(A) and IsAttachedToModularSymbols(B) then
      return ModularSymbols(A)[1] eq ModularSymbols(B)[1];
   end if;
   require false : "Unable to determine whether or not A and B are isogenous.";
end intrinsic;

intrinsic IsAbelianVariety(A::ModAbVar) -> BoolElt
{True if A is an abelian variety.}
   if Dimension(A) eq 0 then
      return true;
   end if;
   if IsOnlyMotivic(A) then
      return Type(BaseRing(A)) eq Type(ComplexField());
   end if;
   R := BaseRing(A);
   n := Characteristic(R);
   if n eq 0 then
      if Type(R) in {FldRat, FldNum, FldCyc, FldQuad} then
         return true;
      end if;
   end if;
   t, A0 := CanChangeRing(A,QQ);
   require t : "It must be possible to change the base ring of " * 
               "argument 1 to the RationalField().";
   N := Conductor(A0);
   t := IsInvertible(R!N);
   return t;
end intrinsic;

// TO DO: this seems to require sign 0

intrinsic IsSelfDual(A::ModAbVar) -> BoolElt
{True if A is known to be isomorphic to its dual.}
   if not assigned A`is_selfdual then
      if Dimension(A) eq 1 then
         A`is_selfdual := true;
      else
         t, dual := IsDualComputable(A);
         require t : "Unable to determine the dual of A ("*dual*").";
         t, ans := CanDetermineIsomorphism(A,dual);
         require t : "Unable to determine if A is isomorphic to its dual ("*ans*").";
         if t then
            A`is_selfdual := ans;
         end if;
      end if;
   end if;
   return A`is_selfdual;
end intrinsic;

intrinsic IsAttachedToModularSymbols(A::ModAbVar) -> BoolElt
{True if the underlying homology of A is being computed using a space
of modular symbols.  }
   return assigned (A`homology)`modsym;   
end intrinsic;

intrinsic IsOnlyMotivic(A::ModAbVar) -> BoolElt
{True if any of the modular forms attached to A have weight bigger than 2.}
   if not assigned A`is_only_motivic then
      if Type(BaseRing(A)) eq FldRe then
         A`is_only_motivic := false;
      else
         Amb := Codomain(ModularEmbedding(A));
         // TODO: Polish is_only_motivic
         // This is potentially a BUG, though definitely not serious.
         // (It might just print "abelian variety" when it should
         // print "motivic".)
         // At worst it would say that something is not motivic when
         // it is --- since we never do anything such that this matters,
         // it isn't an issue for now.  This should be improved
         // for the final release.
         A`is_only_motivic := assigned Amb`is_only_motivic and
                           Amb`is_only_motivic;
      end if;
   end if;
   return A`is_only_motivic;
end intrinsic;


/***************************************************************************

  << Printing >>

 ***************************************************************************/

intrinsic Print(A::ModAbVar, level::MonStgElt)
{}

   if InCreation(A) then
      printf "Modular abelian variety.";
   else
      printf "Modular %o%o of dimension %o%o level %o %oover %o%o", 
         IsOnlyMotivic(A) select "motive" else "abelian variety",
         A`name ne "" select " "*A`name else "", 
         Dimension(A), 
         assigned A`conductor select "," else " and",
         FactorPrint(Level(A)), 
         assigned A`conductor select Sprintf("and conductor %o ",FactorPrint(Conductor(A))) else "",
         RingName(BaseRing(A)), 
         Sign(A) ne 0 select Sprintf(" with sign %o",Sign(A)) else "";
   end if;
end intrinsic;


/***************************************************************************

  << Equality and Inclusion Testing >> 

 ***************************************************************************/

intrinsic 'eq'(A::ModAbVar, B::ModAbVar) -> BoolElt
{True if A and B are equal.}
   if Dimension(A) ne Dimension(B) then
      return false;
   end if;
   if not (A`field_of_definition cmpeq B`field_of_definition) then
      return false;
   end if;
   if not (A`base_ring cmpeq B`base_ring) then
      return false;
   end if;
   if IsAttachedToModularSymbols(A) then
      if not IsAttachedToModularSymbols(B) then
         return false;
      end if;
      return A`homology eq B`homology;  
   end if;
   // Now over same field and ring, and neither is attached to modular symbols.
   // so we consider them the same if they are exactly the same model for a 
   // sub-abelian variety of something attached to modular symbols.
   if Homology(A) ne Homology(B) then   // check if lattices the same lattice.
      return false;
   end if;
   eA := ModularEmbedding(A);
   eB := ModularEmbedding(B);
   return Codomain(eA) eq Codomain(eB) and Matrix(eA) eq Matrix(eB);

end intrinsic;

intrinsic 'in'(A::ModAbVar, X::List) -> BoolElt
/* EXCLUDE FROM HANDBOOK */
{True if A is equal to one of the elements of the list X.}
   return &or [A eq B : B in X];
end intrinsic; 

intrinsic 'subset'(A::ModAbVar, B::ModAbVar) -> BoolElt
{True if A is a subset of B.}
   if A eq B then
      return true;
   end if;
   if Dimension(A) eq 0 then
      return true;
   end if;
   if Dimension(A) gt Dimension(B) then
      return false;
   end if;
   eA := ModularEmbedding(A);
   eB := ModularEmbedding(B);
   if Codomain(eA) ne Codomain(eB) then
      return false;
   end if;
   if not IsInjective(eA) then
      return false;
   end if;
   if not IsInjective(eB) then
      return false;
   end if;
   return RowSpace(Matrix(eA)) subset RowSpace(Matrix(eB));
end intrinsic;


/***************************************************************************

  << Modular Embedding and Parameterization >>


 ***************************************************************************/


intrinsic ModularParameterization(A::ModAbVar) -> MapModAbVar
{A surjective morphism to A from an abelian variety attached to
modular symbols.}
   return A`modular_param;
end intrinsic;

intrinsic ModularEmbedding(A::ModAbVar) -> MapModAbVar
{A morphism with finite kernel from A to a modular 
abelian variety attached to modular symbols.  }
   return A`modular_embedding;
end intrinsic;


intrinsic CommonModularStructure(X::[ModAbVar]) -> List, List
{This intrinsic finds modular abelian varieties J_e and J_p associated to modular symbols 
and returns a list of finite-kernel maps from the abelian varieties in X to J_e 
and a list of modular paramaterizations from J_p to the abelian varieties in X.}
   require #X gt 0 : "Argument 1 must be nonempty.";

   Dp := [* Domain(ModularParameterization(X[1])) *]; 
   De := [* Codomain(ModularEmbedding(X[1])) *]; 
   for i in [2..#X] do 
      B := Domain(ModularParameterization(X[i]));
      if not (B in Dp) then
         Append(~Dp, B);
      end if;
      B := Codomain(ModularEmbedding(X[i]));
      if not (B in De) then
         Append(~De, B);
      end if;
   end for;
 

   _, embed_p, param_p := DirectSum([x : x in Dp]);
   _, embed_e, param_e := DirectSum([x : x in De]);

   param_X := [* *];
   embed_X := [* *];
   for A in X do
      for i in [1..#Dp] do
         if Dp[i] eq Domain(ModularParameterization(A)) then
            Append(~param_X, param_p[i]*ModularParameterization(A));
            break;
         end if;
      end for;
      for i in [1..#De] do 
         if De[i] eq Codomain(ModularEmbedding(A)) then
            Append(~embed_X, ModularEmbedding(A)*embed_e[i]);
            break;
         end if;
      end for;
   end for;

   return embed_X, param_X;
end intrinsic;

/***************************************************************************

  << Coercion >>

 ***************************************************************************/

intrinsic IsCoercible(A::ModAbVar, x::.) -> BoolElt, ModAbVarElt
{Coerce x into A.  The argument x can be an element of a modular abelian
variety, the integer 0, a sequence obtained by Eltseq'ing an element of A (i.e.,
a linear combination of *integral* homology),  a vector on the basis for 
*rational* homology, or a tuple of the form <P(X,Y),[u,v]> that defines
a modular symbol.}
   require Characteristic(BaseRing(A)) eq 0 : 
         "Creation of points on abelian varieties over " * 
         "finite fields not allowed.";
    
   H := Homology(A);
   case Type(x):
      when Tup:
         t, z := IsCoercible(H,x);
         if not t then
            return false, "Could not coerce modular symbol into abelian variety.";
         end if;
         return true, A!z;
      when ModAbVarElt:
         if Parent(x) eq A then
            return true, x;
         end if;
         e := ModularEmbedding(Parent(x)); 
         f := ModularEmbedding(A);
         if Codomain(f) eq Codomain(e) then
            y := e(x);
            if Element(y) in RowSpace(Matrix(f)) then
               pi := ModularParameterization(A);
               return true, pi(y);
            end if;
         end if;   
         return false, "Illegal coercion."; 
      when SeqEnum, ModTupFldElt, ModTupRngElt, LatElt:
         lattice := Type(x) eq SeqEnum;
         if Type(x) ne SeqEnum then
            w := x;
            x := Eltseq(x);
         end if;
         if #x gt 0 and Type(x[1]) in {SetCspElt, ExtReElt} then
            t, z := IsCoercible(H, x);   // as modular symbol.
            if not t then
               return false, "Unable to coerce modular symbol into space.";
            end if;
            return true, A!z;
         end if;
       
         if #x ne Dimension(Homology(A)) then
            return false, Sprintf("Argument 2 must be a sequence of %o elements.",
                      Dimension(Homology(A)));   
         end if;
         if #x eq 0 then
            return A!0;
         end if;
         if lattice then           
            B := Basis(IntegralHomology(A));
            V := VectorSpace(FieldOfFractions(Parent(x[1])),#x);
            w := &+[V|x[i]*B[i]  : i in [1..#x]];
         end if;

         t, v := IsCoercible(VectorSpace(H), w);

         K := Qbar;
         if not t then
            t, v := IsCoercible(RealVectorSpace(H), w);
            K := CC;
         end if;
         if not t then
            return false, "Illegal coercion.";
         end if;
         z := Create_ModAbVarElt(v, A, K);
         return true, z;

      when RngIntElt, FldRatElt:
         if x ne 0 then 
            return false, "Argument 2 must be 0 if it is an integer.";
         end if;
         return true, Create_ModAbVarElt_Zero(A);
      else 
         return false, "Illegal coercion";
   end case;      
end intrinsic;




/***************************************************************************

  << Modular Symbols to Homology >>

***************************************************************************/

function MStoHom_Coercion(A, x)
   if not IsAttachedToModularSymbols(A) then  
              // first reduce to modular symbols case.
      pi := ModularParameterization(A);
      y := MStoHom_Coercion(Domain(pi),x);
      if Type(y) eq BoolElt then
         return y;
      end if;
      return y*Matrix(pi);
   end if;
   t,y := IsCoercible(Homology(A),x);
   if not t then
      return false;
   end if;
   return y;
end function;

intrinsic ModularSymbolToRationalHomology(A::ModAbVar, x::ModSymElt) 
     -> ModTupFldElt
{The element of rational homology of the abelian variety A naturally
associated to the modular symbol x.}
   ans := MStoHom_Coercion(A, x);
   require Type(ans) ne BoolElt : "Argument 2 not coercible into argument 1.";
   return ans;
end intrinsic;

intrinsic ModularSymbolToRationalHomology(A::ModAbVar, x::SeqEnum) -> ModTupFldElt
{The element of rational homology of the abelian variety A naturally
associated to the (formal) modular symbol x.}
   ans := MStoHom_Coercion(A, x);
   require Type(ans) ne BoolElt : "Argument 2 not coercible into argument 1.";
   return ans;
end intrinsic;

intrinsic ModularSymbolToRationalHomology(A::ModAbVar, x::Tup) -> ModTupFldElt
{The element of rational homology of the abelian variety A naturally
associated to the (formal) modular symbol x.}
   ans := MStoHom_Coercion(A, x);
   require Type(ans) ne BoolElt : "Argument 2 not coercible into argument 1.";
   return ans;
end intrinsic;

intrinsic ModularSymbolToIntegralHomology(A::ModAbVar, x::SeqEnum) -> ModTupFldElt
{The element of integral homology of the abelian variety A naturally
associated to the (formal) modular symbol x.}
   ans := MStoHom_Coercion(A, x);
   require Type(ans) ne BoolElt : "Argument 2 not coercible into argument 1.";
   H := Homology(A);
   C := BasisChange_Rational_to_Lattice(H);
   return ans*C;
end intrinsic;

intrinsic ModularSymbolToIntegralHomology(A::ModAbVar, x::Tup) -> ModTupFldElt
{The element of integral homology of the abelian variety A naturally
associated to the (formal) modular symbol x.}
   ans := MStoHom_Coercion(A, x);
   require Type(ans) ne BoolElt : "Argument 2 not coercible into argument 1.";
   H := Homology(A);
   C := BasisChange_Rational_to_Lattice(H);
   return ans*C;
end intrinsic;


/***************************************************************************

  << Embeddings >>

 ***************************************************************************/

intrinsic Embeddings(A::ModAbVar) -> List
{Return a list of morphisms from A into abelian varieties.}
   if not assigned A`embeddings then
      A`embeddings := [* ModularEmbedding(A) *];
   end if;
   return A`embeddings;
end intrinsic;

intrinsic AssertEmbedding(~A::ModAbVar, phi::MapModAbVar)
{Prepend embedding phi to Embeddings(A).}
   require Domain(phi) eq A : "The domain of argument 2 must be A.";
   require Nullity(phi) eq 0 : "Argument 2 must have finite kernel.";
   if not assigned A`embeddings then
      dummy := Embeddings(A);
   end if;
   if #A`embeddings gt 0 and A`embeddings[1] eq phi then
      return ;
   end if;
   X := [* phi *];
   for f in A`embeddings do
      Append(~X, f);
   end for;
   A`embeddings := X;
end intrinsic;

function AllCharactersTrivial(A)
   return &and[IsTrivial(DirichletCharacter(M)) : 
              M in ModularSymbols(Homology(Codomain(ModularEmbedding(A))))];
end function;

function Can_Compute_Inner_Twists(A)
   return IsAttachedToModularSymbols(A) and #ModularSymbols(A) eq 1 and 
     IsNew(ModularSymbols(A)[1]) and #NewformDecomposition(ModularSymbols(A)[1]) eq 1 ;
end function;


/***************************************************************************

 ***************************************************************************/

intrinsic BaseExtend(A::ModAbVar, R::Rng) -> ModAbVar
{Extend the base ring of A to R, if possible.}
   S := BaseRing(A);
   t, T := ExistsCoveringStructure(R, S);
   require t and T cmpeq R :
           "The base ring of argument 1 and argument 2 are incompatible."*
              " Try using ChangeRing instead.";
   return ChangeRing(A,R);
end intrinsic;

intrinsic ChangeRing(A::ModAbVar, R::Rng) -> ModAbVar
{Change the base ring of A to R, if possible.}
   if R cmpeq BaseRing(A) then
      return A;
   end if;
   if Type(R) eq FldRat and assigned A`associated_abvar_over_Q then
      return A`associated_abvar_over_Q;
   end if;
   B := Copy_ModAbVar(A);
   B`base_ring := R;
   delete B`endomorphism_ring;
   delete B`endomorphism_algebra;
   delete B`hecke_algebra;
   delete B`isogeny_decomp;
   delete B`is_simple;
   delete B`is_selfdual;
   delete B`conductor;
   delete B`inner_twists;
   delete B`cm_twists;
   delete B`decomposition;
   delete B`tamagawa_numbers;
   delete B`embeddings;  // would get infinite loops if try to base extend these...
   if not assigned B`associated_abvar_over_Q then
      if Type(BaseRing(A)) eq FldRat then
          B`associated_abvar_over_Q := A;
      end if;
   end if;
   if Characteristic(R) ne 0 then
      if Type(FieldOfDefinition(A)) eq FldRat then
         B`field_of_definition := GF(Characteristic(R));
      end if;
      B`field_of_definition := R;
   end if;
   Rname := RingName(R);
   if B`name ne "" and Rname ne "" and #Rname lt 8 then
      B`name := Sprintf("%o_%o",B`name,Rname);   
   end if;
   // base extend modular parameterizations, etc.
   if IsAttachedToModularSymbols(A) then
      B`modular_param := IdentityMap(B);
      B`modular_embedding := IdentityMap(B);
   else
      J := ChangeRing(Domain(ModularParameterization(A)),R);
      B`modular_param`domain := J;
      B`modular_param`codomain := B;
      B`modular_param`parent := Hom(J,B);
      B`modular_embedding`domain := B;
      B`modular_embedding`codomain := B`modular_param`domain;
      B`modular_embedding`parent := Hom(B,J);
   end if;
   // It is tempting to base extend all of them, instead of throwing 
   // them away.  However, one could easily get in an infinite loop 
   // by doing so.
   B`embeddings := [* B`modular_embedding *];
   return B;
end intrinsic;

intrinsic CanChangeRing(A::ModAbVar, R::Rng) -> BoolElt, ModAbVar
{True if it is possible to change the base ring of A to R, and A over R 
when possible.}
   t := true;
   /* todo: actually add some conditions! */
   return t, ChangeRing(A,R);
end intrinsic;



function HasOnlyTrivialCharacters(A)
   J := Codomain(ModularEmbedding(A));
   for M in ModularSymbols(J) do
      if not IsTrivial(DirichletCharacter(M)) then
         return false;
      end if; 
   end for;
   return true;
end function;



DEFAULT_COLUMNS := 70;

function Format(s, start, only_first)
/* Reformat string s so each new line starts with start, and
   so the lines have length GetColumns(). */
   cols := GetColumns()-4;
   if GetVerbose("ModAbVar") in {1,3} and #s gt cols * 4 then
      s := &*[s[i] : i in [1..cols*4]] * "...(truncated)";
   end if;
   if GetVerbose("ModAbVar") in {2,4} and #s gt cols * 10 then
      s := &*[s[i] : i in [1..cols*10]] * "...(truncated)";
   end if;
   if cols lt 1 then
      cols := DEFAULT_COLUMNS;
   end if;
   ans := "";
   IDX := [i : i in [1..#s] | s[i] ne "\n"];
   if #IDX eq 0 then
      return "";
   end if;
   s := &*[s[i] : i in IDX];
   while #s gt 0 do 
      ans := ans * start;
      if only_first then
         start := &*[" " : i in [1..#start]];
      end if;
      /*if #s lt cols - #start then
         ans := ans * s;
         return ans;
      end if;*/
      j := cols-#start;
      while j ge 1 and j le #s and not (s[j] in {" ", "\t", "\n"}) do 
         j := j - 1;
      end while;
      if j eq 0 then
         j := cols-#start;
      end if;
      if j ge 1 then
         add := &*[s[i] : i in [1..j] | i le #s];
      else   
         add := "";
      end if;
      ans := ans * add;
      if #start + #add lt cols then
         ans := ans * &*[" " : i in [#start+#add+1..cols]] ;
      end if;
      //ans := ans * " |";
      if j+1 le #s then
         s := &*[s[i] : i in [j+1..#s]];
      else
         s := "";
      end if;
      if #s gt 0 then
         ans := ans * "\n";
      end if;
   end while;
   return ans;
end function;

function VerboseHeader(cmd, level)
   LEN:=45;
   if #cmd gt LEN then
      cmd := &*[cmd[i] : i in [1..LEN]] * "...";
   else
      cmd := cmd * &*[" " : i in [#cmd+1..LEN+3]];
   end if;
   return Sprintf("*  ModAbVar-Verbose %o: %o (time %o)\n", level, cmd, Cputime());
end function;


function VerboseFooter()
   cols := GetColumns();
   if cols eq 0 then
      cols := DEFAULT_COLUMNS;
   end if;
   return &*["-" : i in [1..cols-2]];
end function;

procedure Verbose(cmd, msg1, msg2)
   file := false;
   level := GetVerbose("ModAbVar");
   if level eq 0 then
      return;
   end if;
   msg1 := Sprintf("%o",msg1);
   if level eq 3 then
      level := 1;
      file := true;
   elif level ge 4 then
      level := 2;
      file := true;
   end if;
   if level gt 1 then
      msg2 := Sprintf("%o",msg2);
      msg1 := msg1 * msg2;
   end if;
   out := VerboseHeader(cmd, 
           level eq 1 or #msg2 eq 0 select "1" else "2");
   out := out* Format(msg1, "|  ", false);
   out := out* VerboseFooter();
   if file then
      Write("ModAbVar-verbose.log",out);
   else
      print out;
   end if;
end procedure;
