freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODABVAR: Modular Abelian Varieties in MAGMA
 
                              William A. Stein        
                         
   FILE: compgrp.m
   DESC: Component groups

   Creation: 06/16/03 -- initial creation

TODO: Could easily add components groups of J_0(N) for various N,
since these are in papers of Mazur, Edixhoven, etc. 
      
 ***************************************************************************/

/*
HANDBOOK_TITLE: Tamagawa Numbers and Component Groups of Neron Models
*/

import "modabvar.m":
   Verbose;


/***************************************************************************

  << Component Groups >>

****************************************************************************/


intrinsic ComponentGroupOrder(A::ModAbVar, p::RngIntElt) -> RngIntElt
{The order of the component group of the special fiber of the 
Neron model of A over the algebraic closure of GF(p).  }
   require Type(BaseRing(A)) in {RngInt, FldRat} : "Argument 1 must " * 
      "be defined over Q.";
   require IsPrime(p) : "Argument 2 must be prime.";
   t, Af := IsAttachedToNewform(A);
   require t : "Argument 1 must be attached to a newform.";
   N := Level(Af);
   require N mod p^2 ne 0 : "No known algorithm to compute "*
      "the exact order of the component group of a general modular abelian variety "*
      "when p^2 divides the level.";
   ans := 1;
   require IsTrivial(DirichletCharacter(Af)) : 
           "Each factor Af of A must have trivial Dirichlet character.";
   M := ModularSymbols(Af);
   assert #M eq 1;
   M := M[1];
   return ComponentGroupOrder(M,p);
end intrinsic;

/***************************************************************************

  << Tamagawa Numbers >>

 ***************************************************************************/


intrinsic TamagawaNumber(A::ModAbVar) -> RngIntElt, RngIntElt, BoolElt
{Let c be the product of the Tamagawa numbers of A at primes of
bad reduction, where A is an abelian variety over Q attached to a newform.
This command returns a divisor of c, an integer some power of which is a 
multiple of c, and true if the divisor is provably equal to c.}
   Verbose("TamagawaNumber", 
      Sprintf("Computing product of Tamagawa numbers of A=%o.",A), "");
   require Type(BaseRing(A)) in {RngInt, FldRat} : "Argument 1 must " * 
      "be defined over Q.";
   bool, A_f := IsAttachedToNewform(A);
   require bool : "Argument 1 must be attached to a newform.";

   N := Level(A_f);
   divc := 1;
   mulc := 1;
   exact := true;
   for F in Factorization(N) do
      p := F[1];
      div_p, mul_p, exact_p := TamagawaNumber(A_f,p);
      divc := divc * div_p;
      mulc := mulc * mul_p;
      exact := exact and exact_p;
   end for;

   if exact then
      mulc := divc;
   else
      sqfree := &*[Integers()|F[1] : F in Factorization(mulc) | divc mod F[1] ne 0];
      mulc := divc * sqfree;
   end if;

   return divc, mulc, exact;
   
end intrinsic;

intrinsic TamagawaNumber(A::ModAbVar, p::RngIntElt) -> RngIntElt, RngIntElt, BoolElt
{A divisor of the Tamagawa number of A at p, an integer some power of which is a 
multiple of the Tamagawa number of A at p, and true if the divisor of the 
Tamagawa number is provably equal to the Tamagawa number of A.  The abelian variety
A must be attached to a newform.}
   Verbose("TamagawaNumber", 
      Sprintf("Computing Tamagawa number at %o of A=%o.",p,A), "");
   require Type(BaseRing(A)) in {RngInt, FldRat} : "Argument 1 must " * 
      "be defined over Q.";
   require IsPrime(p) : "Argument 2 must be prime.";
   
   if not assigned A`tamagawa_numbers then
      A`tamagawa_numbers := [];
   end if;
   if exists(a) { x[2] : x in A`tamagawa_numbers | x[1] eq p } then
      return a[1], a[2], a[3];
   end if;
   bool, A_f := IsAttachedToNewform(A);
   require bool : "Argument 1 must be attached to a newform.";
   exact := true;
   if Level(A_f) mod p ne 0 then
      return 1, 1, true;
   end if;
   eps := DirichletCharacter(A_f);
   if IsTrivial(eps) and Valuation(Level(A_f),p) eq 1 then
      cpbar := ComponentGroupOrder(A_f, p);
      wp := AtkinLehnerOperator(A_f,p);
      if wp eq -1 then
         div_cp := cpbar;
         mul_cp := cpbar;
      else // 2-torsion subgroup
         mul_cp := 2^Valuation(cpbar,2);
         if mul_cp mod 2 eq 0 then
            div_cp := 2;
         else
            div_cp := 1;
         end if;
         if mul_cp ne div_cp then
            exact := false;
        end if;
      end if;
   else
      div_cp := 1;
      mul_cp := p * &*[q : q in [2..2*Dimension(A_f)+1] | IsPrime(q)];
      exact := false;
   end if;
   if exact then
      mul_cp := div_cp;
   else
      sqfree := &*[Integers()|F[1] : F in Factorization(mul_cp) | div_cp mod F[1] ne 0];
      mul_cp := div_cp * sqfree;
   end if;
   if mul_cp eq 1 then
      exact := true;
   end if;
   Append(~A`tamagawa_numbers, <div_cp, mul_cp, exact>);
   return div_cp, mul_cp, exact;
end intrinsic;

