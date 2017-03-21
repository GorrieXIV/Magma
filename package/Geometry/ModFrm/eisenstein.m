freeze;

/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: eisenstein.m

   2007-09 (Steve):
      Change EisensteinSeries yet again!!  
      See the entry below (2006-10, item 2) for the story so far.
      In that change, I decided to list and store the EisensteinSeries
      for all the characters instead of just for M`DirichletCharacters
      (the set of Galois reps).
      But that meant I was wasting significant time and space. 
      Now, EisensteinSeries by default will compute, store and return 
      the series which have character in M`DirichletCharacters. 
      However when the vararg AllCharacters:=true, it will return all
      the series (just like now), but **store nothing**.
      Spaces satisfying IsGamma1 are not treated differently now 
      (whereas originally it listed all conjugates in this case).

      DimensionOfEisensteinSpace: it's slightly more efficient to work
      out the dimension in ComputeAllEisensteinSeries, which we now do.

   2007-03 (Steve):
      1) Add general Atkin-Lehner operators (before, there was only w_N).
       
      2) AtkinLehnerOnEisensteinSeries now returns only A, i instead of
         A*F, A, i, since the A*F was never used by calling functions.

      3) Revisit the first of the 2006-10 bugs.
         Reverting the fix in ComputeAllEisensteinSeries, and replacing 
         psi by psibar in q-expansions instead. 
         
         The definition of Eisenstein series (now) used in this package is, 
         exactly as in Miyake section 7.1,
            E_<chi,psi,t>(z) := Sum_{c,d} chi(c) * psi(d) / (c*T*z+d)^k
         where T = t*Conductor(psi).
         The q-expansion of this is some constant times 
            c_0 + sum_{m \geq 1}[sum_{n|m}psibar(n)n^{k-1}chi(m/n)] q^{mt}
         (see q-expansions.m).
         Before the 2006-10 fix, the psibar in this formula was completely 
         missing absent from the package. With that fix, some inconsistencies
         remained. 

         Now, I claim that at least constructing the Eisenstein series, 
         their q-expansions, and their Atkin-Lehner operators is all correct.

   2007-01 (Steve): 
         Fix minor bug in AtkinLehnerOnEisensteinModularFormsSpace: 
         (return matrix over FieldOfFractions(BaseRing(M)) instead of Q.

   2006-10 (Steve): 
      1) Fixed bug in ComputeAllEisensteinSeries 
         (by putting a bar on a character, see comment in the code)

      2) Corrected the previous (2006-04) bug fix. In fact the problem 
         came from EisensteinSeries, not DimensionOfEisensteinSpace.
         EisensteinSeries was using M`DirichletCharacters whereas it
         needs to use all conjugates (over Z) of these as well.
         
         Example 1: 
         > Qi := CyclotomicField(4); i := Qi.1;
         > Chi := DirichletGroup(25, Qi);
         > Mchi2 := ModularForms(Chi.1^2);
         > Dimension(Mchi2);
         // Previously returned 8, now gives 6
          
         Example 2 (apparently this was the example behind the 2006-04 fix):
         > G<chi>:=DirichletGroup(9,CyclotomicField(3));
         > M:=ModularForms(chi^2);
         > Dimension(M);  // Fixed 2006-04 (prior to that, returned 2)
         4
         > EisensteinSeries(M);
         // Now returns four series, previously only gave two 
         // (even after the 2006-04 fix)

   2006-04-12 (WAS): Fixed major bug in DimensionOfEisensteinSpace...
   
   01/04/04 (WAS):
        Fixed minor bug AtkinLehnerOnEisensteinModularFormsSpace(M, q)
        that affected
        "operators.m:function compute_Wq(M, q)"---in some cases WE was over Z,
        so DirectSum(WS,WE) would terminate with an error, since WS is over Q.

   07/06/03(WAS): Fixed bug in ExtendBaseMaximal introduced by changing
             how Dirichlet characters work.  I had assumed that the parent
             after base extension had properties that it didn't have.  -- WAS
             Also bug in construction of Eisenstein series -- got the wrong 
             ones in some cases!  
   
   Revision 1.6  2002/09/11 18:22:18  was
   Fixed bug in ComputeAllEisensteinSeries that manifest itself
   when some of the characters eps that define M do not satisfy
   eps(-1) eq (-1)^k.

   Revision 1.5  2002/09/11 18:16:04  was
   nothing.

   Revision 1.4  2002/09/11 18:12:43  was
   Rewrote ExtendBaseMaximal to be more efficient and fix a bug.

   Revision 1.3  2002/01/17 03:54:33  was
   added a comment

   Revision 1.2  2001/10/25 02:53:03  was
   Fixed serious bug in function ExtendBaseMaximal(eps) that occured when
   the user "stupidly" created a character like
         G<a>:=DirichletGroup(27, CyclotomicField(4));
   (Note that 4 doesn't divide EulerPhi(27)!)
   Also fixed a bug in ComputeAllEisensteinSeries that might appear when there
   is more than one character.

   Revision 1.1  2001/05/30 18:51:48  was
   Initial revision


   [Theorem 15, page IV-39 in Ogg's Modular Forms book looks very relevant.]

 ***************************************************************************/

forward EisensteinBasisHelper;

import "misc.m":  EchelonPowerSeriesSequence;

import "predicates.m": SpaceType;

import "q-expansions.m": ApproximatePrecisionBound, 
                         BasisOfAmbientEisensteinSpace;

function QZeta(n)
   assert Type(n) eq RngIntElt; 
   assert n ge 1;
   if n le 2 then
      return RationalField();
   else
      return CyclotomicField(n);
   end if;
end function;

function ExponentOfZModN(N)
   // This could probably be optimized.
   return Exponent(UnitGroup(Integers(N)));
end function;

/* Let eps : (Z/N)^* ----> Q(zeta_n) be a Dirichlet character.
   This function returns an equal Dirichlet character
       chi : (Z/N)^* ----> Q(zeta_m)
   where m is LCM(n, exponent of (Z/N)^*).
*/
function ExtendBaseMaximal(eps)

   assert Type(eps) eq SeqEnum;
   assert #eps gt 0;
   assert Type(eps[1]) eq GrpDrchElt;
  
   N := Modulus(eps[1]);
   g := ExponentOfZModN(N);
   if g eq 1 then
      g := 2;
   end if;
   _, r := DistinguishedRoot(Parent(eps[1]));

   R := QZeta(LCM(g,r));
   G := DirichletGroup(Modulus(eps[1]),R);
   ans := [G!e : e in eps];
   return ans;
end function;


function MakeEisensteinSeries(M,chi,psi,t)
   assert Type(M) eq ModFrm;
   assert Type(chi) eq GrpDrchElt;
   assert Type(psi) eq GrpDrchElt;
   assert Type(t) eq RngIntElt;
   assert Level(M) mod (Conductor(chi)*Conductor(psi)*t) eq 0;

   f := New(ModFrmElt);
   f`parent :=
          BaseExtend(EisensteinSubspace(M), QZeta(LCM(Order(chi),Order(psi))));
   f`eisenstein :=<MinimalBaseRingCharacter(AssociatedPrimitiveCharacter(chi)),
                   MinimalBaseRingCharacter(AssociatedPrimitiveCharacter(psi)),
                    t, chi, psi>;
   return f;
end function;

function IsInSequence(x, seq)
   for i in [1..#seq] do
      if x eq seq[i] then
         return true, i;
      end if;
   end for;
   return false, _;
end function;

function ComputeAllEisensteinSeries(M : all:=false)
   assert Type(M) eq ModFrm;
   assert SpaceType(M) in {"full", "eis"};

   ans := [* *]; 
   N   := Level(M);
   k   := Weight(M);

   eps := ExtendBaseMaximal(DirichletCharacters(M));
   K   := BaseRing(eps[1]);
   Chi := Universe(eps);
   Chi1 := DirichletGroupCopy(Chi);  
       // work in this copy, make a big mess, then toss the lot at the end

   if all then
      // include all conjugates in the list of characters. 
      new_eps := [];
      for chi in eps do 
        e := Order(chi);
        if e in {1,2} then Append( ~new_eps, chi); continue; end if;
        new_eps cat:= [ chi^k : k in [1..e-1] | GCD(e,k) eq 1 ];
      end for;
      eps := new_eps;
   end if;

   // Divide up Chi by conductor:
   C   := [[] : i in [1..N]];
   for e in Elements(Chi1) do
      Append(~C[Conductor(e)],e);
   end for;

/* Find all pairs chi, psi such that
     chi * psibar = eps (nebentypus)
   See [Miyake] Lemma 7.1.1. 
*/
   dims := [0 : i in [1..#eps]];  // record dimensions
   for L in Divisors(N) do
      GL := (k eq 1) select [cc : cc in C[L] | IsEven(cc)]
                      else   C[L];
      for R in Divisors(N div L) do
         GR := C[R];
  
         for chi in GL do
            for psi in GR do
               if Evaluate(chi*psi,-1) eq (-1)^k then
                  in_eps, idx := IsInSequence( chi*(psi^-1), eps);
                  if in_eps then
                     for t in Divisors(N div (R*L)) do
                        if Weight(M) eq 2 and t eq 1 and 
                              IsTrivial(chi) and IsTrivial(psi) then
                           // do nothing
                        else
                           Append(~ans, MakeEisensteinSeries(M, Chi!chi, Chi!psi, t));      
                           dims[idx] +:= 1;
                        end if;
                     end for;
                  end if;
               end if;
            end for;
         end for;
      end for;
   end for;
   dim := &+[ EulerPhi(Order(eps[i]))*dims[i] : i in [1..#eps]];

   if all then 
      return ans, _;
   else
      return ans, dim;
   end if;
end function;


intrinsic EisensteinSeries(M::ModFrm : AllCharacters:=false) -> List
{List of the Eisenstein series associated to M.}
/*   
   chi is a primitive character of conductor L
   psi is a primitive character of conductor R
   RLt divides N
   chi*psi = eps, or if gamma_1, the parity condition.
  
   This function can definitely be optimized much more.
*/
   require Characteristic(BaseRing(M)) eq 0 : 
           "Argument 1 must have characteristic 0.";
   if not assigned M`eisenstein_series then
      case SpaceType(M):
         when "full", "eis": 
            if AllCharacters then
               return ComputeAllEisensteinSeries(M : all:=true); // don't store them (too bulky)
            end if;
            M`eisenstein_series, dim := ComputeAllEisensteinSeries(M : all:=false);
            E := EisensteinSubspace(AmbientSpace(M));
            E`dimension := dim;
         when "full_half_int":
            error "Eisenstein series not implemented for half-integral weight";
         when "cusp", "cusp_new", "cusp_half_int":
            M`eisenstein_series := [* *]; 
         when "eis_new":
            require not AllCharacters: 
              "The optional parameter AllCharacters must be 'false' for newform spaces";
            M`eisenstein_series := [* *];
            for class in Newforms(M) do
               for f in class do
                  Append(~M`eisenstein_series, f);
               end for;
            end for;
         else: 
            error "Bug in EisensteinSeries.";
      end case; 
   end if;

   return M`eisenstein_series;
end intrinsic;


function DimensionOfEisensteinSpace(M)
   assert Type(M) eq ModFrm;
   assert IsAmbientSpace(M);

   N := Level(M);
   if IsGamma0(M) then
      if IsOdd(Weight(M)) then
         dim := 0;
      else
         dim := &+[EulerPhi(GCD(d,N div d)) : d in Divisors(N)];
         if Weight(M) eq 2 then
            dim -:= 1;
         end if;
      end if;
   elif IsGamma1(M) then
      if N in {1, 2} then
         dim := N;
      elif N eq 4 then 
         if IsOdd(Weight(M)) then
            dim := 2;
         else
            dim := 3;
         end if;
      else
         dim := &+[EulerPhi(GCD(d,N)) : d in [1..N]] div 2;
      end if;
      if Weight(M) eq 1 then
         dim div:= 2;
      elif Weight(M) eq 2 then
         dim -:= 1;
      end if;
   else
      // Calls ComputeAllEisensteinSeries which stores series and gets dimension
      if not assigned M`eis or not assigned M`eis`dimension or M`eis`dimension eq -1 then
         _ := EisensteinSeries(M : AllCharacters:=false);
      end if;
      assert M`eis`dimension ge 0;  
      dim := M`eis`dimension;
   end if;
   return dim;
end function;

// Return obj_q, obj_qq (the q- and q-prime parts of obj)
// satisfying obj = obj_q * obj_qq,
// where obj is either a RngIntElt or a GrpDrchElt.

function q_qprime_split(obj,q)  
   if Type(obj) eq RngIntElt then
      q := &*[Integers()| ff[1]^ff[2] : ff in Factorization(obj) | q mod ff[1] eq 0];
      qq := obj div q;
      assert q*qq eq obj and GCD(q,qq) eq 1;
      return q, qq;
   elif Type(obj) eq GrpDrchElt then
      q, qq := q_qprime_split( Modulus(obj), q);
      chis := Decomposition(obj);
      assert &and[ Modulus(obj) mod Modulus(chi) eq 0 : chi in chis ];
      chi_qs := [* chi : chi in chis | q mod Modulus(chi) eq 0 *];
      chi_qqs := [* chi : chi in chis | qq mod Modulus(chi) eq 0 *];
 error if #chis ne #chi_qs + # chi_qqs, 
  "Mistake occurred splitting the character";
      // multiply together the lists (can't use &* here):
      chi_q := DirichletGroup(1)! 1;
      for chi1 in chi_qs do chi_q *:= chi1; end for;
      chi_qq := DirichletGroup(1)! 1;
      for chi1 in chi_qqs do chi_qq *:= chi1; end for;
      error if obj ne chi_q*chi_qq, "Mistake occurred splitting the character";
      return chi_q, chi_qq;
   end if;
end function;

function AtkinLehnerOnEisensteinSeries(E,q)
   assert Type(E) eq ModFrmElt;
   assert IsEisensteinSeries(E);
   k := Weight(E);
   assert IsEven(k);   // This is not strictly necessary!
                       // we do this to avoid thinking about how
                       // to deal with N^(k/2).
   M := AmbientSpace(Parent(E));
   assert IsGamma0(M) or IsGamma1(M) or 
          // (&and [e^2 eq 1 : e in DirichletCharacters(M)]);
          (&and [ Conductor(e^2) eq 1 : e in DirichletCharacters(M)]);

   _,_,t,chi,psi := Explode(EisensteinData(E));
   L := Conductor(chi);
   R := Conductor(psi);
   N := Level(M);   

   // Adjust q so that q and qq:=N/q are coprime.
   error if q eq 1 or N mod q ne 0, 
         "q should be a nontrivial factor of the level";
   q, qq := q_qprime_split(N, q);

   if q eq N then 
     // ORIGINAL CASE (WAS)
     A := N^(k div 2) / (R*t)^k * chi(-1);
     
     t_new   := N div (R*L*t);
     chi_new := psi;
     psi_new := chi;
   
   else
     /* NEW CASE (Steve)
       (generalises the old case, but keep using the old case anyway...)
     Notation: 
       Let T = R*t. Then 
         E_<chi,psi,T>(z) := Sum_{c,d} chi(c) * psi(d) / (c*T*z+d)^k
       Split everything into its q-part and q-prime part, 
       eg T = T_q*T_qq, chi = chi_q*chi_qq 
       (note: we arranged above that N_q = q and N_qq = qq)
       
     I calculated (using the matrix eta_q as defined by Miyake) that 
       E_<chi,psi,T> | eta_q = A * E_<chi_new,psi_new,T_new>
     where A, chi_new, psi_new, T_new are as defined below.
     */

     T := R*t;
     T_q, T_qq := q_qprime_split(T, q);
     chi_q, chi_qq := q_qprime_split(chi, q);
     psi_q, psi_qq := q_qprime_split(psi, q);

     A := q^(k div 2) / T_q^k * chi_q(-T_qq)^-1 * chi_qq(T_q)^-1 
                              * psi_q(T_qq) * psi_qq(T_q);
     chi_new := psi_q * chi_qq; 
     psi_new := chi_q * psi_qq;
     T_new   := q div T_q * T_qq;
     t_new := T_new div Conductor(psi_new);
   end if;       
   
   ES := EisensteinSeries(M);
   for i in [1..#ES] do F := ES[i];
      eis := EisensteinData(F);            
      if eis[3] eq t_new and eis[4] eq chi_new and eis[5] eq psi_new then
         return A, i;
      end if;
   end for;
   error "OH NO!!  Didn't find Eisenstein series!";
end function;

function AtkinLehnerOnEisensteinSeriesBasis(M,q)
   assert Type(M) eq ModFrm;
   ES := EisensteinSeries(M);
   if #ES eq 0 then
      return MatrixAlgebra(RationalField(),0)!1;
   end if;
   k := Weight(M);
   assert IsEven(k);   // This is not strictly necessary!
                       // we do this to avoid thinking about how
                       // to deal with N^(k/2).
   assert IsGamma0(M) or IsGamma1(M) or 
          // (&and [e^2 eq 1 : e in DirichletCharacters(M)]);
          (&and [ Conductor(e^2) eq 1 : e in DirichletCharacters(M)]);

   chi := EisensteinData(ES[1])[4];
   K := BaseRing(Parent(chi));
   W := MatrixAlgebra(K,#ES)!0;

   for i in [1..#ES] do E := ES[i];
      c, j := AtkinLehnerOnEisensteinSeries(E,q);
      W[i,j] := c;
   end for;
   okay := W^2 eq 1 or 
           W^2 eq -1 and q ne Level(M) and not IsGamma0(M);
   error if not okay, "The Atkin-Lehner operator obtained is wrong";
   return W;
end function;

function ChangeOfBasis_EisensteinSeries_To_CanonicalBasis(M)
   assert Type(M) eq ModFrm;
   assert IsEisenstein(M);

   B  := Basis(M);   
   ES := EisensteinSeries(M);
   assert #ES eq Dimension(M);

   if #ES eq 0 then
      return MatrixAlgebra(RationalField(),0)!1;
   end if;

   n := PrecisionBound(M);
   chi := EisensteinData(ES[1])[4];
   ES_qexp := [PowerSeries(e,n) : e in ES];      
   M_qexp := [PowerSeries(f,n) : f in Basis(M)];
   K := BaseRing(Parent(chi));
   Eis := RMatrixSpace(K,#ES,n)! (&cat [[Coefficient(e,i) : i in [0..n-1]] : e in ES_qexp]);
   Std := RMatrixSpace(K,Dimension(M),n)! (&cat [[Coefficient(b,i) : i in [0..n-1]] : 
                   b in M_qexp]);
   return Solution(Std,Eis);
end function;

function AtkinLehnerOnEisensteinModularFormsSpace(M, q)
   assert Type(q) eq RngIntElt;
   assert Type(M) eq ModFrm;
   assert IsEisenstein(M);
   if Dimension(M) eq 0 then  
      // Need field of fractions, since Atkin-Lehner doesn't
      // preserve integrality, and "function compute_Wq(M, q)"
      // in ModFrm/operators.m assumes this. 
      return MatrixAlgebra(FieldOfFractions(BaseRing(M)),0)!1;
   end if;

   k := Weight(M);
   assert IsEven(k);   // This is not strictly necessary!
                       // we do this to avoid thinking about how
                       // to deal with N^(k/2).
   assert IsGamma0(M) or IsGamma1(M) or 
          // (&and [e^2 eq 1 : e in DirichletCharacters(M)]);
          (&and [ Conductor(e^2) eq 1 : e in DirichletCharacters(M)]);
          // TO DO: why the last restriction ??

   W := AtkinLehnerOnEisensteinSeriesBasis(M, q);
   C := ChangeOfBasis_EisensteinSeries_To_CanonicalBasis(M);
   W := C^(-1)*W*C;
   // fix by Steve:
   //return MatrixAlgebra(RationalField(),Nrows(W))!Eltseq(W);      
   return MatrixAlgebra(FieldOfFractions(BaseRing(M)),Nrows(W))!Eltseq(W);  
end function;

