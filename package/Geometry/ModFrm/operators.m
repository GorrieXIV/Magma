freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: operators.m

   09/08 (Steve) - changed precision bound used in ApplyHecke:
                   was PrecisionBound(Ambient(Parent(f))), 
                   now PrecisionBound(Parent(f) : Exact).

   01/07 (Steve) - add easy-to-find syntax for applying operators,
                   HeckeOperator(n,f) and AtkinLehnerOperator(n,f) 

   02/09/05 (CF) change to reflect new cyclo conventions  
   
   01/04/04 (WAS) - fixed bug in the require statement in 
          "intrinsic AtkinLehnerOperator(M::ModFrm, q::RngIntElt)"
       
     

   04/06/03 (WAS) - added caching of eigenvector for T2 when
                    computing level 1 charpolys.

   04/06/03 (WAS) - found bug in charpoly routine: In a part of HeckePolynomial
                    it was finding charpoly of Tn instead of T2 which hanged.

   04/05/03 (WAS) - fixed bug in HeckeOperator (it said BaseField instead
                    of BaseRing at a certain point).

   $Header: /home/was/magma/packages/ModFrm/code/RCS/operators.m,v 1.9 2002/10/20 06:30:02 was Exp was $

   $Log: operators.m,v $
   Revision 1.9  2002/10/20 06:30:02  was
   Fixed serious bug in function WqOnNewSpace(M, q, prec) that meant Wq was
   computed wrt wrong basis.

   Revision 1.8  2002/05/04 18:33:24  was
   Made AtkinLehnerOperator much much more efficient by not computing T_p.

   Revision 1.7  2002/04/25 05:34:11  was
   some improvements to HeckePolynomial in the level 1 case.

   Revision 1.6  2002/04/25 00:21:40  was
   *** empty log message ***

   Revision 1.5  2001/07/13 02:33:01  was
   Changed a name.

   Revision 1.4  2001/06/08 06:49:36  was
   Added AtkinLehnerEigenvalue

   Revision 1.3  2001/05/30 18:56:17  was
   Created.

   Revision 1.2  2001/05/16 04:11:40  was
   *** empty log message ***

   Revision 1.1  2001/05/16 03:52:06  was
   Initial revision

      
 ***************************************************************************/

forward 
   ApplyHeckeOperator, 
   ComputeHeckePolynomialUsingHeckeOperator,
   Tn, Tp;

import "eisenstein.m":
   AtkinLehnerOnEisensteinModularFormsSpace;

import "level1.m": 
   Level1CharacteristicPolynomialOfTp,
   EigenvectorOfMatrixWithCharpoly;

import "modular_symbols.m": 
   MF_ModularSymbols;

import "predicates.m": 
   AssociatedSpaceOverZ, 
   SpaceType, 
   SpaceTypeParam;

import "q-expansions.m": 
   PowerSeriesInternal;

function field_of_fractions(R)
   t := Type(R);
   if ISA(t, Fld) then 
      return R;
   elif ISA(t, RngOrd) then
      return NumberField(R);
   else 
      return FieldOfFractions(R);
   end if;
end function;

intrinsic HeckeOperator(n::RngIntElt, f::ModFrmElt) -> ModFrmElt
{Apply the Hecke operator T_n to f.}
   return f*HeckeOperator(Parent(f),n);
end intrinsic;

intrinsic HeckeOperator(M::ModFrm, n::RngIntElt) -> AlgMatElt
{Matrix representing the n-th Hecke operator on M.}
   //require IsGamma0(M) : 
   //  "Hecke operator computation currently only supported for Gamma_0(N).";
   require #chars eq 1 and Order(chars[1]) in {1,2} where chars is DirichletCharacters(M) :
      "Hecke operator computation currently only supported for spaces " *
      "with a single character that takes values +/-1.";
   requirege n, 1;
   if not assigned M`hecke_operator then
      M`hecke_operator := [];
   end if;
   if exists(i) { i : i in [1..#M`hecke_operator]
                             | M`hecke_operator[i][1] eq n } then
      return M`hecke_operator[i][2];
   end if;
   if n eq 1 then
      Tn := MatrixAlgebra(BaseRing(M),Dimension(M))!1;
   else
      Tn := MatrixAlgebra(BaseRing(M),Dimension(M))!
          &cat[Eltseq(ApplyHeckeOperator(n,M.i)) : i in [1..Dimension(M)]];
   end if;
   Append(~M`hecke_operator,<n,Tn>);
   return Tn;
end intrinsic;

function ApplyHeckeOperator(n, f)
   // The image of f under the n-th Hecke operator.
   assert Type(n) eq RngIntElt;
   assert Type(f) eq ModFrmElt;
   //assert IsGamma0(Parent(f)); // allow spaces with a single quadratic character
   if n eq 1 then
      return f;
   end if;
   prec := (n+1)*PrecisionBound(Parent(f) : Exact); 
   Tnf := Tn(Level(f), DirichletCharacters(Parent(f))[1], Weight(f), n, 
             PowerSeriesInternal(f, prec));
   return Parent(f)!Tnf;
end function;

intrinsic AtkinLehnerEigenvalue(f::ModFrmElt, q::RngIntElt) -> RngElt
{The eigenvalue of the Atkin-Lehner involution W_q on the cuspidal newform f.}
   if assigned f`elliptic_curve and not assigned f`mf_modular_symbols then
      require false : "Not yet programmed for elliptic curve newforms.";
   end if;
   require assigned f`is_newform and f`is_newform and 
             assigned f`mf_modular_symbols : "f must be a cuspidal newform.";
   Wq := AtkinLehner(f`mf_modular_symbols,q);
   assert IsDiagonal(Wq);
   return Wq[1,1];
end intrinsic;


function CoerceUnivariatePolynomialElement(R, f)
   assert Type(R) eq RngUPol;
   assert Type(f) eq RngUPolElt;
   return &+[R.1^i*(R!(Integers()!Coefficient(f,i))) : i in [0..Degree(f)]];
end function;


function GaloisConjugatesOfPolynomial(f)
   assert Type(f) eq RngUPolElt;
   F := BaseRing(Parent(f));
   if Degree(F) eq 1 then
      return [f];
   end if;
   assert Type(F) eq FldCyc;
   X := Parent(f).1;
   ans := [f];
   m := CyclotomicOrder(F);
   for n in [2..m] do
      if GCD(n, m) eq 1 then
        Append(~ans,&+[Conjugate(Coefficient(f,j),n)*X^j : j in [0..Degree(f)]]); 
      end if;
   end for;
   return ans;
end function;

function ComputeHeckePolynomialOfModularSymbolsSpace(M, modsym, n, Proof)
   assert Type(M) eq ModFrm;
   assert Type(modsym) eq ModSym;
   assert Type(n) eq RngIntElt and n ge 1;
   assert Type(Proof) eq BoolElt;

   if Dimension(M) eq 0 then
      return PolynomialRing(BaseRing(M))!1;
   end if;
   f := HeckePolynomial(modsym, n : Proof := Proof);
   normf := &*GaloisConjugatesOfPolynomial(f);
   return normf;

end function;

function CharpolyOfEigenvalue(a)
   if Type(Parent(a)) eq FldRat then
      return PolynomialRing(RationalField()).1 - a;
   end if;
   return CharacteristicPolynomial(a);
end function;

function ComputeHeckePolynomialUsingEisensteinSeries(M,n)
   assert Type(M) eq ModFrm;
   assert IsEisenstein(M);
   assert GCD(Level(M),n) eq 1;

   if Dimension(M) eq 0 then
      return PolynomialRing(BaseRing(M))!1;
   end if;

// This is incorrect, because the n-th coefficient of the 
// Eisenstein series need not be the Eigenvalue of T_n,
// except in some special cases.   
   error "Computing Hecke polynomial on Eisenstein series not yet implemented.";

   E := EisensteinSeries(M);
   R := PolynomialRing(CyclotomicField(EulerPhi(Level(M))));
   F := &*[R|R.1 - R!Coefficient(PowerSeriesInternal(f,n+1),n) : f in E];
   return F;
end function;


function ComputeHeckePolynomialUsingModularSymbols(M,n, Proof)
   assert Type(M) eq ModFrm;
   assert Type(n) eq RngIntElt;
   assert Type(Proof) eq BoolElt;

   if Dimension(M) eq 0 then
      return PolynomialRing(BaseRing(M))!1;
   end if;
   if IsEisenstein(M) then
      if IsNew(M) then
         if IsGamma0(M) then
             return ComputeHeckePolynomialUsingHeckeOperator(M,n,Proof);
         else
             error "Not yet programmed -- I haven't coded an algorithm to compute "*
               "the char poly of T_n on the new Eisenstein series when n divides "*
               "the level (and we're not in the Gamma_0(N) case).";
         end if;
      end if;
      modsym := MF_ModularSymbols(M,0);
      return &*[ComputeHeckePolynomialOfModularSymbolsSpace(M,m,n,Proof) : m in modsym];
   elif IsCuspidal(M) then
      modsym := MF_ModularSymbols(M,+1);
      return &*[ComputeHeckePolynomialOfModularSymbolsSpace(M,m,n,Proof) : m in modsym];
   end if;

   return ComputeHeckePolynomialUsingModularSymbols(EisensteinSubspace(M),n,Proof) * 
          ComputeHeckePolynomialUsingModularSymbols(CuspidalSubspace(M),n,Proof) ;
end function;



function ComputeHeckePolynomialUsingHeckeOperator(M, n, Proof)
   assert Type(M) eq ModFrm;
   assert Type(n) eq RngIntElt;
   assert Type(Proof) eq BoolElt;
   Tn := HeckeOperator(M,n);
   if Type(BaseRing(M)) in {RngInt, FldRat} then
      return CharacteristicPolynomial(Tn : Al := "Modular", Proof := Proof);
   end if;
   return CharacteristicPolynomial(Tn);
end function;


intrinsic HeckePolynomial(M::ModFrm, n::RngIntElt :
                  Proof := true) -> AlgMatElt
{The characteristic polynomial of the n-th Hecke operator on M.}
   require n ge 1 : "Argument 2 must be at least 1.";
   if not assigned M`hecke_polynomial then
      M`hecke_polynomial := [];   // sequence of pairs <n,f(x)>
   end if;
 
   if exists(i) { i : i in [1..#M`hecke_polynomial]
                             | M`hecke_polynomial[i][1] eq n } then
      return M`hecke_polynomial[i][2];
   end if;
 
   vprint ModularForms, 2: "Computing Hecke polynomial of index", n;
   if n eq 1 then
      f := (PolynomialRing(BaseRing(M)).1-1)^Dimension(M);
   elif assigned M`made_from_newform then
      f := CharpolyOfEigenvalue(
              Coefficient(PowerSeries(M`made_from_newform,n+1),n));
   elif Characteristic(BaseRing(M)) eq 0 and Level(M) eq 1 
              and n le Dimension(CuspidalSubspace(M)) and Proof eq false then
      A := AssociatedSpaceOverZ(CuspidalSubspace(M));
      assert Dimension(A) eq Dimension(CuspidalSubspace(M));
      d := Dimension(A);
      T2 := HeckeOperator(A,2);   // yes, T2, because my algorithm uses T2!!
      if exists(i) { i : i in [1..#A`hecke_polynomial] | A`hecke_polynomial[i][1] eq n } then
          f2 := A`hecke_polynomial[i][2];
      else
         vprint ModularForms, 2: 
           "Computing characteristic polynomial of T_2 using standard algorithm.";
          t := Cputime();
          f2  := CharacteristicPolynomial(T2 : Proof := Proof, Al := "Modular");
          vprintf ModularForms, 2: "Time = %o seconds\n", Cputime(t);
          Append(~A`hecke_polynomial, <2, f2>);
      end if;

      if not assigned A`t2_eigenvector then
         T2Q := MatrixAlgebra(RationalField(),Nrows(T2))!Eltseq(T2);
         f2Q := PolynomialRing(RationalField())!f2;
         A`t2_eigenvector := EigenvectorOfMatrixWithCharpoly(T2Q, f2Q);
      end if;
      
      if n gt 2 then
         cuspidal_part := Level1CharacteristicPolynomialOfTp(Weight(A),n,d,A`t2_eigenvector);
      else
         cuspidal_part := f2;
      end if;        
      eisenstein_part := ComputeHeckePolynomialUsingEisensteinSeries(EisensteinSubspace(M), n);
      f :=  cuspidal_part * eisenstein_part;

   else
      MC := AssociatedSpaceOverZ(M);
      if GCD(Level(M),n) eq 1 then
         f_cuspidal := ComputeHeckePolynomialUsingModularSymbols(
                            CuspidalSubspace(MC), n, Proof);      
         f_eisenstein := ComputeHeckePolynomialUsingEisensteinSeries(
                            EisensteinSubspace(MC), n);
         f := f_cuspidal * f_eisenstein;
      else
         f := ComputeHeckePolynomialUsingModularSymbols(MC, n, Proof);
      end if;
   end if;
   f := CoerceUnivariatePolynomialElement(PolynomialRing(BaseRing(M)), f);
   Append(~M`hecke_polynomial, <n, f>);
   return f;
end intrinsic;

function Tp(N, eps, k, p, r, f)
   assert Type(p) eq RngIntElt;
   assert Type(r) eq RngIntElt;
   assert Type(f) eq RngSerPowElt;

   if r gt 1 then
      return Tp(N,eps,k, p,1,Tp(N,eps,k,p,r-1,f)) 
                     - Evaluate(eps,p)*p^(k-1)*Tp(N,eps,k,p,r-2,f);
   end if;
   if r eq 1 then
      R := Parent(f);
      q := R.1;
      prec := Floor(((AbsolutePrecision(f)-1)/p) + 1);
      h := &+[R|Coefficient(f,n*p)*q^n + 
                     Evaluate(eps,p)*p^(k-1)*Coefficient(f,n)*q^(n*p) :
                    n in [0..prec-1]] + O(q^prec);
      return h; 
   end if;
   if r eq 0 then
      return f;
   end if;
end function;

function Tn(N, eps, k, n, f)
   // The image T_n(f) of f under the Hecke operator T_n on level-N
   // weight-k modular forms with character eps.
   assert Type(N) eq RngIntElt and N ge 1;
   assert Type(n) eq RngIntElt and n ge 1;
   assert Type(k) eq RngIntElt and k ge 1;
   assert Type(eps) eq GrpDrchElt;
   assert Type(f) eq RngSerPowElt;

   for p in Factorization(n) do
      f := Tp(N, eps, k, p[1],p[2], f);
   end for;
   return f;
end function;

/*
intrinsic UOperator(f::ModFrmElt, p::RngIntElt) -> ModFrmElt
{The modular forms f(q^p).}
   error "not written.";
end intrinsic;
*/

// write each element of B2 as a linear combination
// of the elements of B1.
function PowerSeriesCoordinates(B1, B2)
   if #B1 eq 0 then
      return [];
   end if;
   K := field_of_fractions(BaseRing(Parent(B1[1])));
   prec := AbsolutePrecision(B1[1]);
   V := VectorSpace(K, prec);
   C1 := [V![Coefficient(f,i) : i in [0..prec-1]] : f in B1];
   C2 := [V![Coefficient(f,i) : i in [0..prec-1]] : f in B2];
   W := VectorSpaceWithBasis(C2);
   D1 := [Coordinates(W,v) : v in C1];
   return D1;
end function;

function BottomBaseRing(R)
   while true do 
      if Type(R) in {RngInt, FldRat, FldFin, RngIntRes} then 
         return R;
      end if;
      R := BaseRing(R);
   end while;
end function;

// These two intrisics added by Steve/MW
intrinsic CuspidalProjection(f::ModFrmElt) -> ModFrmElt
{The projection of f onto the cuspidal part of the ambient space.}
   M:=Parent(f);
   R:=BaseRing(M);
   // tensor with Q if appropriate
   if R cmpeq Integers() then 
      RQ:=Rationals();
   elif Type(R) eq RngOrd then 
      RQ:=NumberField(R);
   else 
      RQ:=R;
   end if;
   require ISA(Type(RQ),Fld) or ISA(Type(BottomBaseRing(RQ)), Fld):
     "Must be able to divide by integers in the base ring of the given form";
   if R cmpne RQ then 
      M,toM:=BaseExtend(M,RQ);
      f:=f@toM;
   end if;
   C:=CuspidalSubspace(M); E:=EisensteinSubspace(M);
   if Dimension(C) eq 0 then return C!0; end if;
   prec := PrecisionBound(M : Exact);
   CE:=[PowerSeriesInternal(x,prec) : x in Basis(C)] cat 
       [PowerSeriesInternal(x,prec) : x in Basis(E)];
   psc:=PowerSeriesCoordinates([PowerSeriesInternal(f,prec)],CE)[1];
   return C!Vector([psc[i] : i in [1..Dimension(C)]]); 
end intrinsic;

intrinsic EisensteinProjection(f::ModFrmElt) -> ModFrmElt
{The projection of f onto the Eisenstein part of the ambient space.}
   M:=Parent(f);
   R:=BaseRing(M);
   // tensor with Q if appropriate
   if R cmpeq Integers() then 
      RQ:=Rationals();
   elif Type(R) eq RngOrd then 
      RQ:=NumberField(R);
   else 
      RQ:=R;
   end if;
   require ISA(Type(RQ),Fld) or ISA(Type(BottomBaseRing(RQ)), Fld):
     "Must be able to divide by integers in the base ring of the given form";
   if R cmpne RQ then 
      M,toM:=BaseExtend(M,RQ);
      f:=f@toM;
   end if;
   C:=CuspidalSubspace(M); E:=EisensteinSubspace(M);
   if Dimension(E) eq 0 then return E!0; end if;
   prec := PrecisionBound(M : Exact);
   EC:=[PowerSeriesInternal(x,prec) : x in Basis(E)] cat 
       [PowerSeriesInternal(x,prec) : x in Basis(C)];
   psc:=PowerSeriesCoordinates([PowerSeriesInternal(f,prec)],EC)[1];
   return E!Vector([psc[i] : i in [1..Dimension(E)]]); 
end intrinsic;

// The matrix A is written wrt the basis B1 of power series.  The function
// B2 return the matrix A written wrt to the basis B2.
function ChangeBasis(A, B1, B2)
   assert Type(A) eq AlgMatElt;
   assert Type(B1) eq SeqEnum;
   assert Type(B2) eq SeqEnum;
   assert #B1 eq #B2;
   assert #B1 eq Degree(Parent(A));

   n := #B1;
   if n eq 0 then
      return A;
   end if;
   K := field_of_fractions(BaseRing(Parent(A)));
   C := PowerSeriesCoordinates(B1, B2);
   S := MatrixAlgebra(K, n)!(&cat[Eltseq(v) : v in C]);
   return S^(-1)*A*S;
end function;


// The matrix Wq of Atkin Lehner q on Basis(M), for q prime.
// Here M must be completely new, weight >= 2.
function WqOnNewSpace(M, q, prec) 
   assert IsIdentical(M, NewSubspace(M));
   N := Level(M);
   if Dimension(M) eq 0 or Valuation(N, q) lt 1 then
      return MatrixAlgebra(BaseRing(M),Dimension(M))!1;
   end if;
/* Don't do this -- it is very very very slow, though conceptually simple.
   elif Valuation(N, q) eq 1 then   
      // use that Wq = -Tq/q^(k/2-1) on newforms when q is prime.
      return -(1/q^((Weight(M) div 2)-1))* HeckeOperator(M,q);
*/
   D := [];
   B := [];
   for i in [1..NumberOfNewformClasses(M)] do
      f := Newform(M,i);
      eps := AtkinLehnerEigenvalue(f,q);
      D cat:= [eps : i in [1..Dimension(Parent(f))]];
      B cat:= [PowerSeriesRing(BaseRing(M))!PowerSeriesInternal(g,prec) : g in Basis(Parent(f))];
   end for;
   assert #D eq Dimension(M);
   Wq := DiagonalMatrix(MatrixAlgebra(Rationals(),Dimension(M)), D);
   // Now change from the B basis that Wq is written wrt to Basis(M),
   // which is what we want.
   return ChangeBasis(Wq, B, [PowerSeriesInternal(f,prec) : f in Basis(M)]);   
end function;

// Matrix of Wq on image of M at level Level(M)*t on the basis B, which
// is returned as the second part.
// M should be a ModFrm of even integral weight,
// q should be prime and prec is the precision of computations.
function WqOnImageOfNewSpace(M, q, t, prec)
   K := field_of_fractions(BaseRing(M));
   k := Weight(M);  
   assert IsEven(k);
   WqOld := WqOnNewSpace(M, q, prec);
   x := PowerSeriesRing(K).1;
   B := [];
   WqB := [];
   qq := q^Valuation(Level(M)*t,q);
   for f in Basis(M) do
      ps := PowerSeriesInternal(f,prec);
      fWq := PowerSeriesInternal(f*WqOld,prec);
      for d in Divisors(t) do
         Append(~B, Evaluate(ps,x^d) + O(x^prec));
         beta := Valuation(t, q);
         gamma := Valuation(d, q);
         dd := Integers()!(q^(beta-2*gamma)*d);
         pow := (k div 2)*(beta-2*gamma);
         g := Evaluate(fWq,x^dd)*q^pow + O(x^prec);
         Append(~WqB, g);
      end for;
   end for;
   C := PowerSeriesCoordinates(B, WqB);
   Wq := MatrixAlgebra(K,#B)!(&cat[Eltseq(v) : v in C]);
   return <Wq, B>;
end function;


// M must be a cuspidal ModFrm of integral weight >= 2, q must be prime, 
function compute_Wq_cuspidal(M, q)
   if Dimension(M) eq 0 then
      return MatrixAlgebra(RationalField(),0)!1;
   end if;

   K := field_of_fractions(BaseRing(M));
   if Type(BaseRing(M)) ne RngInt then
      MZ := AssociatedSpaceOverZ(M);      
      Wq := compute_Wq_cuspidal(MZ,q);
      return ChangeRing(Wq, K);
   end if;

   N := Level(M);
   prec := PrecisionBound(M:Exact) + 1; 
   type := SpaceType(M);    assert type in {"cusp", "cusp_new"};  // the types we know about.
   param := SpaceTypeParam(M);   assert param eq 0 or IsPrime(param);  // all we know about.
   B := [];
   Wq := Matrix(0, 0, [K|]);
   for d in Divisors(N) do 
      NS := 0;
      if type eq "cusp" then
         if d eq N then
            NS := NewSubspace(M); 
         else  
            NS := NewSubspace(CuspidalSubspace(ModularForms(M,d)));
         end if;
      elif type eq "cusp_new" then
         if param eq 0 and d eq N then
            NS := M;
         elif param ne 0 and Valuation(d,param) eq Valuation(N,param) then
            NS := NewSubspace(CuspidalSubspace(ModularForms(M,d)));
         end if;
      end if;
      if NS cmpne 0 then
         W, basis := Explode(WqOnImageOfNewSpace(NS, q, N div d, prec));
         Wq := DiagonalJoin(Wq, W);
         B cat:= basis;
      end if;
   end for;
   C := ChangeBasis(Wq, B, [PowerSeriesInternal(f,prec) : f in Basis(M)]);   
   return C;
end function;

// This function's job is to handle the caching
// (same requirements on M and q as in AtkinLehnerOperator)

function get_Wq(M, q)
   if not assigned M`atkin_operator then
      M`atkin_operator := [];
   end if;
   if exists(i){i : i in [1..#M`atkin_operator] 
                  | M`atkin_operator[i][1] eq q} then
      return M`atkin_operator[i][2];
   end if;

   if IsEisenstein(M) then
      Wq := AtkinLehnerOnEisensteinModularFormsSpace(M, q);
   elif IsCuspidal(M) then
      fact := Factorization(q);
      if #fact eq 1 then 
         Wq := compute_Wq_cuspidal(CuspidalSubspace(M), fact[1][1]); // expects prime q
      else
         Wq := &* [get_Wq(M, tup[1]^tup[2]) : tup in Factorization(q)];
      end if;
   else 
      E := EisensteinSubspace(M);
      S := CuspidalSubspace(M);
      WE := get_Wq(E, q);
      WS := get_Wq(S, q);
      W := DiagonalJoin(WS, WE);
      BS_BE := [M!b : b in Basis(S)] cat [M!b : b in Basis(E)];
      // Change of basis from Basis(S) cat Basis(E) to Basis(M) 
      // TO DO: review all the changes of basis
      C := MatrixAlgebra(RationalField(), Dimension(M)) !
                         &cat[Eltseq(b) : b in BS_BE];
      Wq := C^-1*W*C;
   end if;

   assert Wq^2 eq 1;
   Append(~M`atkin_operator, <q, Wq>);
   return Wq;
end function;


intrinsic AtkinLehnerOperator(q::RngIntElt,f::ModFrmElt) -> ModFrmElt
{Apply the AtkinLehnerOperator w_q to f. (Same result as f*w_q.)}
  return f*AtkinLehnerOperator(Parent(f),q);
end intrinsic;

intrinsic AtkinLehnerOperator(M::ModFrm) -> AlgMatElt
{Same as AtkinLehnerOperator(M,N) where N is the level of M}
   require Level(M) ne 1 : "Space has level 1, no sensible AtkinLehnerOperator";
   return AtkinLehnerOperator(M,Level(M));
end intrinsic; 

intrinsic AtkinLehnerOperator(M::ModFrm, q::RngIntElt) -> AlgMatElt
{The matrix representing the q-th Atkin-Lehner involution W_q on M
with respect to Basis(M).  At present M must be a cuspidal space of 
modular forms for Gamma_0(N).  Note that the Atkin-Lehner operator
W_q can send a q-expansion with integer coefficients to one with nontrivial
denominators.}

   if Dimension(M) eq 0 or GCD(q,Level(M)) eq 1 then
      return MatrixAlgebra(BaseRing(M),0)!1;
   end if;

   require GCD(q,Level(M) div q) eq 1 :
       "Argument 2 (=q) must have the property " *
       "that GCD(q, N/q) = 1, where N is the level of argument 1.";
   require IsGamma0(S) or Dimension(S) eq 0 where S := CuspidalSubspace(M) :
        "Argument 1 must be a space of modular forms on Gamma_0.";
   require Type(Weight(M)) eq RngIntElt : 
        "The weight must be an integer";
   if Dimension(EisensteinSubspace(M)) ne 0 then
      require IsEven(Weight(M)) : "Atkin-Lehner operators are not " *
              "yet implemented on Eisenstein spaces of odd weight.";
   end if; 

   return get_Wq(M, q);
end intrinsic;

