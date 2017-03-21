freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Module of Supersingular Points in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: modss.m (Module of Supersingular Points)

   $Header: /home/was/magma/packages/modss/code/RCS/modss.m,v 1.4 2002/05/06 05:43:28 was Exp $

   $Log: modss.m,v $
   Revision 1.4  2002/05/06 05:43:28  was
   ...

   Revision 1.3  2002/05/06 04:29:58  was
   Lots of little changes.

   Revision 1.2  2001/07/06 20:02:47  was
   Made it so can't compute T_p when p divides the level.
   Added a level intrinsic.  -- was

   Revision 1.1  2001/07/06 19:53:09  was
   Initial revision

   Revision 1.2  2001/06/19 02:31:59  kohel
   *** empty log message ***



   References: Papers of Mestre & Oesterle

 ***************************************************************************/

forward 
   CreateSubspace,
   FindSupersingularJ,
   KernelOn,
   Restrict;


declare type ModSS [ModSSElt];

declare attributes ModSS:
   p,          
   auxiliary_level,
   ss_points,   
   basis,
   monodromy_weights,
   hecke,
   hecke_sparse,
   atkin_lehner,
   decomp,
   cuspidal_subspace,
   eisenstein_subspace,
   uses_brandt,
   brandt_module,
   modular_symbols,
   ambient_space,
   dimension,
   rspace;

declare type ModSSElt;

declare attributes ModSSElt:
   element,
   parent;

BRANDT_MESG := "(try creating the supersingular module with the "*
               "Brandt parameter set to true instead)";


procedure AssignNameToFiniteFieldGeneratorIfItAintAssignedAlready(k)
   assert Type(k) eq FldFin;
   s := Sprintf("%o",k.1);
   if #s gt 1 and s[#s-1] eq "." then
      AssignNames(~k,["t"]);
   end if;
end procedure;


intrinsic SupersingularModule(p::RngIntElt 
                                : Brandt := false) -> ModSS
{}
   require p ge 2 and IsPrime(p) : "Argument 1 must be prime.";
   return SupersingularModule(p,1 : Brandt := Brandt);
end intrinsic;

intrinsic SupersingularModule(p::RngIntElt, N::RngIntElt 
                                       : Brandt := false) -> ModSS
{}
   require p ge 2 and IsPrime(p) : "Argument 1 must be prime.";
   require N ge 1: "The first argument must be at least 1.";
   require GCD(p,N) eq 1 : "Arguments 1 and 2 must be coprime.";

   AssignNameToFiniteFieldGeneratorIfItAintAssignedAlready(GF(p^2));
   M := New(ModSS);
   M`p := p;
   M`auxiliary_level := N;
   if N in {1,2,3,5,7,13} and not Brandt then
      M`uses_brandt := false;
   else
      M`uses_brandt := true;
   end if;
   return M;
end intrinsic;


intrinsic UsesBrandt(M::ModSS) -> BoolElt
{}
   if not IsAmbientSpace(M) then
      return UsesBrandt(AmbientSpace(M));
   end if;
   return M`uses_brandt;
end intrinsic;

intrinsic UsesMestre(M::ModSS) -> BoolElt
{}
   if not IsAmbientSpace(M) then
      return UsesMestre(AmbientSpace(M));
   end if;

   return not UsesBrandt(M);
end intrinsic;

intrinsic RSpace(M::ModSS) -> ModTupRng, Map
{}
   if not assigned M`rspace then
      assert IsAmbientSpace(M);
      W := DiagonalMatrix(MonodromyWeights(M));
      M`rspace := RSpace(Integers(),Dimension(M),W);
   end if;
   V := M`rspace;
   return V, hom<V -> M | x :-> M!x,  x :-> V!Eltseq(x)>;
end intrinsic;


intrinsic IsAmbientSpace(M::ModSS) -> BoolElt
{}
   return not assigned M`ambient_space;
end intrinsic;


intrinsic AmbientSpace(M::ModSS) -> BoolElt
{}
   if not assigned M`ambient_space then
      return M;
   end if;
   return M`ambient_space;
end intrinsic;


function RootsAfterSpecializeX(F, alpha)
   R<x,y> := Parent(F);
   G := UnivariatePolynomial(Evaluate(F,[alpha,y]));
   return Roots(G);
end function;


function RootsAfterSpecializeY(F, beta)
   R<x,y> := Parent(F);
   G := UnivariatePolynomial(Evaluate(F,[x,beta]));
   return Roots(G);
end function;


function CreateModSSElt(M, v)
   assert Type(M) eq ModSS;
   assert Type(v) eq ModTupRngElt;
   assert v in RSpace(M);
   P := New(ModSSElt);
   P`parent := M;
   P`element := v;
   return P;
end function;

function CopyOfModSSElt(P)
   return CreateModSSElt(Parent(P),P`element);
end function;


intrinsic Eltseq(P::ModSSElt) -> SeqEnum
{}
   return Eltseq(P`element);
end intrinsic;


intrinsic Basis(M::ModSS) -> SeqEnum
{}
   if not assigned M`basis then
      W := RSpace(M);
      M`basis := [CreateModSSElt(M,b) : b in Basis(W)];
   end if;
   return M`basis;
end intrinsic;

intrinsic SupersingularPoints(M::ModSS) -> SeqEnum
{}
   if assigned M`ss_points then 
      return M`ss_points;
   end if;

   if UsesBrandt(M) then
      M`ss_points := ["I"*IntegerToString(n) : n in [1..Dimension(M)]];
      return M`ss_points;
   end if;

   p := Prime(M);
   N := AuxiliaryLevel(M);
   ss, t2 := SupersingularInvariants(p);   // defined in mestre.m
   if N eq 1 then
      M`ss_points := [<j,j> : j in ss];
      M`hecke_sparse := [* <2, t2> *];
      return M`ss_points;
   end if;
   F := ModularEquation(M);
   R<x,y> := Parent(F);
   points := [];
   j_num, j_denom := jInvariantMap(M);
   // j_num(x) / j_denom(x) = j.
   for j in ss do   // find the fibers
      f := j_num - j*j_denom;
      for r in Roots(f) do
         // solve for y-coordinates
         y_coords := RootsAfterSpecializeX(F,r[1]);
         assert #y_coords ge 1;
         for s in y_coords do
            Append(~points, <r[1],s[1]>);
         end for;
      end for;
   end for;
   M`ss_points := points;
   return points;
end intrinsic;

intrinsic '.'(M::ModSS, i::RngIntElt) -> ModSSElt
{}
   requirege i, 1;
   require i le Dimension(M) : "Argument 2 can be at most the dimension of argument 1.";
   return Basis(M)[i];
end intrinsic;

intrinsic '+'(M1::ModSS, M2::ModSS) ->  ModSS
{}
   require AmbientSpace(M1) eq AmbientSpace(M2) : "Arguments 1 and 2 must have "*
            "the same ambient space.";
   return CreateSubspace(AmbientSpace(M1), RSpace(M1) + RSpace(M2));
end intrinsic;    

intrinsic 'eq'(M1::ModSS, M2::ModSS) -> BoolElt
{}
   return Prime(M1) eq Prime(M2) and 
          AuxiliaryLevel(M1) eq AuxiliaryLevel(M2) and
          RSpace(M1) eq RSpace(M2) and
          ( (UsesMestre(M1) and UsesMestre(M2)) or (UsesBrandt(M1) and UsesBrandt(M2)));
end intrinsic;

intrinsic 'eq'(P::ModSSElt, Q::ModSSElt) -> BoolElt
{}
   return AmbientSpace(Parent(P)) eq AmbientSpace(Parent(Q)) and     
          Eltseq(P) eq Eltseq(Q);
end intrinsic;

intrinsic 'subset'(M1::ModSS, M2::ModSS) -> BoolElt
{}
   return Prime(M1) eq Prime(M2) and 
          AuxiliaryLevel(M1) eq AuxiliaryLevel(M2) and
          RSpace(M1) subset RSpace(M2) and
          ( (UsesMestre(M1) and UsesMestre(M2)) or (UsesBrandt(M1) and UsesBrandt(M2)));
end intrinsic;

intrinsic 'meet'(M1::ModSS, M2::ModSS) -> ModSS
{The intersection of modules of supersingular divisors M1 and M2 
(which must have the same ambient space)}

   require AmbientSpace(M1) eq AmbientSpace(M2) : 
          "Arguments 1 and 2 must have the same ambient space.";

   return CreateSubspace(AmbientSpace(M1), RSpace(M1) meet RSpace(M2));
end intrinsic;

intrinsic IsCoercible(M::ModSS,P::.) -> BoolElt, ModSSElt
{Coerce P into M.}
   case Type(P):
      when ModSSElt:
         if Parent(P) subset M then
            Q := CopyOfModSSElt(P);
            Q`parent := M;
            return true, Q;
         end if;
      else:
         val, el := IsCoercible(RSpace(M),P);
         if val then
            return true, CreateModSSElt(M,el);
         end if;
   end case;
   return false, "Illegal coercion";
end intrinsic;

intrinsic '-'(P::ModSSElt, Q::ModSSElt) -> ModSSElt
{}
   require AmbientSpace(Parent(P)) eq AmbientSpace(Parent(Q)) : 
             "Incompatible parents.";
   return P + (-1)*Q;
end intrinsic;

intrinsic '*'(a::RngElt, P::ModSSElt) -> ModSSElt
{} 
   val, el := IsCoercible(Integers(),a);
   require val : "Argument 1 must be coercible into the integers.";
   return Parent(P)!(el*P`element);
end intrinsic;


intrinsic ModularEquation(M::ModSS) -> RngMPolElt
{}
   R<x,y> := PolynomialRing(GF(Prime(M)^2),2);
   table := [* x-y,    // N=1
               x*y-2^12, // N=2 
               x*y-3^6,  // N=3
               0,        
               x*y-5^3,  // N=5
               0,
               x*y-7^2,  // N=7
               0,
               0,
               0, 
               0,
               0,
               x*y-13    // N=13
            *];

   N := AuxiliaryLevel(M);  

   require N le #table : "The model is not known.";
   require table[N] ne 0: "The model is not known.";
   return table[N];                  
end intrinsic;

intrinsic jInvariantMap(M::ModSS) -> RngUPolElt, RngUPolElt
{}
   R := PolynomialRing(GF(Prime(M)^2)); x := R.1;
   table := [* <x, 1>,  // N = 1
               <(x+16)^3, x>,  // N = 2
               <(x+27)*(x+3)^3, x>, // N=3
               <>, 
               <(x^2+10*x+5)^3, x>, // N=5
               <>,
               <(x^2+13*x+49)*(x^2+5*x+1)^3, x>, // N=7
               <>,
               <>,
               <>,
               <>,
               <>,
               <(x^2+5*x+13)*(x^4+7*x^3+20*x^2+19*x+1)^3, x>, //N=13
               <>
             *];
   N := AuxiliaryLevel(M);  

   require N le #table : "The j-invariant map is not known.";
   require table[N] cmpne <> : "The j-invariant map is not known.";
   return table[N][1], table[N][2];   
end intrinsic;

intrinsic HeckeCorrespondence(M::ModSS, p::RngIntElt) -> RngMPolElt
   {Equation that defines the p-th Hecke correspondence on M.}

   N := AuxiliaryLevel(M);
   require N in {1,2,3,5,7,13} :
       "Auxiliary level of argument 1 must be 1, 2, 3, 5, 7, or 13.";
   require p ge 2 and IsPrime(p) : "Argument 2 must be prime.";

   P2 := PolynomialRing(GF(Prime(M)^2),2);
   if N eq 1 then
       D := ModularCurveDatabase("Classical");
       require p in D : 
          "Argument 2 must be in the database of classical modular equations.";
       return P2!Polynomial(ModularCurve(D,p));
   else 
       D := ModularCurveDatabase("Hecke",N);
       require p in D :
          "Argument 2 must be in the database of Hecke correspondences.";
       return P2!Polynomial(ModularCurve(D,p));
   end if;
end intrinsic;

intrinsic Prime(M::ModSS) -> RngIntElt
{}
   return M`p;
end intrinsic;

intrinsic AuxiliaryLevel(M::ModSS) -> RngIntElt
{}
   return M`auxiliary_level;
end intrinsic;

intrinsic Level(M::ModSS) -> RngIntElt
{}
   return Prime(M) * AuxiliaryLevel(M);
end intrinsic;

intrinsic Dimension(M::ModSS) -> RngIntElt
{}
   if not assigned M`dimension then
      if IsAmbientSpace(M) then
         if UsesBrandt(M) then
            M`dimension := Dimension(BrandtModule(M));
         else
            M`dimension := #SupersingularPoints(M);
         end if;
      else
         assert assigned M`rspace;
         M`dimension := Dimension(M`rspace);
      end if;
   end if;
   return M`dimension;
end intrinsic;


intrinsic Print(M::ModSS, level::MonStgElt)
   {}
   if AuxiliaryLevel(M) eq 1 then
      printf "Supersingular module associated to X_0(1)/GF(%o) of dimension %o", 
              Prime(M), Dimension(M);
   else
      printf "Supersingular module associated to X_0(%o)/GF(%o) of dimension %o", 
           AuxiliaryLevel(M), Prime(M), Dimension(M);
   end if;
end intrinsic;

procedure PrintSupersingularPoint(M,i)
   assert Type(M) eq ModSS;
   assert Type(i) eq RngIntElt;
   assert i ge 1 and i le Dimension(AmbientSpace(M));
   if UsesBrandt(M) then 
      printf "[E%o]", i;
   else
      s := SupersingularPoints(M)[i];
      printf "(%o, %o)", s[1],s[2];
   end if;
end procedure;

intrinsic Print(P::ModSSElt, level::MonStgElt)
   {}
   e := P`element;
   first := true;
   for i in [j : j in [1..Degree(e)] | e[j] ne 0] do
      if not first then 
         if e[i] lt 0 then
            printf " - ";
            e[i] := -e[i];
         else
            printf " + ";
         end if;
      end if;
      if e[i] ne 1 then
         if e[i] eq -1 then
            printf "-";
         else
            printf "%o*", e[i];   
         end if;
      end if;
      PrintSupersingularPoint(Parent(P),i);
      first := false;
   end for;
end intrinsic;

intrinsic Parent(P::ModSSElt) -> ModSS
   {}
   return P`parent;
end intrinsic;



function ComputeHeckeOperatorBrandt(M,p)
   assert Type(M) eq ModSS;
   assert Type(p) eq RngIntElt;
   assert p ge 2 and IsPrime(p);
   return HeckeOperator(BrandtModule(M), p);
end function;

function ComputeHeckeOperatorMestre(M,p, sparse)
   assert Type(M) eq ModSS;
   assert Type(p) eq RngIntElt;
   assert p ge 2 and IsPrime(p);
   assert IsAmbientSpace(M);
   assert AuxiliaryLevel(M) mod p ne 0;

   S := SupersingularPoints(M);
   correspondence := HeckeCorrespondence(M,p);
   curve := ModularEquation(M);
   if sparse then
      T := SparseMatrix(Integers(), Dimension(M), Dimension(M));
   else
      T := MatrixAlgebra(Integers(),Dimension(M))!0;
   end if;
   for i in [1..#S] do
      P := S[i];
      for x in RootsAfterSpecializeX(correspondence,P[1]) do
         y_val := RootsAfterSpecializeX(curve,x[1]);
         assert #y_val le 1;
         Q := <x[1], y_val[1][1]>;
         n := Index(S, Q);
         if n eq 0 then
            error "An error in ComputeHeckeOperatorMestre occured, which "*
                  "probably means that one of the polynomial tables is wrong."; 
         end if;
         T[i,n] +:= x[2];
      end for;
   end for;  
   return T; 
end function;


function HeckeOperatorPrimeIndex(M,p, sparse)
   assert Type(M) eq ModSS;
   assert Type(p) eq RngIntElt;
   assert p ge 1 and IsPrime(p);
   if UsesBrandt(M) then
      return ComputeHeckeOperatorBrandt(M,p);
   else
      return ComputeHeckeOperatorMestre(M,p, sparse);
   end if;
end function;

function ComputeHeckeOperator(M,n, sparse)
   assert Type(M) eq ModSS;
   assert Type(n) eq RngIntElt;
   assert n ge 1;
   
   fac := Factorization(n);
   if #fac eq 0 then
      return MatrixAlgebra(Integers(),Dimension(M))!1;
   elif #fac eq 1 then
      // T_{p^r} := T_p * T_{p^{r-1}} - eps(p)p^{k-1} T_{p^{r-2}}.
      p  := fac[1][1];
      r  := fac[1][2];
      T  := HeckeOperatorPrimeIndex(M,p, sparse);
      if r gt 1 then
         if r eq 2 then
            S := T;
         else
            S := ComputeHeckeOperator(M,p^(r-1));
         end if;
         T  := T*S  - p*ComputeHeckeOperator(M,p^(r-2));
      end if;
   else  // T_m*T_r := T_{mr} and we know all T_i for i<n.
      m  := fac[1][1]^fac[1][2];
      T  := ComputeHeckeOperator(M,m)*ComputeHeckeOperator(M,n div m);
   end if;            
   return T;
end function;


intrinsic HeckeOperator(M::ModSS, n::RngIntElt) -> AlgMatElt
   {Hecke operator T_n.}
   require n ge 1 : 
      "Argument 1 must be positive.";
   require GCD(AuxiliaryLevel(M),n) eq 1 or 
          assigned M`uses_brandt and M`uses_brandt eq true:
          "Argument 2 must be coprime to the level of argument 1.";

   if not assigned M`hecke then
      M`hecke := [* *];
   end if;
   for x in M`hecke do
      if x[1] eq n then
         return x[2];
      end if;
   end for;

   if IsAmbientSpace(M) then
      Tn := ComputeHeckeOperator(M,n, false);
   else
      Tn := Restrict(ComputeHeckeOperator(AmbientSpace(M),n, false), RSpace(M));
   end if;

   Append(~M`hecke,<n,Tn>);

   return Tn;
end intrinsic;

intrinsic SparseHeckeOperator(M::ModSS, n::RngIntElt) -> MtrxSprs
{Hecke operator T_n as a sparse matrix.  If M is not the full ambient
space or UseMestre is false or n is composite or too large, then the
nth dense Hecke operator is computed internally as well.}

   if not assigned M`hecke_sparse then
      M`hecke_sparse := [* *];
   end if;

   if UsesMestre(M) and AuxiliaryLevel(M) eq 1  and n eq 2 then
      dummy := SupersingularPoints(M);   // computes sparse matrix for T2 and sets M`hecke_sparse.
   end if;

   for x in M`hecke_sparse do
      if x[1] eq n then
         return x[2];
      end if;
   end for;
   if UsesBrandt(M) or not IsAmbientSpace(M) or not IsPrime(n) then
      Tn := SparseMatrix(HeckeOperator(M,n));
   else
      Tn := ComputeHeckeOperator(M, n, true);
   end if;

   Append(~M`hecke_sparse, <n, Tn>);

   return Tn;
end intrinsic;


intrinsic HeckeOperator(n::RngIntElt, x::ModSSElt) -> ModSSElt
{Hecke operator applied to x:  T_n(x)}
   M := AmbientSpace(Parent(x));
   T := HeckeOperator(AmbientSpace(Parent(x)),n);
   return Parent(x)!(x`element*T);
end intrinsic;



intrinsic MonodromyPairing(x::ModSSElt, y::ModSSElt) -> RngIntElt
{}
   require AmbientSpace(Parent(x)) eq AmbientSpace(Parent(y)) : 
         "Arguments 1 and 2 must belong to the same space.";
   w := MonodromyWeights(Parent(x));
   xe := Eltseq(x); 
   ye := Eltseq(y);
   return &+[w[i]*xe[i]*ye[i] : i in [1..#w]];
end intrinsic;


function MonodromyWeights_brandt(B)
   // Returns the monodromy weights of the Brandt module B.
   A := GramMatrix(B);
   return [ Integers()!(A[i,i]) : i in [1..Nrows(A)]];
end function;


function MestreEisensteinFactor(X)
   // Computes the Eisenstein factor of the Mestre module X.
   assert Type(X) eq ModSS;
   assert UsesMestre(X);

   if AuxiliaryLevel(X) mod 2 eq 0 then
      p := 3;   
   else
      p := 2;   
   end if;
   assert AuxiliaryLevel(X) mod p ne 0;
   T := HeckeOperator(X,p)-(p+1);
   V := Kernel(T);
   while Dimension(V) gt 1 and p le 3 do
      p := NextPrime(p); 
      T := HeckeOperator(X,p)-(p+1);
      V := V meet Kernel(T);
   end while;
   if Dimension(V) gt 1 then
      error "Not enough Hecke operators are known for us to compute "*
            "the monodromy weights using the Mestre method " 
              cat BRANDT_MESG cat ".";
   end if;
   if Dimension(V) eq 0 then
      error "Bug in EisensteinFactor";
   end if;
   return V;
end function;

function MonodromyWeights_mestre(X)
   // Returns the monodromy weights.
   eisfactor := MestreEisensteinFactor(X);
   assert Dimension(eisfactor) eq 1;
   eis       := Eltseq(Basis(eisfactor)[1]);
   n         := Lcm([Integers()|e : e in eis]);
   return [Integers()|Abs(Numerator(n/e)) : e in eis];
end function;

intrinsic MonodromyWeights(M::ModSS) -> SeqEnum
    {}
   if not IsAmbientSpace(M) then
      return MonodromyWeights(AmbientSpace(M)); 
   end if;
   if not assigned M`monodromy_weights then
      M`monodromy_weights := UsesBrandt(M) select
                   MonodromyWeights_brandt(BrandtModule(M))
                 else
                   MonodromyWeights_mestre(M); 
   end if;
   return M`monodromy_weights;
end intrinsic;


function AtkinLehnerMestre(M, q)
   assert Type(M) eq ModSS;
   assert Type(q) eq RngIntElt;
   assert UsesMestre(M);
   assert IsAmbientSpace(M);
   p := Prime(M);
   N := AuxiliaryLevel(M);

   if q eq N and N eq 1 then
      return MatrixAlgebra(Integers(),Dimension(M))!1;
   end if;

   Wp := MatrixAlgebra(Integers(),Dimension(M))!0;
   S := SupersingularPoints(M);

   for i in [1..Dimension(M)] do 
      //  P := S[i];
      Q := <S[i][2]^p, S[i][1]^p>;
      j := Index(S, Q);
      assert j ne 0;
      Wp[i,j] := -1;
   end for;
   return Wp;
end function;

function AtkinLehnerBrandt(M, q)
   assert Type(M) eq ModSS;
   assert UsesBrandt(M);
   assert IsAmbientSpace(M);

   return AtkinLehnerOperator(BrandtModule(M),q);
end function;

intrinsic AtkinLehnerOperator(M::ModSS, q::RngIntElt) -> AlgMatElt
{The Atkin-Lehner involution W_q, where q is either Prime(M) or AuxiliaryLevel(M).}
   require q in {Prime(M), AuxiliaryLevel(M)} : "Argument 2 must be either",
                 Prime(M), "or", AuxiliaryLevel(M);
   if not assigned M`atkin_lehner then
      if IsAmbientSpace(M) then
         if UsesMestre(M) then
            M`atkin_lehner := AtkinLehnerMestre(M,q);   
         else
            M`atkin_lehner := AtkinLehnerBrandt(M,q);   
         end if;
      else
         M`atkin_lehner := Restrict(AtkinLehnerOperator(AmbientSpace(M),q),RSpace(M));
      end if;
   end if;
   return M`atkin_lehner;   
end intrinsic;


function CreateSubspace(M, V) 
   assert Type(M) eq ModSS;
   assert Type(V) eq ModTupRng;
   assert V subset RSpace(M);

   if V eq RSpace(M) then
      return M;
   end if;

   S := New(ModSS);
   S`p := Prime(M);
   S`auxiliary_level := AuxiliaryLevel(M);
   S`ambient_space := AmbientSpace(M);
   S`rspace := V;
   return S;
end function;


intrinsic OrthogonalComplement(M::ModSS) -> ModSS
{The orthogonal complement of M, with respect to the monodromy pairing.}
   A := RMatrixSpace(Integers(),Dimension(AmbientSpace(M)), Dimension(M))!0;
   w := MonodromyWeights(M);
   B := Basis(RSpace(M));
   for j in [1..#B] do
      for i in [1..Dimension(AmbientSpace(M))] do
         A[i,j] := B[j][i]*w[i];
      end for;
   end for;   

   B := Basis(Kernel(A));
   V := RSpace(AmbientSpace(M));
   W := sub<V | [V!x : x in B]>;
   return CreateSubspace(AmbientSpace(M), W);
end intrinsic;

intrinsic EisensteinSubspace(M::ModSS) -> ModSS
{The Eisenstein subspace of M.}
   if not assigned M`eisenstein_subspace then
      if not IsAmbientSpace(M) then
         M`eisenstein_subspace := EisensteinSubspace(AmbientSpace(M)) meet M;
      else  // the orthogonal complement of the cuspidal subspace.
         M`eisenstein_subspace := OrthogonalComplement(CuspidalSubspace(M));
      end if;
   end if;
   return M`eisenstein_subspace;
end intrinsic;


intrinsic CuspidalSubspace(M::ModSS) -> ModSS
{The cuspidal subspace of M.}
   if not assigned M`cuspidal_subspace then
      if not IsAmbientSpace(M) then
         M`cuspidal_subspace := CuspidalSubspace(AmbientSpace(M)) meet M;
      else
         V := RSpace(M);
         Zero := sub<V | [ V.1 - V.i : i in [2..Dimension(V)]] >;
         M`cuspidal_subspace := CreateSubspace(M, Zero);
      end if;
   end if;
   return M`cuspidal_subspace;
end intrinsic;


function DecompositionHelper(M, pstart, pstop, Proof)
   assert Type(M) eq ModSS;
   assert Type(pstart) eq RngIntElt;
   assert Type(pstop) eq RngIntElt; 
   assert Type(Proof) eq BoolElt;
   if pstart gt pstop then
      return [M];
   end if;
   p := NextPrime(pstart-1);
   while UsesMestre(M) and AuxiliaryLevel(M) mod p eq 0 do
      print "Skipping p=", p, ".";
      p := NextPrime(p);   
   end while;
   if p gt pstop then
      return [M];
   end if;
   fp := CharacteristicPolynomial(HeckeOperator(M,p) : Al := "Modular", Proof := Proof);
   decomp := [];
   for F in Factorization(fp) do
      Append(~decomp, Kernel([<p, F[1]^F[2]>], M));
   end for; 
   p := NextPrime(p);
   return &cat [DecompositionHelper(Msmall, p, pstop, Proof) : Msmall in decomp];
end function;

intrinsic Decomposition(M::ModSS, stop::RngIntElt : Proof := true) -> SeqEnum
{Decomposition of M with respect to the Hecke operators T_2, T_3, T_5, ..., T_stop.}
   D := DecompositionHelper(M, 2, stop, Proof);
   cmp := func<A, B | Dimension(A) - Dimension(B)>;
   Sort(~D, cmp);
   return D;
end intrinsic;

function Kernel_helper(M, W, polyprimes)
   for i in [1..#polyprimes] do
      vprint SupersingularModule : "Current dimension = ", Dimension(W);
      p  := polyprimes[i][1];
      f  := polyprimes[i][2];
      t  := Cputime();
      vprintf SupersingularModule: "Computing Ker(f(T_%o))\n", p;
      T  := Restrict(HeckeOperator(M, p), W);
      fT := Evaluate(f,T);
      K  := KernelOn(fT,W);
      W  := W meet K;
      vprintf SupersingularModule: "   (%o seconds.)", Cputime(t);
      if Dimension(W) eq 0 then
         return W;
      end if;
   end for;
   vprint SupersingularModule : "Current dimension = ", Dimension(W);
   return W;
end function;

intrinsic Kernel(I::[Tup], M::ModSS) -> ModSS
{The kernel of I on M.  This is the subspace of M obtained 
by intersecting the kernels of the operators 
f_n(T_\{p_n\}), where I is a sequence 
[<p_1, f_1(x)>,...,<p_n,f_n(x)>] of pairs
consisting of a prime number and a polynomial.}
   if #I eq 0 then
      return M;
   end if;
   exceptional_tp := I;
   p := I[1][1];
   f := I[1][2];
   t := Cputime();
   vprintf SupersingularModule : "Computing Ker(f(T_%o))\n", p;
   fT:= Evaluate(f, HeckeOperator(M,p));
   W := KernelOn(fT,RSpace(M));
   vprintf SupersingularModule : "   (%o seconds.)", Cputime(t);
   W := Kernel_helper(M, W, Remove(I,1));
   return CreateSubspace(M,W);
end intrinsic;


///////////////////////////////////////////////////
// Some connections with other modules.
///////////////////////////////////////////////////


intrinsic BrandtModule(M::ModSS) -> ModBrdt
{}
   require IsAmbientSpace(M) : "Argument 1 must be an ambient space.";

   if not assigned M`brandt_module then
      M`brandt_module := BrandtModule(QuaternionOrder(Prime(M),AuxiliaryLevel(M)));
   end if;
   return M`brandt_module;

end intrinsic;

intrinsic ModularSymbols(M::ModSS : Proof := true) -> ModSym
{}
   return ModularSymbols(M, 0 : Proof := Proof);
end intrinsic;

intrinsic ModularSymbols(M::ModSS, sign::RngIntElt : Proof := true) -> ModSym
{} 
   require sign in {-1,0,1} : "Argument 2 must be -1, 0, or 1.";
   if not assigned M`modular_symbols or 
      Type(M`modular_symbols[sign+2]) eq BoolElt then
      if not assigned M`modular_symbols then
         M`modular_symbols := [* false, false, false *];
      end if;       
      N := AuxiliaryLevel(M);
      p := Prime(M);
      if IsAmbientSpace(M) then
         modsym := NewSubspace(ModularSymbols(N*p, 2, sign),p);
         M`modular_symbols[sign+2] := modsym;
      else
         modsym := ModularSymbols(AmbientSpace(M),sign);
         p := 2;
         if UsesMestre(M) and N mod p eq 0 then
            p := 3;
         end if;
         factor := sign eq 0 select 2 else 1;
         while Dimension(EisensteinSubspace(modsym)) + 
                          (Dimension(CuspidalSubspace(modsym)) div 2) 
                               gt Dimension(M) and
               (UsesBrandt(M) or (UsesMestre(M) and p le 3 and N mod p ne 0)) do

            fp := CharacteristicPolynomial(HeckeOperator(M,p) : 
                      Al := "Modular", Proof := Proof);
            modsym := Kernel([<p, fp>], modsym);
            p := NextPrime(p);
         end while;
         if Dimension(EisensteinSubspace(modsym)) + 
                          (Dimension(CuspidalSubspace(modsym)) div 2) 
                   gt Dimension(M) then
            error "Unable to compute corresponding modular symbols space "*
                  BRANDT_MESG;
         end if;
         M`modular_symbols[sign+2] := modsym;
      end if;
   end if;
   return M`modular_symbols[sign+2];
end intrinsic;


function LinearCombinations(Comb, B) 
// Compute the linear combinations of the elements of B
// defined by the elements of Comb.
    n := #B;
    if n eq 0 then
      return B;
    end if;
    return [Parent(B[1])|&+[B[i]*v[i] : i in [1..n]] : v in Comb];
end function;

function KernelOn(A, B)
   // Suppose B is a basis for an n-dimensional subspace
   // of some ambient space and A is an nxn matrix.
   // Then A defines a linear transformation of the space
   // spanned by B.  This function returns the
   // kernel of that transformation.
   if Type(B) eq ModTupRng then
      B := Basis(B);
   end if;
   n := #B;
   if n eq 0 then
      return sub<Universe(B)|0>;
   end if;
   assert Nrows(A) eq Ncols(A) and Nrows(A) eq n;
   K := Kernel(A);
   return sub<Universe(B) | LinearCombinations(Basis(K),B)>;

//   return RSpaceWithBasis(LinearCombinations(Basis(K),B));
end function;

// Restriction of A to x.
function Restrict(A,x)
   F := BaseRing(Parent(A));
   if Type(x) eq SeqEnum then
      B := x;
   else
      if Dimension(x) eq 0 then
         return MatrixAlgebra(F,0)!0;
      end if;
      Z := Basis(x);
      V := RSpace(F, Degree(x));
      B := [V!Z[i] : i in [1..Dimension(x)]];
   end if; 
   S := RSpaceWithBasis(B);
   v := [Coordinates(S, S.i*A) : i in [1..#B]];
   return MatrixAlgebra(F,#B) ! (&cat v);
end function;


intrinsic '+'(x::ModSSElt, y::ModSSElt) -> ModSSElt
   {}
   require AmbientSpace(Parent(x)) eq AmbientSpace(Parent(y)) :
     "Arguments 1 and 2 are incompatible.";

   sum := x`element + y`element;
   if Parent(x) ne Parent(y) then
      return AmbientSpace(Parent(x))!sum;
   else
      return Parent(x)!sum;
   end if;
end intrinsic; 

intrinsic BaseRing(M::ModSS) -> Rng
{}
   return IntegerRing();
end intrinsic;

intrinsic Degree(P::ModSSElt) -> RngElt
{}
   return &+Eltseq(P);
end intrinsic;

intrinsic DisownChildren(M::ModSS) 
{No longer necessary -- do not use!}
end intrinsic;

// Arghh, this should never have been here
intrinsic Memory() -> RngIntElt
{Current memory usage in MB}
   return Round(GetMemoryUsage()/(1024*1024.0));
end intrinsic;
