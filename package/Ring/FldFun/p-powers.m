freeze;

/////////////////////////////////////////////////////////////////////////////
/*  
  
   p-powers.m: p-power representations and kernels of p-linear maps.
  
   FH Oct 2004
  
   There is no generic for transcendental field extensions in place.
   Hence the following works only for the special case of recursively
   defined FldFunG's. 
  
*/  
/////////////////////////////////////////////////////////////////////////////  
  
  
/*
  
> k := GF(3);
> kxf<x> := RationalFunctionField(k);
> kxfy<y> := PolynomialRing(kxf);
> F1<a1> := FunctionField(y^2 - x^7 + 1);
> F1zf<z> := RationalFunctionField(F1);
>
> A := Matrix(F1zf, 3, [ 1, z, x^3 + z*x, 0, 1, x]);
> A;
[1   z   x*z + x^3]
[0   1   x]
> PrimePowersInVectorSpace(A, 1);
[1   0   x]
>
> A := Matrix(F1zf, 3, [ 1, z, x^9 + z*x, 0, 1, x]);
> PrimePowersInVectorSpace(A, 1);
[1   0   x^3]
> PrimePowersInVectorSpace(A, 2);
[1   0   x]
  
*/
  
  
IsPerfect := function(F)
//   
//  Whether F is a perfect field.
//  
  if IsZero(Characteristic(F)) then 
     return false;
  end if;
  if Type(F) eq FldFin then
     return true;
  elif Type(F) eq FldFun or Type(F) eq FldFunRat then
     return false;
  else
     error "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  end if;
end function;
   
   
BasisOfModuleOfDerivationsOverPerfectBase := function(F)
//   
//  Return a basis of the module of derivations of F over the recursively
//  first base field of F which is perfect.  
//
//  An element of F is then a p-th power if and only if all these 
//  derivations applied to the element are zero.
//
//  The function returns a sequence of maps representing the derivations
//  and a separating trancendence basis.
//
  if not ISA(Type(F), FldFunG) and not IsPerfect(F) then
     error "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  end if;

  if IsPerfect(F) then
     return [ Maps(F, F) | ], [ F | ];
  end if;
 
  // make derivation on F
  dx := Differential(SeparatingElement(F));
  f := map< F -> F | z :-> Differential(z)/dx >;

  // get derivations from coeff
  L, S := $$(ConstantField(F));

  // extend coeff derivations to F

  // ( only to get hold of the coeffs more easily,
  //   might unfortunately result in an expensive computation )
  Fre := RationalExtensionRepresentation(F); 
  o := EquationOrderFinite(Fre);
  kx := BaseRing(o);
  ExtendDerivation := function(f)
     g := function(z)
       znum, zden := IntegralSplit(Fre!z, o);
       zdenprime := kx!f(Eltseq(zden));
       znumprime := Fre!(o![ f(Eltseq(kx!a)) : a in Eltseq(znum) ]);
       return F!(( znumprime * zden - znum * zdenprime ) / zden^2);
     end function;	
     return map< F -> F | z :-> g(z) >;
  end function;	    
  
  return [ f ] cat [ ExtendDerivation(g) : g in L ], 
         [ SeparatingElement(F) ] cat ChangeUniverse(S, F);

end function;
   
   
//////////////////////////////////////////////////////////////////////////////
//  
// Method 1.
//
//  As it stands, it is exponential in the transcendence degree and   
//   exponential in log(p^k).
//  
  
  
DerivationConstantRep := function(x, f, a)
//   
//   x a separating element, f the derivation wrt to x, a element.
//   Write a = sum_{i=0}^{p-1} b_i x^i with f(b_i) = 0.
//   Return B = [b_0, ..., b_{p-1} ].
//           
            
   F := Parent(a);
   p := Characteristic(F);
   L := [ a ];
   b := a;
   for i in [1..p-1] do
      b := f(b) / i;
      Append(~L, b);
   end for;
   B := [ F!0 : i in [0..p-1] ];
   B[1 + p-1] := L[1 + p-1];
   i := p-2;
   while i ge 0 do
      B[1+ i] := L[1+ i] - &+ [ Binomial(j, i) * B[1+ j]*x^(j-i)
                                : j in [i+1..p-1] ];
      i := i - 1;
   end while;
   assert &and [ IsZero( f(b) ) : b in B];
   return B;
   
end function;


PrimePowerRepresentationSub := function(z, L, S)
   if #L eq 0 then
      return [ z ];
   end if;
   f := L[1];
   x := S[1];
   B := DerivationConstantRep(x, f, z);
   L1 := [ L[i] : i in [2..#L] ];
   S1 := [ S[i] : i in [2..#S] ];
   B := &cat [ $$(a, L1, S1) : a in B ];
   return B;
end function;

   
PrimePowerRepresentation := function(z, k)
//
//  Write z = sum_{i,j,..} lam_{i,j,...}^(p^k) x^i y^j ...
//   where x,y,.. form a separating transcendence basis.
//

  F := Parent(z);
  p := Characteristic(F);  

  if not ISA(Type(F), FldFunG) and not IsPerfect(F) then
     error "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  end if;
  
  if k eq 0 then
     return [ z ], [ F!1 ];
  elif k eq 1 then
    L, S := BasisOfModuleOfDerivationsOverPerfectBase(F);
    B := PrimePowerRepresentationSub(z, L, S);
    B := [ c where _, c := IsPower(b, p) : b in B ];
    T := [ F | ];
    for ind in CartesianPower([0..p-1], #S) do
       T[1+ &+ [ ind[#S-i+1]*p^(i-1) : i in [1..#S] ] ] :=
           &* [ S[i]^ind[i] : i in [ 1..#S] ];                      
    end for;
  else // k gt 1            
    B, T := $$(z, k-1);
    BB := [];
    TT := [];
    for i in [1..#B] do
       BB[i], TT[i] := $$(B[i], 1);     
    end for;
    B := &cat BB;
    T := &cat [ [ a^p * T[i] : a in TT[i] ] : i in [1..#T] ];
  end if;
          
  // check
  assert z eq &+ [ B[i]^(p^k) * T[i] : i in [1..#B] ];     
          
  return B, T;
  
end function;


   
PrimePowerKernelMatrix1 := function(A, k)
//   
//  Solve for x^(p^k) A = 0 where x^(p^k) is a vector whose coordinates   
//  are p^k-th powers in F = BaseRing(Parent(A)).  
//  A row matrix with a basis of the solution F-space x is returned.
//  
  
  F := BaseRing(Parent(A));
  p := Characteristic(F);  

  if not ISA(Type(F), FldFunG) and not IsPerfect(F) then
     error "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  end if;
  
  m := NumberOfColumns(A);
  
  if k eq 0 or m eq 0 then
    return KernelMatrix(A);
  else
     L := Eltseq(A);
     L := [ PrimePowerRepresentation(z, k) : z in L ];
     A1p := Matrix( #L[1] * m, &cat L );    
     return KernelMatrix(A1p);
  end if;
  
end function;
   
   
//////////////////////////////////////////////////////////////////////////
//  
// Method 2  
//  
//  As it stands, this is polynomial in the transcendence degree 
//  and in log(p^k) and in p.  
//  
//  However more echelon forms over F may have to be computed,
//  so for "small" fields F method one might be faster?
//  
  
  
PrimePowersInVectorSpaceSub := function(M, L)  
//   
// Returns a basis of the F^p-linear subspace of p-th powers of M.
// Thus coeffs are p-th powers, number of columns eq number of columns of M.
//  
  
  F := BaseRing(Parent(M));
  
  // clean up M
  M := EchelonForm(M);
  n := NumberOfRows(M);
  m := NumberOfColumns(M);
  M := IsZero(M) select Matrix( F, 0, m, [] )
       else Matrix( [ M[i] : i in [1..n] | not IsZero(M[i]) ] );
  n := NumberOfRows(M);
  
  if n eq 0 or n eq m then
     return M;
  end if;
  
  N := Matrix( F, n, #L * m, 
               [ &cat [ [ F | f(a) : a in Eltseq(M[i]) ] : f in L ] 
               : i in [1..n] ] );
  V := KernelMatrix(N);
  T := $$(V, L);
  return T * M;
  
end function;
  
  
PrimePowersInVectorSpace := function(M, k)  
//   
//  Return basis for F-vector space which consists of all coeffwise 
//  p-th roots of the row vector span of M.    
//   
  
  F := BaseRing(Parent(M));  
  p := Characteristic(F);
  
  if not ISA(Type(F), FldFunG) and not IsPerfect(F) then
     error "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  end if;
  
  L, _ := BasisOfModuleOfDerivationsOverPerfectBase(F);  
  T := M;
  
  for i in [1..k] do
     T := PrimePowersInVectorSpaceSub(T, L);
     if NumberOfRows(T) ne 0 then
        T := Matrix( [ [ F | c where _, c := IsPower(T[i][j], p) 
                     : j in [1..NumberOfColumns(T) ] ] 
                     : i in [1..NumberOfRows(T)] ] );
     end if;   
  end for;
  
  return T;
  
end function;
  
  
PrimePowerKernelMatrix2 := function(A, k)
//   
//  Solve for x^(p^k) A = 0 where x^(p^k) is a vector whose coordinates   
//  are p^k-th powers in F = BaseRing(Parent(A)).  
//  A row matrix with a basis of the solution space x is returned.
//  
  
  V := KernelMatrix(A);
  T := PrimePowersInVectorSpace(V, k);
  return T;
  
end function;
   
   
//////////////////////////////////////////////////////////////////////////   
  
  
CheckField := function(F)  
   if IsPerfect(F) then
      return true;
   end if;
   if not ISA(Type(F), FldFunG) then
     return false;
  end if;
  return $$(BaseRing(F)); 
end function;
   
   
intrinsic PrimePowerNullspaceMatrix(M::Mtrx, n::RngIntElt : 
                     UsePrimePowerRepresentation := false ) -> Mtrx
{Return a row basis of the F-vector space of all solutions x^(p^n) M = 0 where
F is the coefficient field of M and p is the characteristic of F}  
        
  require n ge 0 :
      "n must be non-negative";       
  F := BaseRing(Parent(M));
  require CheckField(F) :
    "Internal algorithm not (yet) implemented for this type of ring:", Type(F);
  
  if UsePrimePowerRepresentation cmpeq true then
     N := PrimePowerKernelMatrix1(M, n);
  else
     N := PrimePowerKernelMatrix2(M, n);
  end if;
  
  return N;
  
end intrinsic;  



intrinsic PrimePowerKernelMatrix(M::Mtrx, n::RngIntElt :
        UsePrimePowerRepresentation := false ) -> Mtrx
{Return a row basis of the F-vector space of all solutions x^(p^n) M = 0 where
F is the coefficient field of M and p is the characteristic of F}  
        
  require n ge 0 :
      "n must be non-negative";       
  F := BaseRing(Parent(M));
  require CheckField(F) :
    "Internal algorithm not (yet) implemented for this type of ring:", Type(F);

  return PrimePowerNullspaceMatrix(M, n : 
              UsePrimePowerRepresentation := UsePrimePowerRepresentation );
  
end intrinsic;  

