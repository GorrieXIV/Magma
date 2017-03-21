freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                     MODFORM: Modular Forms in MAGMA
 
                              William A. Stein        
                         
   FILE: misc.m

   $Header: /home/was/magma/packages/modform/code/RCS/misc.m,v 1.1 2001/05/30 18:55:42 was Exp $

   $Log: misc.m,v $
   Revision 1.1  2001/05/30 18:55:42  was
   Initial revision


 ***************************************************************************/


function MinimalLiftOfCharacter(e)
   // A pair eps, phi, where eps is a minimal lift of e to characteristic 0
   // and phi is a homomorphism from BaseRing(eps) to BaseRing(e), that is
   // defined on a subset of the domain.

   assert Type(e) eq GrpDrchElt;
   R := BaseRing(Parent(e));

   if Type(R) in {FldCyc, FldRat} then
      return e, map<R->R | x :-> x>;
   end if;

   G := Parent(e);
   u, r := DistinguishedRoot(G);
   d := Order(e);
   if d eq 1 then
      K := RationalField();
      z := K!1;
      phi := hom<K -> R | a :-> R!a>;
   elif d eq 2 then
      K := RationalField();
      z := K!(-1);
      phi := hom<K -> R | a :-> R!a>;
   else
      K := CyclotomicField(d); z := K.1;
      phi := hom<K -> R | u^(r div d) >;
   end if;
   H := DirichletGroup(Modulus(G),K,z,d);
   v := Eltseq(e);
   g := GCD(v);
   assert r mod d eq 0;
   eps := H![Integers()|a div (r div d) : a in v];
   return eps, phi;
end function;

// This was only called in EchelonPowerSeriesSequence (below), 
// so get rid of it!
/*
function EchelonPolySequence(P, prec) 
// Put the sequence of poly's in Echelon form.
   if #P eq 0 then 
      return P;
   end if;
   R    := Universe(P);
 //mat  := RMatrixSpace(BaseRing(R),#P,prec);
 //A    := mat!&cat[[Coefficient(f,i) : i in [0..prec-1]] :  f in P];
   A    := Matrix(BaseRing(R),
                  [[Coefficient(f,i) : i in [0..prec-1]] :  f in P]);
   A    := EchelonForm(A);
   return [&+[A[j][i+1]*R.1^i : i in [0..prec-1]] : j in [1..#P] | A[j] ne Parent(A[j])! 0];
end function;
*/

function EchelonPowerSeriesSequence(P)
   if #P eq 0 then
      return P;
   end if;
   /*
   R<q> := Parent(P[1]); 
   prec := Min([AbsolutePrecision(f) : f in P]);
   E := EchelonPolySequence(P,prec);
   return [f + O(q^prec) : f in E];
   */
   R := Universe(P);
   prec := Min([AbsolutePrecision(f) : f in P]);
   A := Matrix(BaseRing(R), [[Coefficient(f,i) : i in [0..prec-1]] : f in P]);
   A := EchelonForm(A);
   // ignore zero rows
   r := Nrows(A);
   while r gt 0 and IsZero(A[r]) do r -:= 1; end while;
   return [ R! Eltseq(A[i]) + O(R.1^prec) : i in [1..r]];
end function;

function CoercePowerSeries(f, phi, q)
   assert Type(f) eq RngSerPowElt;
   assert Type(phi) eq Map;
   assert Type(q) eq RngSerPowElt;
   prec := AbsolutePrecision(f);
   return &+[phi(Coefficient(f,n))*q^n : n in [0..prec-1]] + O(q^prec);
end function;

function MakeLattice(B)
   Mat := RMatrixSpace(Rationals(),#B, #Eltseq(B[1]));
   X   := Mat!B;
   if Dimension(RowSpace(X)) eq 0 then
      return RowSpace(X);
   end if;
   return Lattice(X);
end function;

/*
function Saturate(B) 
   t := Cputime();
   if Type(B[1]) eq SeqEnum then
      V := RSpace(Rationals(), #B[1]);
      B := [V|b : b in B];
   end if;
   L := MakeLattice(B);
   S := PureLattice(L);
   return S;
end function;

function SaturatePowerSeriesSequence(P) 
   // Returns generators for the saturation of the Z-module generated
   // by the sequence of q-expansions.
   if #P eq 0 then 
      return P;
   end if;
   R := Parent(P[1]);
   prec := Min([AbsolutePrecision(f) : f in P]);
   X    := [[Integers()!Coefficient(f,i) : i in [0..prec-1]] :  f in P];
   S := Saturate(X);
   S    := sub<RSpace(Integers(),Degree(S)) | [Eltseq(b) : b in Basis(S)]>;
   return [&+[Integers()!(v[i])*R.1^(i-1) : 
                 i in [1..prec]] + O(R.1^prec): v in Basis(S)];
end function;
*/

function SaturatePowerSeriesSequence(P) 
   // Returns generators for the saturation of the Z-module generated
   // by the sequence of q-expansions.
   // AKS version, 18/5/07
   if #P eq 0 then 
      return P;
   end if;
   R := Parent(P[1]);
   prec := Min([AbsolutePrecision(f) : f in P]);
   Z := IntegerRing();
   S := Matrix([[Z!Coefficient(f,i) : i in [0..prec-1]] :  f in P]);
   S := Saturation(S);
   S := HermiteForm(S);
   return [&+[Integers()!(S[r, i])*R.1^(i-1) : 
                 i in [1..prec]] + O(R.1^prec): r in [1 .. Nrows(S)]];
end function;


ALPHABET := {@ "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L",
     "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z" @};
alphabet := {@ "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
     "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z" @};
function IsogenyCodeToInteger(s)
// Returns the number n so that s = ToIsogenyCode(n).
   return 26*(#s-1)+Index(ALPHABET,s[1])+Index(alphabet,s[1]);
end function;

function ToIsogenyCode(n)
// Returns the n-th isogeny coding.  The coding goes A,B,C,...,Z,AA,BB,...
   if n eq 0 then return "?"; end if;
   return &cat[ALPHABET[((n-1)mod 26)+1]: i in [0..((n-1) div 26)]];
end function;

function ToLowerCaseLetter(n)
// Returns the n-th isogeny coding.  The coding goes a,b,c,...,z,aa,bb,...
   if n eq 0 then return "?"; end if;
   return &cat[alphabet[((n-1)mod 26)+1]: i in [0..((n-1) div 26)]];
end function;


intrinsic mfdevel(fun::MonStgElt, mesg::MonStgElt)
{Don't use this}
   vprintf ModularForms,2 : "\t(mfdevel: in %o -- %o)\n", fun, mesg;
end intrinsic;


