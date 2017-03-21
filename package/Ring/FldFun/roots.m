freeze;

//////////////////////////////////////////////////////////////////////////////
// FH Aug 2000
  
declare verbose ROOTS, 1;
  
//////////////////////////////////////////////////////////////////////////////
  
PlaceForRoots := function(F, m)
   if IsGlobal(F) then
      m := m - 1;
      repeat
         m := m + 1;
         h, P := HasRandomPlace(F, m);
      until h ne false;
      return P, m;
   else
      R := PolynomialRing(ConstantField(F));
      p := 2;
      for i in [1..m] do
         p := NextPrime(p);
      end for;
      L := Zeros(F!(R.1^Ceiling(m / Degree(F)) - p));
      min := Minimum( [ Degree(P) : P in L ] );
      for P in L do
         if Degree(P) eq min then
            return P, m;
         end if;
      end for;   
   end if;
end function;
   
//////////////////////////////////////////////////////////////////////////////

  
intrinsic Roots(f::RngUPolElt, D::DivFunElt) -> SeqEnum
{
  Compute the roots of f which lie in the Riemann-Roch space of D
};

  F := FunctionField(D);
  
  require IsGlobal(F) or Characteristic(F) eq 0
    : "Function field is required to be global or have characteristic zero";
  
  F := CoveringStructure(CoefficientRing(Parent(f)), F);
  require F cmpeq CoefficientRing(Parent(f)) or F cmpeq FunctionField(D) 
		      or F cmpeq FunctionField(CoefficientRing(Parent(f)))
     : "Arguments are not defined over the same function field";

  if Degree(f) le 0 then
     return [ F | ];
  end if;
     
  B := Basis(D);
  
  if #B eq 0 then
     return [ F | ];
  end if;
  
  // Get reasonably nice places not in the support of D. Additionally the 
  // coefficients of f must evaluate to finite values at these places.
    
  g := Eltseq(f);  
  m := Degree(D);
  ok := false;
  repeat
     m := m + 1;
     P, m := PlaceForRoots(F, m);
     if not P in Support(D) then
        h := [];
        ok := true;
        for v in g do
           w := Evaluate(v, P);
           if w cmpeq Infinity() then
              ok := false;
              break;
           else
              Append(~h, w);
           end if;
        end for;
     end if;   
  until ok;
  
  M := [ Evaluate(x, P) : x in B ];
  
  vprint ROOTS: "Place of degree", Degree(P), "taken";
  
  // Get roots of f mod P
    
  rf := ResidueClassField(P);
  g := PolynomialRing(rf) ! h;  
  
  vprint ROOTS: "Computing roots in", rf;
  
  roots := [ x[1] : x in Roots(g) ];
  
  vprint ROOTS: "Number of roots mod P is", #roots;
  
  if #roots eq 0 then
    return [ F | ];
  end if;
    
  // Linearize problem
    
  vprint ROOTS: "Doing linear algebra";  
    
    while (Universe(M) ne ConstantField(F)) do
	M := &cat[Eltseq(x) : x in M];
    end while;

  M := Matrix( ConstantField(F), Degree(P), M);
  if Rank(M) lt #B then
     error "Wrong dimension";
  end if;

    E := [[x] : x in roots];
    while (Universe(E[1]) ne ConstantField(F)) do
	E := [&cat[Eltseq(x) : x in t] : t in E];
    end while;

  roots := [ V ! x : x in E ] 
           where V is VectorSpace(ConstantField(F), Degree(P));
  S := [];
  for r in roots do
     ok, v := IsConsistent(M, r);
     if ok then
        s := &+ [ v[i] * B[i] : i in [1..#B] ];
        if Evaluate(f, s) eq 0 then
           Append(~S, s);
        end if;
     end if;   
  end for;
  
  return S;
  
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
  
