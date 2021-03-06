freeze;

/* quasicylic and quasi twisted cyclic codes
  
   v1.0 13.03.2002

   Markus Grassl
   IAKS
   Univeritaet Karlsruhe
   Germany
   e-mail: grassl@ira.uka.de
 
*/   

poly_to_vec:=function(p,V);
// converts the coefficients of the polynomial p into a vector in V,
// appending zeroes
  n:=Degree(V);
  v:=Eltseq(p mod (Parent(p).1^n-1));
  return V!(v cat [0:i in [#v+1..n]]);
end function;

intrinsic QuasiCyclicCode(n::RngIntElt,Gen::[RngUPolElt]) -> Code
{Constructs the quasi-cyclic code with generator polynomials given by
Gen of length n. Attaches the generator matrices of the cyclic codes
generated by Gen side by side. Requires that n be a multiple of #Gen}

  require n mod #Gen eq 0 :
      "The length n must be a multiple of the number of generators";

  return QuasiCyclicCode(n,Gen,1);
  
end intrinsic;

intrinsic QuasiCyclicCode(n::RngIntElt,Gen::[RngUPolElt],h::RngIntElt) -> Code
{Constructs the quasi-cyclic code with generator polynomials given by
Gen of length n. Attaches the Generator matrices of the cyclic codes
generated by Gen 2-dimensionally, stacking with height h. Requires
that #Gen be a multiple of h, and that n be a multiple of #Gen/h}

  require h gt 0 : "Stacking height must be positive integer";
  require #Gen mod h eq 0 : 
       "Number of generator polynomials must be a multiple of h";
  require n mod (#Gen div h) eq 0 : 
       "n must be a multiple of #Gen/h";

  n0:=n div (#Gen div h);
  F:=CoefficientRing(Gen[1]);
  V:=RSpace(F,n0);
  gen_vecs:=[poly_to_vec(g,V):g in Gen];
  
  return QuasiCyclicCode(gen_vecs,h);
    
end intrinsic;

intrinsic QuasiCyclicCode(Gen::[ModTupRngElt])->Code
{Constructs the quasi cyclic code generated by simultaneous cylic shifts of the vectors in Gen.}

   return QuasiCyclicCode(Gen,1);

end intrinsic;

intrinsic QuasiCyclicCode(Gen::[ModTupRngElt],h::RngIntElt)->Code
{Constructs the quasi cyclic code generated by simultaneous cylic shifts of the vectors in Gen, arranging them 2-dimensionally with height h.}

  require h gt 0 : "Stacking height must be positive integer";
  require #Gen mod h eq 0 : 
      "Number of generators must be a multiple of h";

  F:=CoefficientRing(Generic(Universe(Gen)));
  m:=Degree(Generic(Universe(Gen)));
  p:=#Gen div h;
  N:=m*p;
  G:=RMatrixSpace(F,m*h,N)!0;
  for k:=0 to h-1 do
    for i:=1 to p do
      v:=Gen[p*k+i];
      for j:=0 to m-1 do
  	  InsertBlock(~G,RMatrixSpace(F,1,m)!Rotate(v,j),k*m+j+1,(i-1)*m+1);
      end for;
    end for;
  end for;

  C :=  LinearCode(G);

    //call this to register it as quasicyclic internally
  _ := IsQuasiCyclic(C);

  return C;
end intrinsic;

/////// ----------------- Now Additive quasi cyclic codes -----------//

intrinsic AdditiveQuasiCyclicCode(n::RngIntElt,Gen::[RngUPolElt])-> CodeAdd
{Constructs the K-additive quasi-cyclic code with generator polynomials given by
Gen of length n, where K is the prime field. 
Attaches the generator matrices of the cyclic codes
generated by Gen side by side. Requires that n be a multiple of #Gen}
    F := CoefficientRing(Universe(Gen));
    K := PrimeField(F);
    return AdditiveQuasiCyclicCode(K, n, Gen);
end intrinsic;

intrinsic AdditiveQuasiCyclicCode(K::FldFin, n::RngIntElt,Gen::[RngUPolElt]) 
							    -> CodeAdd
{Constructs the K-additive quasi-cyclic code with generator polynomials given by
Gen of length n. Attaches the generator matrices of the cyclic codes
generated by Gen side by side. Requires that n be a multiple of #Gen}

  F := CoefficientRing(Universe(Gen));  
  require Type(F) eq FldFin : "Polynomials must be over a field";
  require Characteristic(F) eq Characteristic(K) and K subset F :
	"K must be a subfield of the coefficient ring of the generators";
  require n mod #Gen eq 0 :
      "The length n must be a multiple of the number of generators";

  return AdditiveQuasiCyclicCode(K, n, Gen, 1);
  
end intrinsic;

intrinsic AdditiveQuasiCyclicCode(n::RngIntElt,Gen::[RngUPolElt],
                                                        h::RngIntElt) -> CodeAdd
{Constructs the K-additive quasi-cyclic code with generator polynomials given by
Gen of length n, where K is the prime field. 
Attaches the Generator matrices of the cyclic codes
generated by Gen 2-dimensionally, stacking with height h. Requires
that #Gen be a multiple of h, and that n be a multiple of #Gen/h}

  F := CoefficientRing(Universe(Gen));
  K := PrimeField(F);

  return AdditiveQuasiCyclicCode(K, n, Gen, h);
end intrinsic;


intrinsic AdditiveQuasiCyclicCode(K::FldFin, n::RngIntElt,Gen::[RngUPolElt],
							h::RngIntElt) -> CodeAdd
{Constructs the K-additive quasi-cyclic code with generator polynomials given by
Gen of length n. Attaches the Generator matrices of the cyclic codes
generated by Gen 2-dimensionally, stacking with height h. Requires
that #Gen be a multiple of h, and that n be a multiple of #Gen/h}

  F := CoefficientRing(Universe(Gen));  
  require Type(F) eq FldFin : "Polynomials must be over a field";
  require Characteristic(F) eq Characteristic(K) and K subset F :
	"K must be a subfield of the coefficient ring of the generators";
  require h gt 0 : "Stacking height must be positive integer";
  require #Gen mod h eq 0 : 
       "Number of generator polynomials must be a multiple of h";
  require n mod (#Gen div h) eq 0 : 
       "n must be a multiple of #Gen/h";

  n0:=n div (#Gen div h);
  V:=KSpace(F,n0);
  gen_vecs:=[poly_to_vec(g,V):g in Gen];
  
  return AdditiveQuasiCyclicCode(K, gen_vecs, h);
    
end intrinsic;

intrinsic AdditiveQuasiCyclicCode(Gen::[ModTupFldElt])->CodeAdd
{Constructs the K-additive quasi cyclic code generated by simultaneous 
cyclic shifts of the vectors in Gen, where K is the prime field.}
    F := Field(Universe(Gen));
    K := PrimeField(F);

    return AdditiveQuasiCyclicCode(K, Gen);
end intrinsic;

intrinsic AdditiveQuasiCyclicCode(K::FldFin, Gen::[ModTupFldElt])->CodeAdd
{Constructs the K-additive quasi cyclic code generated by simultaneous 
cyclic shifts of the vectors in Gen.}

  F := Field(Universe(Gen));  
  require Characteristic(F) eq Characteristic(K) and K subset F :
	"K must be a subfield of the coefficient ring of the generators";

   return AdditiveQuasiCyclicCode(K, Gen,1);

end intrinsic;

intrinsic AdditiveQuasiCyclicCode(Gen::[ModTupFldElt],
						    h::RngIntElt)->CodeAdd
{Constructs the K-additive quasi cyclic code generated by simultaneous 
cyclic shifts of the vectors in Gen, where
K is the prime field, arranging them 2-dimensionally 
with height h.}

  F := Field(Universe(Gen));  
  K := PrimeField(F);

  return AdditiveQuasiCyclicCode(K, Gen, h);

end intrinsic;

intrinsic AdditiveQuasiCyclicCode(K::FldFin, Gen::[ModTupFldElt],
						    h::RngIntElt)->CodeAdd
{Constructs the K-additive quasi cyclic code generated by simultaneous 
cyclic shifts of the vectors in Gen, arranging them 2-dimensionally 
with height h.}

  F := Field(Universe(Gen));  
  require Characteristic(F) eq Characteristic(K) and K subset F :
	"K must be a subfield of the coefficient ring of the generators";
  require h gt 0 : "Stacking height must be positive integer";
  require #Gen mod h eq 0 : 
      "Number of generators must be a multiple of h";

  m:=Degree(Generic(Universe(Gen)));
  p:=#Gen div h;
  N:=m*p;
  G:=KMatrixSpace(F,m*h,N)!0;
  for k:=0 to h-1 do
    for i:=1 to p do
      v:=Gen[p*k+i];
      for j:=0 to m-1 do
  	  InsertBlock(~G,KMatrixSpace(F,1,m)!Rotate(v,j),k*m+j+1,(i-1)*m+1);
      end for;
    end for;
  end for;

  C := AdditiveCode(K, G);
    //call this to register it as quasicyclic internally
  _ := IsQuasiCyclic(C);

  return C;
end intrinsic;


//------------------ quasi twisted codes ------------------------------//


intrinsic QuasiTwistedCyclicCode(n::RngIntElt,Gen::[RngUPolElt],alpha::FldFinElt)->Code
{Construct the quasi-twisted cyclic code of length n pasting together the constacylic codes with parameter alpha generated by the polynomials in Gen.}

  require n mod #Gen eq 0 :
      "The length n must be a multiple of the number of generators";

  n0:=n div #Gen;
  F:=CoefficientRing(Gen[1]);
  V:=KSpace(F,n0);
  gen_vecs:=[poly_to_vec(g,V):g in Gen];

  return QuasiTwistedCyclicCode(gen_vecs,alpha);

end intrinsic;

intrinsic QuasiTwistedCyclicCode(Gen::[ModTupRngElt],alpha::FldFinElt)->Code
{Construct the quasi-twisted cyclic code generated by simultaneous 
constacylic shifts w.r.t. alpha of the vectors in Gen.}

  F:=CoefficientRing(Universe(Gen));
  m:=Degree(Universe(Gen));
  p:=#Gen;
  N:=m*p;
  G:=KMatrixSpace(F,m,N)!0;
  s:=MatrixRing(F,m)!0;
  for i:=1 to m-1 do 
    s[i,i+1]:=1;
  end for;
  s[m,1]:=alpha;
  for i:=1 to p do
    v:=Gen[i];
    for j:=0 to m-1 do
      InsertBlock(~G,KMatrixSpace(F,1,m)!(v*s^j),j+1,(i-1)*m+1);
    end for;
  end for;

  return LinearCode(G);

end intrinsic;

