freeze;

//////////////////////////////////////////////////////////////////////////
//
//  Implements the general GHS construction for y^2 + y = c/x + a + bx
//   written by Florian Hess, version 20050829
//   mch - 06/06 - some minor changes and functions added to compute
//   and return the divisor map from the original to the descent field.
//

declare attributes  FldFunG:      datalist;  // sequence of data   
   
///////////////////////////////////////////////////////////////////////////
  
data_fmt := recformat< 
                i,              // Position in E`datalist
                K, k,           // the finite fields
                k0,             // prime field
                p, q,           // #k
                n,              // n = [K:k]
                c, a, b,        // the input coefficients from K
                f,              // c/x + a + bx for x = Kxf.1
                m_c, m_b,       // the minimal polynomials of c, b wrt Frob,
                                // Degree(m_c) le Degree(m_b)
                m_f,            // and of f
                xflip,          // whether a trafo x -> 1/x was done
                Delta_0,        // Genus 0 part of Delta
                Delta_1,        // the rest
                Kxf,            // base field of Type FldFun
                C_0,            // Kxf(wp^-1(Delta_0)) of genus zero
                y_0,            // y_0 \in wp^-1( f m_c(FrobKxf) ) in C_0
                C,              // C_0(\wp^-1(Delta_1))
                y,              // y \in \wp^-1( Delta_1[1] ) in C
                                // if #Delta_1 > 0. Undefined otherwise.
                FrobK,          // Frob on K
                FrobKxf,        // Frob on Kxf
                FrobC_0,        // Frob on C_0
                FrobC,          // Frob on C
                g,              // Genus of C
                d,              // [ C : C_0 ]
                M, mt, u, v,       // ztilde = u * z + v 
                ztilde,         // Rational Generator of C_0
                mztildex,       // x = mztildex(ztilde)
                Kztildef,       // K(ztilde)
                C_0toKztildef,  // Map C_0 --> K(ztilde)
                Cztilde,        // C = Kztilde( wp^-1( Delta_1 ) )
                CtoCztilde,     // Map C -> Cztilde
            
                ytilde,         // ytilde Generator of C over C_0  
                FrobCztilde,    // Frob on Cztilde
                Cztildeprim,    // Cztildeprim = Kztildef( ytilde )
          CztildetoCztildeprim, // Function C --> Cztildeprim  
                Cztildeprimrat, // Cztildeprimrat = kztildef ( ytilde )
                FrobKztildef,   // Frob on Kztildef
                Delta_1red,     // AS reduced Delta_1 over Kztildef  
                ASRed,          // y -> y - ASRed corr. to Delta_1red  
                yred,           // The corr element in Cztilde
            
		DivMap		// The divisor map from E -> Cztildeprimrat
>;
   
   
////////////////////////////////////////////////////////////////////////////
     
   
intrinsic ArtinSchreierExtension(c :: FldFinElt, 
                                 a :: FldFinElt, 
                                 b :: FldFinElt) -> FldFun
{ Returns the Artin-Schreier extension defined by y^p - y = c/x + a + b*x }
  
   K := Parent(c);
   require Parent(a) eq K and Parent(b) eq K
     : "Parameters are not defined over the same field";
  
   Kxf := RationalFunctionField(K); x := Kxf.1;
   Kxfy := PolynomialRing(Kxf); y := Kxfy.1;
   p := Characteristic(K);
   
   f := y^p - y - c/x - a - b*x;
   
   require IsIrreducible(f)
     : "Parameters do not define an irreducible equation";
   
   F := FunctionField(f); y := F.1;
   
   return F;
   
end intrinsic;

   
   
InitializeData := function(E, k)   
   
   if not assigned E`datalist then
      E`datalist := [];
   end if;
   
   found := 0;
   for i in [1..#E`datalist] do
      if E`datalist[i]`k eq k then
         found := i;
         break;
      end if;
   end for;   
      
   if found ne 0 then
      return true, "Ok", found;
   end if;
      
   // Check E
   
   if not IsFinite(Degree(E)) then
      return false, "Extension is not of finite degree", _;
   end if;
   
   if not Degree(RationalExtensionRepresentation(BaseField(E))) eq 1 then
      return false, "Base field is not a rational function field", _;
   end if;
   
   K := ConstantField(E);
   f := DefiningPolynomial(E);
   Kxfy := Parent(f);
   z := Coefficient(f, 0);
   Kxf := RationalFunctionField(K);
   z := Kxf!z;
   znum := Numerator(z);
   
   if Denominator(z) ne Kxf.1 or Degree(znum) gt 2 then
      return false, 
             "Defining equation is not of the form y^p - y - c/x - a - b*x", _;
   end if;
   
   c := -Coefficient(znum, 0);
   a := -Coefficient(znum, 1);
   b := -Coefficient(znum, 2);
   
   p := Characteristic(K);
   x := BaseRing(Kxfy)!(Kxf.1);
   if f ne (Kxfy.1)^p - (Kxfy.1) - c/x - a - b*x then
      return false, 
             "Defining equation is not of the form y^p - y - c/x - a - b*x", _;
   end if;
   
   if c eq 0 and b eq 0 then
      return false, "Extension is not regular", _;
   end if;

   k0 := PrimeField(k);
   if PrimeField(K) ne k0 or
      not IsDivisibleBy( Degree(K, k0), Degree(k, k0) ) then
      return false, "Second argument k is not a subfield of the constant field of the first argument", _; 
   end if;
   
   Embed(k, K);   
   
   if Trace(a, k0) ne 0 and Trace(c, k) eq 0 and Trace(b, k) eq 0 then
      return false, "Trace conditions are not met", _;
   end if;
   
   // Now everything is fine
   
   data := rec< data_fmt | >;
   
   data`k := k;
   data`K := K;
   data`k0 := k0;
   
   data`c := c;
   data`a := a;
   data`b := b;
   
   data`q := #k;
   data`p := Characteristic(k);
   data`n := Degree(data`K, k);
   
   data`i := #E`datalist + 1;
   Append(~E`datalist, data);
     
   return true, "Ok", data`i;
   
end function;
   
   
   
intrinsic MultiplyFrobenius( b :: RngElt, 
                             f :: RngUPolElt, 
                             Frob :: Map ) -> RngElt
{ Compute f(Frob) b. }        
  
   K := Parent(b);
   require CoveringStructure(BaseRing(Parent(f)), K) eq K and
           Domain(Frob) eq K and Codomain(Frob) eq K
     : "Parameters incompatible";
     
   l := [ K!x : x in Eltseq(f) ];  
   sum := K!0;
   c := b;
   for i in [1..#l] do
     sum := sum + l[i] * c;           
     c := Frob(c);
   end for;
   return sum;
   
end intrinsic;
  
  
  
intrinsic MinimalPolynomialFrobenius( b :: FldFinElt, 
                                      Frob :: Map ) -> RngUPolElt
{ Compute smallest GF(p)-polynomial m_b such that m_b(Frob) b = 0 }  
  
   K := Parent(b);
   require Domain(Frob) eq K and Codomain(Frob) eq K
     : "Parameters incompatible";
   
   p := Characteristic(Parent(b));

   // Mipo on b 
   ffp := GF(p);
   ffpsig := PolynomialRing(ffp);
   sig := ffpsig.1;
   l := [ Eltseq(b, ffp) ];
   i := 0;
  
   repeat
      i := i + 1;
      b := Frob(b);
      Append(~l, Eltseq(b, ffp));
      M := Matrix(l);
      M := BasisMatrix(Kernel(M));
   until Nrows(M) gt 0;
  
   f_mipo := Normalize(ffpsig!Eltseq(M[1]));
   assert MultiplyFrobenius(b, f_mipo, Frob) eq 0;
   return f_mipo;
   
end intrinsic;



intrinsic MinimalPolynomialFrobenius( b :: FldFinElt, 
                                      Frob :: Map,
                                      k :: FldFin ) -> RngUPolElt
{ Compute smallest k-polynomial m_b such that m_b(Frob) b = 0 }  
  
   K := Parent(b);
   require Domain(Frob) eq K and Codomain(Frob) eq K
     : "Parameters incompatible";
   
   // as a check
   Embed(k, K);
   
   // Mipo on b 
   ksig := PolynomialRing(k);
   sig := ksig.1;
   l := [ Eltseq(b, k) ];
   i := 0;
   c := b;
   
   repeat
      i := i + 1;
      c := Frob(c);
      Append(~l, Eltseq(c, k));
      M := Matrix(l);
      M := BasisMatrix(Kernel(M));
   until Nrows(M) gt 0;
  
   f_mipo := Normalize(ksig!Eltseq(M[1]));
   assert MultiplyFrobenius(b, f_mipo, Frob) eq 0;
   return f_mipo;
   
end intrinsic;




ComputeGenusAndDegree := procedure(~data)
                  
   K := data`K;         
   q := data`q;
   Kxf<x> := RationalFunctionField(K: Type := FldFun);
   Kxfrat := RationalFunctionField(K);  
   Kx := PolynomialRing(K);
   FrobK := hom< K -> K | x :-> x^q, y :-> y^(#K div q)/*Root(y, q)*/ >;
   FrobKxf := function(z)
      assert Parent(z) eq Kxf;
      z := Kxfrat!z;  
      num := Kx![ x^q : x in Eltseq(Numerator(z)) ];
      den := Kx![ x^q : x in Eltseq(Denominator(z)) ];
      return Kxf!(num/den);
   end function;
   FrobKxfInv := function(z)
      assert Parent(z) eq Kxf;
      z := Kxfrat!z;  
      num := Kx![ x^(#K div q)/*Root(x, q)*/ : x in Eltseq(Numerator(z)) ];
      den := Kx![ x^(#K div q)/*Root(x, q)*/ : x in Eltseq(Denominator(z)) ];
      return Kxf!(num/den);
   end function;
   FrobKxf := hom< Kxf -> Kxf | x :-> FrobKxf(x), y :-> FrobKxfInv(y) >;      
      
   m_c := MinimalPolynomialFrobenius(data`c, FrobK);  
   m_b := MinimalPolynomialFrobenius(data`b, FrobK);   
   m_f := Lcm( m_c, m_b );
   
   if Degree(m_c) gt Degree(m_b) then
      z := data`c;
      data`c := data`b;
      data`b := z;
      z := m_c;
      m_c := m_b;
      m_b := z;
      data`xflip := true;
   else   
      data`xflip := false;
   end if;

   // Genus of C and [C : C_0]
     
   p := data`p;  
   g := p^Degree(m_f) - p^(Degree(m_f)-Degree(m_c)) 
                      - p^(Degree(m_f)-Degree(m_b)) + 1;
   d := p^Degree(m_c);     
        
   // Return stuff     
        
   data`FrobK := FrobK;
   data`FrobKxf := FrobKxf;
   
   data`m_c := m_c;
   data`m_b := m_b;
   data`m_f := m_f;
   
   data`Kxf := Kxf;
   
   data`g := g;
   data`d := d;

end procedure;




intrinsic WeilDescentGenus(E :: FldFun, k :: FldFin ) -> RngIntElt
{ Returns the genus of the function field resulting by Weil descent }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`g then
      return E`datalist[i]`g;
   end if;
   
   ComputeGenusAndDegree(~E`datalist[i]);
   
   return E`datalist[i]`g;
   
end intrinsic;   
   

intrinsic WeilDescentDegree(E :: FldFun, k :: FldFin ) -> RngIntElt
{ Returns the degree over k(x) of the function field resulting by 
  Weil descent }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`d then
      return E`datalist[i]`d;
   end if;
   
   ComputeGenusAndDegree(~E`datalist[i]);
   
   return E`datalist[i]`d;
   
end intrinsic;   



ComputeDeltas := procedure(~data)
                 
   if not assigned data`g then
     ComputeGenusAndDegree(~data);
   end if;

   FrobKxf := data`FrobKxf;           
   m_c := data`m_c;
   m_f := data`m_f;
   x := data`Kxf.1;
   
   // Create Deltas
   f := data`c/x + data`a + data`b*x;
   z := MultiplyFrobenius( f, m_c, FrobKxf );
   Delta_0 := [];
   for i in [1..Degree(m_f)-Degree(m_c)] do
      Append(~Delta_0, z);
      z := FrobKxf(z);
   end for;
   Delta_1 := [];
   ff := f;
   for i in [1..Degree(m_c)] do
      Append(~Delta_1, ff);
      ff := FrobKxf(ff);
   end for;
   
   // Return stuff     
        
   data`f := f;
   data`Delta_0 := Delta_0;
   data`Delta_1 := Delta_1;
   
end procedure;



// Check code, maps von E nach C_red, conorm norm hom?



intrinsic WeilDescentDeltas(E :: FldFun, 
                            k :: FldFin) -> FldFunG, SeqEnum
{ Return Delta_0 and Delta_1 }
         
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`Delta_1 then
      return E`datalist[i]`Delta_0, E`datalist[i]`Delta_1;
   end if;
   
   ComputeDeltas(~E`datalist[i]);
   
   return E`datalist[i]`Delta_0, E`datalist[i]`Delta_1;
         
end intrinsic;



ComputeCandC_0 := procedure(~data)
                   
   if not assigned  data`Delta_1 then               
      ComputeDeltas(~data);
   end if;   
                   
   Kxf := data`Kxf;                
   Delta_0 := data`Delta_0;
   Delta_1 := data`Delta_1;
   
   // Create the field extension
   F := Kxf;
   p := data`p;
   for i in [1..#Delta_0] do
      Fy := PolynomialRing(F);
      C := FunctionField( (Fy.1)^p - (Fy.1) - (F!Delta_0[i]) 
                   : Check := false);      
      F := C;   
   end for;
   C_0 := F;
   for i in [1..#Delta_1] do
      Fy := PolynomialRing(F);
      C := FunctionField( (Fy.1)^p - (Fy.1) - (F!Delta_1[i]) 
                   : Check := false);      
      F := C;   
   end for;
   
   // Return stuff     
        
   data`C_0 := C_0;
   data`C := C;
   
end procedure;



intrinsic WeilDescentComposita(E :: FldFun, 
                               k :: FldFin) -> FldFunG, FldFunG
{ Return C_0 = Kxf( wp^(-1)( Delta_0 ) ) and C = C_0( wp^(-1)( Delta_1 ) ) }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`C then
      return E`datalist[i]`C_0, E`datalist[i]`C;
   end if;
   
   ComputeCandC_0(~E`datalist[i]);
   
   return E`datalist[i]`C_0, E`datalist[i]`C;
   
end intrinsic;   

/*************** Functions added by mch 07/06 ***************/
/** Solve y^(q-1)=z and y^q-y=z w/o getting roots of polys **/

// x in GF(q^r) has norm 1 or 0 to GF(q). Function finds a solution
// of y^(q-1)=x in GF(q^r)
function kummer_sol(x,q,r)
    K := Parent(x);
    if x eq 0 then return K!0; end if;

    // if z = sum(i=0 to r-1) x^(1+q+..q^(i-1))*t^(q^i) for any t in
    //  K has z != 0 then y =1/z works. Try first for t=x and if this
    //  gives z=0 try random t
    sum := x;
    terms := [x];
    for i in [1..r-1] do
	y := x*(terms[i]^q);
	sum +:= y;
	Append(~terms,y);
    end for;

    while sum eq 0 do
	t := Random(K);
	if t eq 0 then continue; end if;
	sum := t*x;
	for i in [2..r] do
	    t := t^q;
	    sum +:= terms[i]*t;
	end for;
    end while;
    return (1/sum);
end function;

// x in GF(q^r) has trace 0 to GF(q)=k. Function finds a solution
// of y^q-y=x in GF(q^r)
function AS_sol(x,q,r,k)
    K := Parent(x);
    if x eq 0 then return K!0; end if;

    // if z = sum(i=0 to r-1) (x+x^q+..+x^q^(i-1))*t^(q^i) for t with
    //  trace 1 to GF(q) then y =-z works.

    //First find elt with trace 1
    t := K.1;
    tr := Trace(t,k);
    while tr eq 0 do
	t := Random(K);
	tr := Trace(t,k);
    end while;
    t := t/(K!tr);

    // now for the sums (with t = (above t)^(q^-1))
    sum := x*t;
    term := x;
    for i in [1..r-2] do
	term := x + (term^q);
	t := t^q;
	sum +:= term*t;
    end for;

    return -sum;
end function;

/*****************************************************************/

Computeztilde := procedure(~data)
                 
  // Compute rational generator of C_0 (not using C_0)               
                 
  if not assigned data`Delta_1 then
     ComputeDeltas(~data);
  end if;
                  
  if #data`Delta_0 ne 0 then            
                
    // We proceed as in basic GHS                
    // Get non rational generator first            
    Kxfrat := RationalFunctionField(data`K);            
    Delta_0 := data`Delta_0;
    gamma := [ Coefficient(Numerator(Kxfrat!Delta_0[i]), 0) : 
               i in [1..#Delta_0] ];
    delta := [ Coefficient(Numerator(Kxfrat!Delta_0[i]), 1) : 
               i in [1..#Delta_0] ];
    Kxf := data`Kxf;                 
    m := #Delta_0+1;                     
    p := data`p;
    M := IdentityMatrix(data`K, m-1);
    for i in [1..m-1] do
       for j in [1..i-1] do
          M[i] := M[i] - Root(delta[i]/delta[j], p) * M[j];
          gamma[i] := gamma[i] - delta[i]/delta[j] * gamma[j];
          delta[i] := Root(delta[i]/delta[j], p) - delta[i]/delta[j];
       end for;
    end for;
    
    // represent t_[i] in t[m-1], i=m-1,...,1.  (z = t[m-1])
    Kz := PolynomialRing(data`K); z := Kz.1;
    mt := [];
    mt[m-1] := z;
    for i in [2..m-1] do
       mt[m-i] := (mt[m-i+1]^p - mt[m-i+1] - gamma[m-i+1]) / delta[m-i+1];
    end for;
    mzx := (mt[1]^p - mt[1] - gamma[1]) / delta[1];    
    //assert Evaluate(PolynomialRing(Kxf)!Eltseq(mzx), t[m-1]) eq Kxf.1;
    
    // Find the rational generator
      
    //   ( Frob(t[m-1]) = lam t[m-1] + mu
    //     Applying Frob to mzx( t[m-1 ) = Kxf.1 and equating coeffs  
    //     yields ... )
           
    lam := Coefficient(mzx, 1) / data`FrobK( Coefficient(mzx, 1) );
    mu := data`FrobK( Roots(mzx - Coefficient(mzx, 0)@@data`FrobK)[1][1] );
     
    //   ( ztilde = u t[m-1] + v. Applying Frob left and right and equating
    //     coeffs yields ... )
      
    q := data`q;
    n := data`n;
    Kz := PolynomialRing(data`K); z := Kz.1;
    u := kummer_sol(1/lam,q,n);//Representative(Roots(z^(q-1) - 1/lam))[1];
    v := AS_sol(u^q*mu,q,n,data`k);//Representative(Roots(z^q - z - u^q*mu))[1];

    // ztilde := u * t[m-1] + v;
    // assert data`FrobC_0(ztilde) eq ztilde;
    mztildex := Evaluate(mzx, (z - v)/u);
    assert &and [ c in k : c in Eltseq(mztildex) ] where k := data`k;
    
    // Return stuff
              
    data`mztildex := mztildex;
    data`M := M;
    data`mt := mt;          
    data`u := u;
    data`v := v;
    
  else
    
    data`mztildex := PolynomialRing(data`K).1;
    data`u := data`K!1;
    data`v := data`K!0;
    data`mt := [ data`mztildex ];    
    data`M := Matrix(1, [ data`K | 1 ]);
    
  end if;     
  
  Kztildef := RationalFunctionField(data`K : Type := FldFun);
  AssignNames(~Kztildef, [ "z" ]);    
  data`Kztildef := Kztildef;
  
end procedure;


ComputeRatParam := procedure(~data)
                 
  // Compute rational generator of C_0 and maps               
                 
  if not assigned data`C_0 then
     ComputeCandC_0(~data);
  end if;
                    
  if not assigned data`mztildex then
     Computeztilde(~data);
  end if;
                  
  if #data`Delta_0 ne 0 then            
                
    Kxf := data`Kxf;
    t := [];
    CC := data`C_0;
    while CC ne Kxf do
       Append(~t, CC.1);
       CC := BaseRing(CC);
    end while;
    t := Reverse(t);
    
    m := #data`Delta_0+1;                     
    M := data`M;
    u := data`u;
    v := data`v;
    ztilde := u * &+ [ MM[i] * t[i] : i in [1..m-1] ] + v
              where MM := M[m-1];
 
    // Compute C_0 --> K(ztilde) map
      
    Kztildef := data`Kztildef;
    mztildex := data`mztildex;
    
    Kxfrat := RationalFunctionField(data`K);
    C_0toKztildefKxf := function(c)
       assert Parent(c) eq Kxf;
       c := Kxfrat!c;
       c := Evaluate(Numerator(c), mztildex) /
            Evaluate(Denominator(c), mztildex);
       return Kztildef!c;
    end function;
       
    C_0 := data`C_0;   
    R := Parent(RationalFunction(C_0.1, Kxf));
    CoeffMap := hom< Kxf -> Kztildef | z :-> R!C_0toKztildefKxf(z) >;   
    m0 := Rank(R);
    // this is a bit redundant, see downstairs
    Kz := PolynomialRing(data`K); z := Kz.1;
    mt := data`mt;
    L := [ Evaluate(c, (z - v)/u) : c in mt ];
    L := ChangeUniverse(ChangeUniverse(L, Kxf), Kztildef);
    // Compute M^-1 L  (L a column)
    M := M^(-1);
    M := Matrix( NumberOfColumns(M), ChangeUniverse(Eltseq(M), Universe(L)));
    L := Matrix( NumberOfColumns(M), L) * Transpose(M);
    L := Eltseq(L[1]);
    MPolMap := hom< R -> Kztildef | CoeffMap, L>;//Reverse( L ) >;
    C_0toKztildef := function(c)
       assert Parent(c) eq C_0;
       c := RationalFunction(c, Kxf);
       c := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]])) where z := c;
       c := MPolMap(c);
       return c;
    end function;
    Kxfrat := RationalFunctionField(data`K);   
    KztildeftoC_0 := function(c)
       assert Parent(c) eq Kztildef;
       c := Kxfrat!c;
       return Evaluate(Numerator(c), ztilde) / 
              Evaluate(Denominator(c), ztilde);
    end function;
    C_0toKztildef := hom< C_0 -> Kztildef | x :-> C_0toKztildef(x),
                                            y :-> KztildeftoC_0(y) >;
    assert C_0toKztildef(ztilde) eq Kztildef.1;   
    assert (Kztildef.1)@@C_0toKztildef eq ztilde;
    //assert C_0toKztildef(1/ztilde + 1) eq 1/Kztildef.1 + 1;   
       
    // Return stuff
    
    data`ztilde := ztilde;
    data`C_0toKztildef := C_0toKztildef;
    
  else
    
    data`ztilde := data`Kxf.1;
    data`C_0toKztildef := map< data`Kxf -> data`Kztildef | x :-> x, 
                               y :-> y >;
  end if;     
       
end procedure;



intrinsic WeilDescentRationalParametrization(E :: FldFun, 
                                             k :: FldFin) -> Map
{ Return the rational parametrization of C_0 corresponding to a 
  Frobenius invariant generator}
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`C_0toKztildef then
      return E`datalist[i]`C_0toKztildef;
   end if;
   
   ComputeRatParam(~E`datalist[i]);
   return E`datalist[i]`C_0toKztildef;
   
end intrinsic;   



ExtendFrobenius := procedure(~data)
              
   if not assigned data`C then
     ComputeCandC_0(~data);   
   end if;
     
   m_c := data`m_c;
   m_b := data`m_b;
   m_f := data`m_f;
   f := data`f;
   
   K := data`K;
   Kxf := data`Kxf;
   C_0 := data`C_0;
   C := data`C;
   n := data`n;
   p := data`p;
   
   FrobK := data`FrobK;
   FrobKxf := data`FrobKxf;
   
   Ky := PolynomialRing(K); y := Ky.1;
   am_f := MultiplyFrobenius(data`a, m_f, FrobK);   
   v := Representative(Roots(y^p - y - am_f))[1];   
   c_f := (t^n - 1) div m_f where t := Parent(m_f).1;   
   vc_f := MultiplyFrobenius(v, c_f, FrobK);
   if IsZero(vc_f) then
      lambda := K!0;
   else
      c_f1 := Evaluate(c_f, 1);
      assert not IsZero(c_f1);
      lambda := - vc_f / c_f1;
   end if;

   // Now we know that y m_f = v + lambda where y in wp^-1( f ).
   // Want to adjust/define Frob such that y_0 = y m_c where 
   //    y_0 \in wp^-1( f m_c ).
   // Then y_0 (m_f / m_c) = y m_f = v + lambda.
     
   // Extend FrobKxf to C_0
     
   if C_0 ne Kxf then  
     
      //  ( Do stuff with m_fmc instead of m_f. )
      m_fmc := m_f div m_c;  
      R := Parent(RationalFunction(C_0.1, Kxf));
      CoeffFrobMap := hom< Kxf -> R | z :-> R!FrobKxf(z) >;   
      assert Degree(m_fmc) eq Rank(R);
      m0 := Rank(R);
      MPolFrobMap := hom< R -> R | CoeffFrobMap, 
                     ( [ R.(m0-i) : i in [1..m0-1] ] cat 
                        [ v + lambda - &+ [ Coefficient(m_fmc, i) * R.(m0-i) 
                                   : i in [0..m0-1]  ] ] ) >;
      gens := [];
      CC := C_0;
      while CC ne Kxf do
         Append(~gens, CC.1);
         CC := BaseRing(CC);
      end while;
   
      FrobC_0 := function(z)
         assert Parent(z) eq C_0;
         z := RationalFunction(z, Kxf);
	 z := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]]));
         z := MPolFrobMap(z);
         return Evaluate(z, gens);      
      end function;
         
      FrobC_0 := hom< C_0 -> C_0 | x :-> FrobC_0(x) >;   
         
      // check FrobC_0 has order dividing n   
      // On K is has order n so it has order n then.  
      y_0 := gens[#gens];
      yy := FrobC_0(y_0);
      i := 1;
      while yy ne y_0 do
         yy := FrobC_0(yy);
         i := i + 1;   
      end while;
      assert IsDivisibleBy(n, i);
      
   else
      // Case m_c = m_f
      FrobC_0 := FrobKxf;
      y_0 := C_0!(v + lambda);
   end if;
      
   if C ne C_0 then
   
      // Extend FrobC_0 to C
      //  ( works because we have chosen the correct extension to C_0.  
      //    Mipo is now m_c instead of m_f. )
      c_f := (t^n - 1) div m_c where t := Parent(m_f).1;  
      v := y_0;
      assert v^p - v eq (C_0!MultiplyFrobenius(f, m_c, FrobKxf));
      vc_f := MultiplyFrobenius(v, c_f, FrobC_0);
      assert IsZero(vc_f);
      lambda := K!0;
      
      // now we know that y m_c = v + lambda.
      R := Parent(RationalFunction(C.1, C_0));
      CoeffFrobMap := hom< C_0 -> R | z :-> R!FrobC_0(z) >;   
      assert Degree(m_c) eq Rank(R);
      m := Rank(R);
      MPolFrobMap := hom< R -> R | CoeffFrobMap, 
                        ( [ R.(m-i) : i in [1..m-1] ] cat 
                            [ v + lambda - &+ [ Coefficient(m_c, i) * R.(m-i) 
                               : i in [0..m-1]  ] ] ) >;
      gens := [];
      CC := C;
      while CC ne C_0 do
         Append(~gens, CC.1);
         CC := BaseRing(CC);
      end while;
   
      FrobC := function(z)
         assert Parent(z) eq C;
         z := RationalFunction(z, C_0);
	 z := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]]));
         z := MPolFrobMap(z);
         return Evaluate(z, gens);      
      end function;
      
      FrobC := hom< C -> C | x :-> FrobC(x) >;   
      
      // check FrobC has order n   
      y := gens[#gens];
      yy := FrobC(y);
      i := 1;
      while yy ne y do
         yy := FrobC(yy);
         i := i + 1;   
      end while;
      assert i eq n;
      
   else
      FrobC := FrobC_0;
   end if;   
      
   
   // Return stuff
   
   data`FrobC_0 := FrobC_0;
   data`FrobC := FrobC;
   
   data`y_0 := y_0;
   if assigned y then
      data`y := y;
   end if;
   
end procedure;



intrinsic WeilDescentFrobeniusExtensions(E :: FldFun, 
                                         k :: FldFin) -> Map, Map
{ Return the extensions of the Frobenius to C_0 and C }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`FrobC then
      return E`datalist[i]`FrobC_0, E`datalist[i]`FrobC;
   end if;
   
   ExtendFrobenius(~E`datalist[i]);
   return E`datalist[i]`FrobC_0, E`datalist[i]`FrobC;
   
end intrinsic;   






OreMult := function(f, g, q)
//
//   Polynomial multiplication in Ore domain K[sig]
//      Return f * g.
   
   R := Parent(f);
   x := R.1;
   sum := Coefficient(f, 0) * g;
   l := Eltseq(g);
   for i in [1..Degree(f)] do
      l := [ c^q : c in l ];
      sum := sum + Coefficient(f, i) * (R!l) * x^i;   
   end for;
   return sum;
end function;


OreRightQuotrem := function(f, g, q)
//
//  Polynomial division with remainder in Ore domain
//    Returns d, r such that f = d * g + r.
  
  R := Parent(f);
  d := R!0;
  r := f;
  x := R.1;
  while Degree(r) ge Degree(g) do
     s := Degree(r) - Degree(g);
     c := LeadingCoefficient(r) * LeadingCoefficient(g)^(-q^s) * x^s;
     d := d + c;
     r := r - OreMult(c, g, q);
  end while;
  assert f eq OreMult(d, g, q) + r;
  return d, r;
end function;
   
   
OreLeftQuotrem := function(f, g, q)
//
//  Polynomial division with remainder in Ore domain
//    Returns d, r such that f = g * d + r.
  
  R := Parent(f);
  K := BaseRing(R);
  d := R!0;
  r := f;
  x := R.1;
  qn_rt := #K div (q^Degree(g)); //qn := q^Degree(g);
  while Degree(r) ge Degree(g) do
     s := Degree(r) - Degree(g);
     //c := Root(LeadingCoefficient(r)/LeadingCoefficient(g), qn) * x^s;
     c := (LeadingCoefficient(r)/LeadingCoefficient(g))^qn_rt * x^s;
     d := d + c;
     r := r - OreMult(g, c, q);
  end while;
  assert f eq OreMult(g, d, q) + r;
  return d, r;
end function;
   
   
   
ComputeReducedDelta_1 := procedure(~data)
                          
   if not assigned data`mztildex then
       Computeztilde(~data);
   end if;
   
   if #data`Delta_1 ne 0 then                         
                            
      // do an AS degree reduction on mztildex
      bmztildex := data`b * data`mztildex;
      p := data`p;
      Ksig := PolynomialRing(data`K); sig := Ksig.1;
      h := &+ [ Coefficient(bmztildex, p^i) * sig^i : i in [0..d] ]
           where d := #(data`Delta_0);
      pPower := hom< Parent(bmztildex) -> Parent(bmztildex) | x :-> x^p >;
      d, r := OreLeftQuotrem(h, sig-1, p);
      d := MultiplyFrobenius(Parent(bmztildex).1, d, pPower);
      r := MultiplyFrobenius(Parent(bmztildex).1, r, pPower);
      r := r + Coefficient(bmztildex, 0);
      assert bmztildex eq d^p - d + r and Coefficient(d, 0) eq 0 
        and Degree(r) lt p;
      
      z := data`a + Coefficient(r, 0);
      l := Roots( sig^p - sig - z );
      if #l gt 0 then
        l := Representative(l)[1];
        d := d + l;
        r := r - z; 
      end if;
      
      Kztildef := data`Kztildef;                
      f := Kztildef!( data`c/(data`mztildex) + data`a + r );
      d := Kztildef!d;
      
      Kxfrat := RationalFunctionField(data`K);
      Kx := PolynomialRing(data`K);
      q := data`q;
      FrobKztildef := function(z)
         assert Parent(z) eq Kztildef;
         z := Kxfrat!z;  
         num := Kx![ x^q : x in Eltseq(Numerator(z)) ];
         den := Kx![ x^q : x in Eltseq(Denominator(z)) ];
         return Kztildef!(num/den);
      end function;
      FrobKztildefInv := function(z)
         assert Parent(z) eq Kztildef;
         z := Kxfrat!z;  
         num := Kx![ x^(#(data`K) div q)/*Root(x, q)*/ : x in Eltseq(Numerator(z)) ];
         den := Kx![ x^(#(data`K) div q)/*Root(x, q)*/ : x in Eltseq(Denominator(z)) ];
         return Kztildef!(num/den);
      end function;
         
      FrobKztildef := hom< Kztildef -> Kztildef | x :-> FrobKztildef(x),
                                                  y :-> FrobKztildefInv(y) >;
      Delta_1red := [];
      Append(~Delta_1red, f);
      for i in [2..#(data`Delta_1)] do
         f := FrobKztildef( f );
         Append(~Delta_1red, f);
      end for;
    
      // Return stuff

      data`FrobKztildef := FrobKztildef;
      data`Delta_1red := Delta_1red;
      data`ASRed := Kztildef!d;
      
   else
      
      data`FrobKztildef := data`FrobKxf;
      data`Delta_1red := data`Delta_1;
      data`ASRed := data`Kxf!0;
      
   end if;
      
end procedure;



intrinsic WeilDescentReducedDelta_1(E :: FldFun, 
                                    k :: FldFin) -> SeqEnum
{ Return the Artin Schreier reduction of Delta_1}
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`Delta_1red then
      return E`datalist[i]`Delta_1red;
   end if;
   
   ComputeReducedDelta_1(~E`datalist[i]);
   return E`datalist[i]`Delta_1red;
   
end intrinsic;   




ComputeReducedC := procedure(~data)
// reduced                  
                   
  if not assigned data`Delta_1red then
     ComputeReducedDelta_1(~data);   
  end if;
     
  if #data`Delta_1 ne 0 then              
                  
    p := data`p;
    Delta_1red := data`Delta_1red;
    F := data`Kztildef;
    Fy := PolynomialRing(F);
    Cztilde := FunctionField( (Fy.1)^p - (Fy.1) - (F!Delta_1red[1]) 
                       : Check := false);      
    F := Cztilde;   
    yred := Cztilde.1;
    for i in [2..#Delta_1red] do
       Fy := PolynomialRing(F);
       Cztilde := FunctionField( (Fy.1)^p - (Fy.1) - (F!Delta_1red[i]) 
                  : Check := false);      
       F := Cztilde;   
    end for;
  
    // Return stuff
              
    data`Cztilde := Cztilde;
    data`yred := Cztilde!yred;
    
  else
     
    data`Cztilde := data`Kztildef;
     
  end if;
     
end procedure;




intrinsic WeilDescentReducedCompositum(E :: FldFun, 
                                       k :: FldFin) -> FldFunG
{ Return C_red = Kxf( wp^(-1)(Delta_1) ) for the reduced Delta_1 }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`Cztilde then
      return E`datalist[i]`Cztilde;
   end if;
   
   ComputeReducedC(~E`datalist[i]);
   return E`datalist[i]`Cztilde;
   
end intrinsic;   




ComputeMapCtoReducedC := procedure(~data)
// reduced                  
                   
  if not assigned data`C then
     ComputeCandC_0(~data);   
  end if;
  
  if not assigned data`Cztilde then
     ComputeReducedC(~data);
  end if;
  
  if #data`Delta_1 ne 0 then              
                  
    C_0 := data`C_0;
    C := data`C;
    Kztildef := data`Kztildef;                
    C_0toKztildef := data`C_0toKztildef;
    Cztilde := data`Cztilde;
    
    // Map C --> Cztilde
    gens := [];
    CC := Cztilde;
    while CC ne Kztildef do
       Append(~gens, CC.1);
       CC := BaseRing(CC);
    end while;
    yred := gens[#gens];
    FrobKztildef := data`FrobKztildef;
    d := data`ASRed;  
    L := [ d ];
    for i in [2..#gens] do
       d := FrobKztildef( d );
       Append(~L, d);   
    end for;
    for i in [1..#gens] do
        gens[#gens-i+1] +:= L[i];            
    end for;
    R := Parent(RationalFunction(C.1, C_0));
    CoeffMap := hom< C_0 -> Cztilde | z :-> Cztilde!C_0toKztildef(z) >;   
    MPolMap := hom< R -> Cztilde | CoeffMap, Reverse(gens) >;
    CtoCztilde := function(c)
       assert Parent(c) eq C;
       c := RationalFunction(c, C_0);
       c := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]])) where z := c;
       c := MPolMap(c);
       return c;
    end function;
       
    gens := [];
    CC := C;
    while CC ne C_0 do
       Append(~gens, CC.1);
       CC := BaseRing(CC);
    end while;
    for i in [1..#gens] do
        gens[#gens-i+1] -:= L[i]@@C_0toKztildef;            
    end for;
    R := Parent(RationalFunction(Cztilde.1, Kztildef));
    CoeffMap := hom< Kztildef -> C | z :-> C!(z@@C_0toKztildef) >;   
    MPolMap := hom< R -> C | CoeffMap, Reverse(gens) >;
    CztildetoC := function(c)
       assert Parent(c) eq Cztilde;
       c := RationalFunction(c, Kztildef);
       c := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]])) where z := c;
       c := MPolMap(c);
       return c;
    end function;
       
    CtoCztilde := hom< C -> Cztilde | x :-> CtoCztilde(x), 
                                      y :-> CztildetoC(y) >;   
    assert CtoCztilde(C.1)@@CtoCztilde eq C.1;   
  
    // Return stuff
              
    data`CtoCztilde := CtoCztilde;
    data`yred := yred;
    
  else
     
    data`CtoCztilde := data`C_0toKztildef;
     
  end if;
     
end procedure;



intrinsic WeilDescentCompositaMap(E :: FldFun, 
                                  k :: FldFin) -> Map
{ Compute the isomorphism between C and C_red }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`CtoCztilde then
      return E`datalist[i]`CtoCztilde;
   end if;
   
   ComputeMapCtoReducedC(~E`datalist[i]);
   return E`datalist[i]`CtoCztilde;
   
end intrinsic;   



ExtendFrobeniustoCztilde := procedure(~data)
                            
   if not assigned data`Cztilde then
      ComputeReducedC(~data);
   end if;
                            
   if #data`Delta_1 ne 0 then
   
      // Extend FrobKztildef to Cztilde
        
      Kztildef := data`Kztildef;
      Cztilde := data`Cztilde;      
      FrobKztildef := data`FrobKztildef;
      
      // v := data`C_0toKztildef( data`y_0 );
      // instead:
        
      if #data`Delta_0 eq 0 then
        
         FrobK := data`FrobK;
         FrobKxf := data`FrobKxf;
         m_f := data`m_f;
         Ky := PolynomialRing(data`K); y := Ky.1;
         am_f := MultiplyFrobenius(data`a, m_f, FrobK);   
         v := Representative(Roots(y^data`p - y - am_f))[1];
         c_f := (t^data`n - 1) div m_f where t := Parent(m_f).1;   
         vc_f := MultiplyFrobenius(v, c_f, FrobK);
         if IsZero(vc_f) then
            lambda := data`K!0;
         else
            c_f1 := Evaluate(c_f, 1);
            assert not IsZero(c_f1);
            lambda := - vc_f / c_f1;
         end if;
         
         v := v + lambda;
      else       
              
         Kz := PolynomialRing(data`K); z := Kz.1;
         L := [ Evaluate(c, (z - v)/u) : c in mt ] where mt := data`mt
              where u := data`u where v := data`v;
         L := ChangeUniverse(ChangeUniverse(L, data`Kxf), Kztildef);
         // Compute topmost entry of M^-1 L  (L a column)
         M := data`M^(-1);
         M := M[1];
         
         v := &+ [ M[i] * L[i] : i in [1..#L] ];
                      
      end if;                   
         
      m_c := data`m_c;
      lambda := data`K!0;
      
      // we know that y m_c = v + lambda for the unreduced y
      // With yred = y - ASRed,  yred m_c = v + lambda - ASRed m_c 
        
      ASRed_mc := MultiplyFrobenius(data`ASRed, m_c, FrobKztildef);   
      R := Parent(RationalFunction(Cztilde.1, Kztildef));
      CoeffFrobMap := hom< Kztildef -> R | z :-> R!(data`FrobKztildef(z)) >;   
      assert Degree(m_c) eq Rank(R);
      m := Rank(R);
      MPolFrobMap := hom< R -> R | CoeffFrobMap, 
                        ( [ R.(m-i) : i in [1..m-1] ] cat 
                                [ v + lambda - ASRed_mc 
                                  - &+ [ Coefficient(m_c, i) * R.(m-i) 
                               : i in [0..m-1]  ] ] ) >;
      gens := [];
      CC := data`Cztilde;
      while CC ne Kztildef do
         Append(~gens, CC.1);
         CC := BaseRing(CC);
      end while;
   
      FrobCztilde := function(z)
         assert Parent(z) eq Cztilde;
         z := RationalFunction(z, Kztildef);
	 z := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]]));
         z := MPolFrobMap(z);
         return Evaluate(z, gens);      
      end function;
      
      // check FrobCztilde has order n   
      y := gens[#gens];
      yy := FrobCztilde(y);
      i := 1;
      while yy ne y do
         yy := FrobCztilde(yy);
         i := i + 1;   
      end while;
      assert IsDivisibleBy(data`n, i);
      
   else
      FrobCztilde := data`FrobKztildef;
   end if;   
   
   // Return stuff
             
   data`FrobCztilde := FrobCztilde;          
                       
end procedure;



intrinsic WeilDescentFrobeniusExtension(E :: FldFun, 
                                        k :: FldFin) -> Map
{ Return the extension of the Frobenius to C_red }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`FrobCztilde then
      return E`datalist[i]`FrobCztilde;
   end if;
   
   ExtendFrobeniustoCztilde(~E`datalist[i]);
   return E`datalist[i]`FrobCztilde;
   
end intrinsic;   





ComputeRationalPrimitiveElementofCztilde := procedure(~data)
                                            
  if not assigned data`FrobCztilde then
     ExtendFrobeniustoCztilde(~data);   
  end if;
     
  if #data`Delta_1 ne 0 then                     
                       
    Cztilde := data`Cztilde;                    
    Kztildef := data`Kztildef;                
    
    // This may be done without introducing extra coefficients
    // in special cases (e.g. #Delta_1 = 1)  
    n := data`n;
    w := NormalElement(data`K, data`k);
    yred := data`yred;
    FrobCztilde := data`FrobCztilde;    
    wyred := w * yred;
    ytilde := 0;
    for i in [1..n] do
       ytilde := ytilde + wyred;
       wyred := FrobCztilde( wyred );   
    end for;
   
    // Create primitive representation of C over Kztildef
      
    f := MinimalPolynomial(ytilde, Kztildef);
    Cztildeprim := FunctionField(f: Check := false);  
   
    // Create map Cztilde -> Cztildeprim
     
    // Represent yred_i = sum_j lam_i,j ytilde^j  
    d := data`d;  
    M := [];
    ytildej := Cztilde!1;
    Append(~M, Eltseq(ytildej, Kztildef));
    for j in [1..d-1] do
       ytildej := ytildej * ytilde;   
       Append(~M, Eltseq(ytildej, Kztildef));
    end for;
    M := Matrix(M);   
    v := Eltseq(data`yred, Kztildef);
    v := Matrix(d, v);
    v := Solution(M, v);
    assert NumberOfRows(v) eq 1;
    L := [];
    v := Eltseq(v[1]);
    Append(~L, Cztildeprim!v);
    FrobKztildef := data`FrobKztildef;
    for i in [2..#(data`Delta_1)] do
       v := [ FrobKztildef(c) : c in v ];
       Append(~L, Cztildeprim!v);
    end for;
    //L := Reverse( L );
   
    R := Parent(RationalFunction(Cztilde.1, Kztildef));
    CoeffMap := hom< Kztildef -> Cztildeprim | z :-> Cztildeprim!z >;
    m := Rank(R);
    assert data`p^m eq d;
    MPolMap := hom< R -> Cztildeprim | CoeffMap, L >; 
    CztildetoCztildeprim := function(z)
       assert Parent(z) eq Cztilde;
       z := RationalFunction(z, Kztildef);
       z := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]]));
       z := MPolMap(z);
       return z;
    end function;
    CztildeprimtoCztilde := function(z)
       assert Parent(z) eq Cztildeprim;
       z := RationalFunction(z, Kztildef);
       z := Evaluate(z, Reverse([Parent(z).i : i in [1 .. Rank(Parent(z))]]));
       z := Evaluate(z, [ ytilde ]);
       return z;
    end function;       
       
    CztildetoCztildeprim := hom< Cztilde -> Cztildeprim | 
                                 x :-> CztildetoCztildeprim(x),   
                                 y :-> CztildeprimtoCztilde(y) >;     
       
    assert CztildetoCztildeprim(ytilde) eq Cztildeprim.1;
    assert (Cztildeprim.1)@@CztildetoCztildeprim eq ytilde;
    //assert CztildetoCztildeprim(1/ytilde + 1) eq 1/Cztildeprim.1 + 1;
   
    // Return stuff
             
    data`ytilde := ytilde;          
    data`Cztildeprim := Cztildeprim;          
    data`CztildetoCztildeprim := CztildetoCztildeprim;
    
 else
    
    data`Cztildeprim := data`Kztildef;
    data`CztildetoCztildeprim := hom< data`Kztildef -> data`Kztildef |
                                      x :-> x, y :-> y >;
    
 end if;
 
end procedure;



intrinsic WeilDescentPrimitiveReducedCompositum(E :: FldFun, 
                                                k :: FldFin) -> FldFunG, Map
{ Return primitive extension and isomorphism from C_red }
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`CztildetoCztildeprim then
      return E`datalist[i]`Cztildeprim, E`datalist[i]`CztildetoCztildeprim;
   end if;
   
   ComputeRationalPrimitiveElementofCztilde(~E`datalist[i]);
   return E`datalist[i]`Cztildeprim, E`datalist[i]`CztildetoCztildeprim;
   
end intrinsic;   



ComputeCztildeprimrat := procedure(~data)
                          
   if not assigned data`Cztildeprim then
       ComputeRationalPrimitiveElementofCztilde(~data);
   end if;
                          
  if #data`Delta_1 ne 0 then                     

     f := DefiningPolynomial(data`Cztildeprim);
     R := RationalFunctionField(data`K);
     kxf := RationalFunctionField(data`k);
     l := ChangeUniverse(Eltseq(f), R);
     l := ChangeUniverse(l, kxf);
     kxfy := PolynomialRing(kxf); y := kxfy.1;
     f := kxfy!l;
     Cztildeprimrat := FunctionField(f: Check := false);
     
     // Return stuff
     data`Cztildeprimrat := Cztildeprimrat;
     
   else
      
      data`Cztildeprimrat := 
        RationalExtensionRepresentation(
             RationalFunctionField(data`k : Type := FldFun)
                );
      AssignNames(~data`Cztildeprimrat, [ "z" ]);
      
   end if;
   
   // Remark: substituting x -> 1/x should always yield
   // a imaginary quadratic equation.
     
end procedure;

/////////////////////////////////////////////////////////////////
//  Functions to produce the divisor map. Added mch 06/06

function GHSDivisorMapFF(D,C,mp,tr,F,n)
/*
    D is a place or divisor of the (algebraic) function field E.
    [K will denote the base field of E]
    Here 
     - C is k(C), the (alg) function field of the descent curve over
    k. [K:k] = n
     - mp is the function field morphism E -> K(C) [over K]
     - F is the frobenius map on K(C) [which fixes k(C)]
     - tr represents the trace map from K(C) to k(C) in a useful
    form for divisor descent. If f in K(C) then tr(f) is
    a sequence [a1..an] of elements in k(C) s.t.
    f = a1+a2*w+..+an*w^(n-1) where w = K.1

    The function returns true,"",Trace_K/k(mp(D)) if D is a
    valid place or divisor and false,errmsg,_ otherwise.
    [mp(D) is the pullback (conorm) of D under E->K(C)]	
*/

    E := Domain(mp);
    if (not ((Type(D) cmpeq PlcFunElt) or (Type(D) cmpeq DivFunElt)))
	or (FunctionField(D) ne E) then
	return false, 
	  "Argument must be a place or divisor of the function field",_;
    end if;

    // pull back to divisor on Cztildeprim - we work with ideals
    //  as Conorm can be slow (esp for divisors) and the fin/inf
    //  orders of E go to those of Cztildeprim
    if Type(D) cmpeq PlcFunElt then
	D := Divisor(D);
    end if;
    Cztp := Codomain(mp);
    Ifin,Iinf := Ideals(D);
    // do finite part first - Bfin basis of the finite ideal of pullback
    B := [E!b : b in Generators(Ifin)];
    Bfin := [mp(b) : b in B];
    // do finite part first - Binf basis of the finite ideal of pullback
    B := [E!b : b in Generators(Iinf)];
    Binf := [mp(b) : b in B];

    // now take the K/k trace down to C by binary powering
    Ofin := MaximalOrderFinite(Cztp);
    Ifin := ideal<Ofin|Bfin>;
/*
    for i in [1..n-1] do
	Bfin := [F(b) : b in Bfin];
	Ifin *:= ideal<Ofin|Bfin>;
    end for;
*/
    bits := Reverse(Prune(Intseq(n,2)));
    I := Ifin; m := 1;
    for bit in bits do
	Bfin := Generators(I);	
	for i in [1..m] do
	    Bfin := [F(b) : b in Bfin];
	end for;
	I *:= ideal<Ofin|Bfin>;
	m *:= 2;
	if bit eq 1 then
	    I := ideal<Ofin|[F(b) : b in Generators(I)]> * Ifin;
	    m +:= 1;
	end if;
    end for;
    Ifin := I;

    Oinf := MaximalOrderInfinite(Cztp);
    Iinf := ideal<Oinf|Binf>;
/*
    for i in [1..n-1] do
	Binf := [F(b) : b in Binf];
	Iinf *:= ideal<Oinf|Binf>;
    end for;
*/
    I := Iinf; m := 1;
    for bit in bits do
	Binf := Generators(I);	
	for i in [1..m] do
	    Binf := [F(b) : b in Binf];
	end for;
	I *:= ideal<Oinf|Binf>;
	m *:= 2;
	if bit eq 1 then
	    I := ideal<Oinf|[F(b) : b in Generators(I)]> * Iinf;
	    m +:= 1;
	end if;
    end for;
    Iinf := I;

    Ofin := MaximalOrderFinite(C);
    Bfin := &cat[tr(b) : b in Generators(Ifin)];
    Ifin := ideal<Ofin|Bfin>;

    Oinf := MaximalOrderInfinite(C);
    Binf := &cat[tr(b) : b in Generators(Iinf)];
    Iinf := ideal<Oinf|Binf>;

    return true,"",Divisor(Ifin,Iinf);
end function;

function MakeDivisorMapForFF(E,i)
/*
  E is an Artin-Schreier AlFF/K with GHS descent data.
  If C is the descent AlFF/k, this function returns
  the divisor map that takes divisors of E/K to
  divisors of C/k by pullback from E/K to C/K
  followed by the trace down to C/k
*/ 
    data := E`datalist[i];
    Kzt := data`Kztildef;
    Cztp := data`Cztildeprim;
    Cztpr := data`Cztildeprimrat;
    mp := data`CztildetoCztildeprim;
    X := Evaluate(data`mztildex,Kzt.1);
    if data`xflip then X := 1/X; end if;
    if #data`Delta_1 ne 0 then
	Y := data`yred+data`ASRed;
    else
	Y := Evaluate((data`mt)[1],(Kzt.1-data`v)/data`u);
    end if;
    L := [mp(Y),mp(X)];
    if Type(BaseRing(E)) ne FldFunRat then
	Append(~L,1);
    end if;
    boo,mp,_ := HasMorphismFromImages(FunctionFieldCategory())
		  (E,Cztp,L);
    assert boo;

    F := data`FrobKztildef;
    kzt := BaseRing(Cztpr);
    n := data`n;

    K := data`K;
    matr1 := [K.1^i : i in [0..n-1]];
    matrws := [[K.1^i : i in [0..n-1]]];
    for i in [1..n-1] do
	matr := [(data`FrobK)(e): e in matrws[i]];
	Append(~matrws,matr);
    end for;
    mat := Matrix(K,matrws);
    mat := mat^-1;
    Ktok := function(x)
	vec := [x];
	for i in [1..n-1] do
	    Append(~vec,F(vec[i]));
	end for;
	return [kzt| &+[mat[i,j]*vec[j] : j in [1..n]] : i in [1..n]];
    end function;
    tr := map<Cztp -> PowerSequence(Cztpr)|
		x :-> [&+[seqk[i][j]*(Cztpr.1)^(i-1) : i in [1..#es]]
				: j in [1..n]]
		where seqk := [Ktok(es[i]) : i in [1..#es]]
		where es is Eltseq(x)>;

    F1 := map<Cztp -> Cztp | x :-> &+[F(es[i])*(Cztp.1)^(i-1) : i in [1..#es]]
		where es is Eltseq(x)>;

    div_map := function(x)
	ok,mess,D := GHSDivisorMapFF(x,Cztpr,mp,tr,F1,n);
	if not ok then
	    Traceback();
	    error mess;
	end if;
	return D;	
    end function;

    return div_map;
end function;

/////////////////////////////////////////////////////////////////
   
   
intrinsic WeilDescent(E :: FldFun, 
                      k :: FldFin) -> FldFunG, Map
{ Return function field obtained by Weil descent and the
  descent map for divisors.}
  
   ok, mess, i := InitializeData(E, k);
   require ok : mess;
  
   if assigned E`datalist[i]`Cztildeprimrat then
      if not assigned E`datalist[i]`DivMap then
	E`datalist[i]`DivMap := MakeDivisorMapForFF(E,i);
      end if;
      return E`datalist[i]`Cztildeprimrat,E`datalist[i]`DivMap;
   end if;
   
   ComputeCztildeprimrat(~E`datalist[i]);
   E`datalist[i]`DivMap := MakeDivisorMapForFF(E,i);
   return E`datalist[i]`Cztildeprimrat,E`datalist[i]`DivMap;
   
end intrinsic;   


