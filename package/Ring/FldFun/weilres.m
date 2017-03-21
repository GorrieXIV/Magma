freeze;

forward HyperEllipticReduce;

//////////////////////////////////////////////////////////////////////////////
  
  
EmbedOverSubRing := procedure(k1, k2, k, x)
//   
//  Install an embedding of k1 in k2 by mapping the generator
//  of k1 over k to x in k2. If k is not yet embedded into k1 and k2,
//  proper embeddings are chosen. Results in an error if k1 cannot be
//  embedded in k2 as requested (e.g. other embedding exists already, 
//  mathematically not possible, ...).
//  
                                                    
   Embed(k, k1);
   Embed(k, k2);
   
   assert x in k2;
   if MinimalPolynomial(x, k) ne MinimalPolynomial(Generator(k1, k)) then
      error "Minimal polynomial of x over k is not equal to the minimal polynomial of the generator of k1 over k";
   end if;  
   
   y := Evaluate(PolynomialRing(k)!Eltseq(Generator(k1, PrimeField(k1)), k),
                 x);
   Embed(k1, k2, y);
   
end procedure;


//////////////////////////////////////////////////////////////////////////////

intrinsic WeilRestriction(E::FldFun, n:: RngIntElt : Reduction := true) -> FldFun, UserProgram
{A hyperelliptic function field in the Weil restriction over GF(q) of the elliptic function field E: y^2 + xy + x^3 + ax^2 + b defined over GF(q^n)};
   
    require Type(Reduction) eq BoolElt : "Reduction must have a boolean value";

   require not Degree(E) cmpeq Infinity() : 
     "Degree of function field must be finite";
   
   K := ConstantField(E);
   
   require IsFinite(K) and Characteristic(K) eq 2 :
    "Constant field must be a finite field of characteristic 2";
  
   require Degree(K, GF(2)) mod n eq 0 :
    "Second argument must divide the degree of the constant field over GF(2)";

   KT := PolynomialRing(K);
   KTy := PolynomialRing(KT);

    require CoefficientRing(EquationOrderFinite(E)) cmpeq KT : 
	"Field must be an absolute extension of the rational function field";

   k := GF(2, Degree(K, GF(2)) div n);
   p := 2;
   q := #k;
     
   Embed(k, K);
   
   b := Evaluate(Evaluate(KTy!DefiningPolynomial(E), 0), 0);
   a := Evaluate(Evaluate(KTy!DefiningPolynomial(E), 0), 1) - 1 - b;
   
   qnp := q^n div p;
   alpha := [ a^(q^i) : i in [0..n-1] ];
   beta := [ b^(q^i) : i in [0..n-1] ];
   delta := [ (beta[1] + beta[i+1])^(qnp) : i in [1..n-1] ];
   gamma := [ alpha[1] + alpha[i+1] : i in [1..n-1] ];
   deltabef := [ d : d in delta ];
   gammabef := [ g : g in gamma ];
   
   c := KT.1;
   cold := KT.1;
   Kc := KT;
   kc := PolynomialRing(k);
   y := KTy.1;

   require DefiningPolynomial(E) eq y^2 + c*y + c^3 + a*c^2 + b : 
     "Defining Polynomial must be of the form y^2 + x*y + x^3 + a*x^2 + b";

   // Mipo on b 
   ff2 := GF(2);
   ff2sig := PolynomialRing(ff2);
   sig := ff2sig.1;
   l := [b];
   i := 0;

   repeat
      i := i + 1;
      Append(~l, b^(q^i));
      M := [ Eltseq(x, ff2) : x in l ];
      M := Matrix(M);
      M := BasisMatrix(Kernel(M));
   until Nrows(M) gt 0;
   
   f_mipo := ff2sig!Eltseq(M[1]);
   
   if IsZero(Evaluate(f_mipo, 1)) then
      f_ev := f_mipo;
   else
      f_ev := f_mipo * (sig + 1);
   end if;
   
   assert (sig^n + 1) mod f_ev eq 0;
   h := (sig^n + 1) div f_ev;
   m := Degree(f_ev);

   vprintf WeilRes : "f_mipo is %o\n", f_mipo;
   vprintf WeilRes : "f_ev is %o\n", f_ev;
   vprintf WeilRes : "h is %o\n", h;

   // v := f_ev(sig)s_0
   l := Eltseq(f_ev);
   v := K!0;
   for i in [0 .. Degree(f_ev)] do
      if not IsZero(l[i + 1]) then
         if i gt 0 then
            v +:= alpha[i];
         else
            v +:= a;
         end if;
      end if;
   end for;

   v := Factorization(KT.1^2 + KT.1 + v);
   assert #v eq 2;
   v := Evaluate(v[1][1], 0);

   vprintf WeilRes : "v is \t%o\n", v;

   // vv := h(sig)v
   l := Eltseq(h);
   vv := K!0;
   for i in [0 .. Degree(h)] do
      if not IsZero(l[i + 1]) then
         vv +:= v^(q^i);
      end if;
   end for;

   vprintf WeilRes : "vv is \t%o\n", vv;

   if not IsZero(vv) then
      if IsZero(Evaluate(h, 1)) then
         error "No Weil restriction possible";
      end if;
      vprintf WeilRes : "v -> v + 1\n";
      v +:= 1;
   end if;

   // Frobenius operation on k-space of dim m+n
   Sig := Identity(MatrixAlgebra(k, m));
   Sig := Sig[2 .. m];
   Sig := [ Eltseq(Sig[i]) : i in [1 .. #Sig] ];
   Sig := [ Sig[i] cat z : i in [1 .. #Sig] ]
          where z is [ 0 : i in [1 .. n] ];        
   tmp := Eltseq(PolynomialRing(k)!f_ev)[1 .. m] cat Eltseq(v, k);
   Append(~Sig, tmp);
   tmp := [ z cat Eltseq(Generator(K, k)^((i - 1)*q), k) : i in [1 .. n] ]
          where z is [ 0 : i in [1 .. m] ];
   Sig := Sig cat tmp;
   
   Sig := Matrix(Sig);
   assert IsOne(Sig^n);

   // lemma 3
   // we will have M (s_0 + s_1, ..., s_0 + s_(n-1))^t = (t_1, ..., t_(n-1))^t
   // we have delta[i] = 0 iff i > m-1.
   // reminder: c equals t_(m-1) at the end

   vprintf WeilRes : "delta before is %o\n", delta;

   m := 1;
   M := Identity(MatrixRing(K, n - 1));

   for i in [1 .. n - 1] do
      for j in [1 .. i - 1] do
         if not IsZero(delta[j]) then
            M[i] +:= (delta[i]/delta[j])^qnp * M[j];
            gamma[i] := delta[i]/delta[j] * gamma[j] + gamma[i];
            delta[i] := delta[i]/delta[j] + (delta[i]/delta[j])^qnp;
         end if;
      end for;
      if not IsZero(delta[i]) then
         m +:= 1;
      end if;
   end for;
   
   assert ISA(Type(M), MtrxSpcElt);
   assert m eq Degree(f_ev);
   
   z := c;
   for i in [1 .. n - 1] do
      if not IsZero(delta[i]) then
         z := Evaluate(z, ((c^2 + c) - gamma[i]) / delta[i]);
      end if;
   end for;
   zold := z;

   vprintf WeilRes : "delta after is %o\n", delta;
   vprintf WeilRes : "m is %o\n", m;
   vprintf WeilRes : "z is %o\n", z;

   // create F:  x = 1/z. z = z(c). This relation is non rational
   F := FunctionField(z^3*y^2 + z^2*y + 1 + a*z + b*z^3: Check := false);

   // find original X, Y etc.
   c := F!BaseRing(F).1;
   z := Evaluate(z, c);
   X := 1/z;
   Y := F.1;
   
   assert IsZero(Y^2 + X*Y + X^3 + a*X^2 + b);

   vv := [];
   for i in [1 .. n] do 
      Sig1 := Sig^(i - 1);  // opti
      Sig1 := Sig1[1];
      Sig1 := Eltseq(Sig1)[m + 1 .. n + m];
      Append(~vv, Sig1);
   end for;
   
   vv := [ &+ [ (K!x[i]) * Generator(K, k)^(i - 1) : i in [1 .. n] ] 
           : x in vv[2 .. n] ];

   vv := Transpose(Matrix(K, [vv]));
   t := Eltseq(Transpose(M*vv)[1]);
   
   for i in [m .. n - 1] do
      assert IsZero(Evaluate(KT.1^2 + KT.1 + gamma[i], t[i]));
   end for;

   ChangeUniverse(~t, Parent(c));
   if m gt 1 then
      t[m - 1] := c;
      for i := m - 2 to 1 by -1 do
         t[i] := (t[i + 1]^2 + t[i + 1] - gamma[i + 1]) / delta[i + 1];
      end for;
   end if;
   
   ss := Matrix(1,  #t, t) * (MatrixAlgebra(Parent(c), n - 1)!Transpose(M)^-1); // opti
   ss := Eltseq(ss);
   
   vprintf WeilRes : "t is %o\n", t;
   vprintf WeilRes : "ss is %o\n", ss;

   for i := 1 to n - 1  do
      assert IsZero(ss[i]^2 + ss[i] + gammabef[i] + deltabef[i]*z);
   end for;

   s := [ (Y + beta[1]^qnp) / X + 0*Y ];
   for i := 2 to n do
      Append(~s, ss[i - 1] + s[1] + 0*Y);
   end for;

   YY := [ X*s[i] + beta[i]^qnp : i in [1 .. n] ];
   for i := 1 to n do
      assert IsZero(YY[i]^2 + X*YY[i] + X^3 + a^(q^(i-1))*X^2 + b^(q^(i-1)));
   end for;  // opti takes very long

   // get the frobenius conjugates of c
   sigma := Sym(n).1;
   cc := [];
   if m gt 1 then
      for i := 1 to n do 
         for j := 2 to n do
            ss[j - 1] := s[1^(sigma^(i-1))] + s[j^(sigma^(i-1))];
         end for;
         v := [ u^(q^(i-1)) : u in Eltseq( M[m-1] ) ];
         v := Matrix(K, #v, 1, v);
         Append(~cc, F!((Matrix(F, 1, #ss, ss) * 
                      KMatrixSpace(F, Nrows(v), Ncols(v))!v)[1][1]));
      end for;
   else
      cc := [c : i in [1 .. n]];
   end if;  // opti takes longest

   for i := 1 to n do
      tmp := Kc![u^(q^(i-1)) : u in Eltseq(zold)];
      tmp := Evaluate(tmp, cc[i]) - zold;
      assert IsZero(tmp);
   end for;

   vprintf WeilRes : "YY is %o\n", YY;
   vprintf WeilRes : "cc is %o\n", cc;

   // trace Y and c
   // get fixed variable of c

   if n mod 2 eq 0 then
      mu := Generator(K);
      while IsZero(Trace(mu, k)) do
         mu *:= Generator(K);
      end while;
      mu := mu / K!Trace(mu, k);
   else
      mu := K!1;
   end if;

   lam0 := Evaluate(Derivative(zold), 0);
   Yfix := &+ [ mu^(q^(i-1))*YY[i] : i in [1 .. n] ];
   cfix := &+ [ (mu*lam0)^(q^(i-1))*cc[i] : i in [1 .. n] ];

// print "cfix = ", cfix;
// print "lam0 = ", lam0;
// print "cc = ", cc;
   lamss := cfix - lam0*cc[1];
// print "lamss = ", lamss;
   //time is_const, lamss := IsConstant(lamss); // opti very long
   is_const, lamss := IsConstant(lamss); // opti very long
   assert is_const;
// print "lamss = ", lamss;
   
   zincfix := kc!Evaluate(zold, (cold - lamss) / lam0);

   vprintf WeilRes : "Yfix is %o\n", Yfix;
   vprintf WeilRes : "cfix is %o\n", cfix;
   vprintf WeilRes : "z in cfix is %o\n", zincfix;

   if n mod 2 eq 0 then
      // do nothing here
   else
      assert IsZero(Yfix^2 + X*Yfix + X^3 + K!Trace(a, k)*X^2 + K!Trace(b, k));
   end if;

   // get rational equation in Yfix and cfix
   f := Eltseq(MinimalPolynomial(Yfix));
//print "f = ", f;
    f := [FieldOfFractions(Kc)!g : g in f];
   lcm := LCM( [ Denominator(g) : g in f ] );
//print "f = ", f;
   f := [ Kc!(lcm*g) : g in f ];
   assert #f ge 3; 
// print "f = ", f;
//print "cold = ", cold;
// print "lamss = ", lamss;
//print "lam0 = ", lam0;
   f := [ Evaluate(p, (cold - lamss) / lam0) : p in f ];
   
// print "f = ", f;
   f :=  [ g / LeadingCoefficient(f[#f]) : g in f ];

   assert ConstantField(F) eq K;
// print "f = ", f;
//print "cfix = ", cfix;
//print "Yfix = ", Numerator(Yfix, MaximalOrderFinite(Parent(Yfix)));
//print "Yfix = ", Denominator(Yfix, MaximalOrderFinite(Parent(Yfix)));
//Parent(Yfix):Minimal;
   assert IsZero( &+ [ Evaluate(Kc!f[i + 1], cfix)*Yfix^i : i in [0 .. 2] ] );

   ChangeUniverse(~f, kc);
   kcy := PolynomialRing(kc);

   f := kcy!f;
   Fs := FunctionField(f: Check := false);

   vprintf WeilRes : 
     "\nUnreduced hyperelliptic field is %o of genus %o\n\n", Fs, Genus(Fs);

   Ys := Fs.1;

   map := function(pl)

      vprintf WeilRes : "Map place to F\n";

      // Some checks
      
      if Type(pl) ne PlcFunElt then
         error "Runtime error: Function field place expected";
      end if;
      
      if FunctionField(pl) ne E then
         error "Runtime error: Place belongs to the wrong function field";
      end if;
      
      if Degree(pl) gt 1 then
         error "Runtime error: Place must have degree one";
      end if;
      
      // first to F
      yp := Evaluate(E.1, pl);
      xp := Evaluate(E!BaseRing(E).1, pl);

      if xp cmpeq Infinity() or IsZero(xp) then 
         error 
        "Runtime error: Cannot map zeros or poles of generator of base ring";
      end if;
      
      P1 := Gcd(Numerator(Divisor(Y + yp)), Numerator(Divisor(X + xp)));
      assert Degree(P1) eq 2^(m - 1);
      P1 := Support(P1);

      vprintf WeilRes : "Length of P1 is %o\n", #P1;

      D := DivisorGroup(Fs)!0;
// DFF<d> := FunctionField(D);
      for p in P1 do

         vprintf WeilRes : "Map place to F'\n";

         yp := Evaluate(Yfix, p);
         cp := Evaluate(cfix, p);
         fp := MinimalPolynomial(cp, k);

         if Degree(fp) gt 1 then
            kp := ext<k | fp>;
/* print "min poly   ", MinimalPolynomial(cp, k); */
/* print "defin poly ", DefiningPolynomial(kp, k); */
/* print "prime min poly   ", MinimalPolynomial(cp, PrimeField(k)); */
/* print "prime defin poly ", DefiningPolynomial(kp, PrimeField(k)); */
            EmbedOverSubRing(kp, Parent(cp), GroundField(kp), cp);
            assert Parent(cp)!Generator(kp, k) eq cp;
         else
            kp := k;
         end if;

         yp := MinimalPolynomial(yp, kp);
/* print "yp = ", yp; */
         yp := Eltseq(yp);
/* print "yp = ", yp; */
         yp := [ kc!Eltseq(a, k) : a in yp ];
/* print "yp = ", yp; */
/* print "Ys = ", Ys; */
/* T<t> := Parent(MinimalPolynomial(Ys)); */
/* R<r> := CoefficientRing(T); */
/* Z<z> := ConstantField(R); */
/* print "min_poly(Ys) = ", MinimalPolynomial(Ys); */
/* print "Parent(Ys) = ", Parent(Ys); */
/* MinimalPolynomial(Ys)*Denominator(TrailingCoefficient(MinimalPolynomial(Ys))); */
         yp := &+ [ yp[i]*Ys^(i - 1) : i in [1 .. #yp] ];
/* print "yp = ", yp; */
/* print "num(yp) = ", Numerator(yp, MaximalOrderFinite(Parent(yp))); */
/* print "den(yp) = ", Denominator(yp, MaximalOrderFinite(Parent(yp))); */
                       
/* print "Num(Div(yp)) = ", Support(Numerator(Divisor(yp))); */
/* print "Num(Div(fp)) = ", Support(Numerator(Divisor(Fs!fp))); */
         pp := Gcd(Numerator(Divisor(yp)), Numerator(Divisor(Fs!fp)));
         
         assert #Support(pp) eq 1;
         assert (n*Degree(p)) mod Degree(pp) eq 0;
         
/* print "pp = ", pp; */
/* print "p = ", p; */
/* print "D = ", Support(D); */
         D +:= ((n*Degree(p)) div Degree(pp)) * pp;
/* print "D = ", Support(D); */

      end for;

      assert Degree(D) eq n*2^(m - 1);
      
      return D;
      
   end function;
      
   // skip reduction
   if not Reduction then
      return Fs, map;
   end if;
      
   F, rmap := HyperEllipticReduce(Fs);

    comb_map := function(pl)
	D := map(pl);
	return rmap(D);
    end function;
      
   return F, comb_map;
      
end intrinsic;

///////////////////////////////////////////////////////////////////////////

HyperEllipticReduce := function(F)
//  Performs some coefficient reduction for hyperelliptic alffs
//  over finite fields. Maps also divisors over.
//  The method may unfortunately not work well for large examples ...

    K := ConstantField(F);
    KT := PolynomialRing(K);
    T := KT.1;
    KTy := PolynomialRing(KT);
    y := KTy.1;

    p := Poles(BaseRing(F).1)[1];
    DT := DecompositionType(F, p);
    if DT ne [<1, 2>] then
	D := Support(DifferentDivisor(F));
	// there is always a ramified place of degree one, hopefully ...
	D := [x : x in D | Degree(x) eq 1];
	if #D gt 0 then
	    Sort(~D);
	    P := D[1];
	else
	    if #DT ne 2 then
		_, P := HasPlace(F, 1);
		if not assigned P then
		    error "Could not find a place of degree one";
		end if;
	    end if;
	end if;
	// push the rational point P to infty
	if assigned P then 
	    min := T - Evaluate(Min(P), 0);
	    f := DefiningPolynomial(EquationOrderFinite(F));
	    // opposite order to kash
            f := [Evaluate(KT!x, min) : x in Eltseq(f)];
            f := [Evaluate(KT!x, 1/T) : x in f];
	    lcm := Lcm([Denominator(x) : x in f]);
	    // coerce explicitly just to be sure!!
	    f := [x*Universe(f)!lcm : x in f];
	    // no need to swap back since still in magma order
// print "f = ", f;
// print "F = ", F;
// print "PPB(F) = ", KTy;
	    f := KTy!f;
// print "f = ", f;
	    G := FunctionField(f : Check := false);
	    Y := G.1;

	    map1 := function(D)
	        // DD := List(AlffDivisorIdeals(D), x->AlffIdealBasis(x^-1)); 
		id1, id2 := Ideals(D);
		DD := [Basis(id1^-1), Basis(id2^-1)];
		
		EOF := EquationOrderFinite(F);
		// DD := List(DD, x->List(x, y->AlffEltMove(y,
		//	      AlffOrderEqFinite(F))));
		// DD := List(DD, x->List(x, y->AlffEltToList(y)));
		DDN := [[Eltseq(Numerator(y, EOF)) : y in x] : x in DD];
		DDD := [[Denominator(y, EOF) : y in x] : x in DD];

		//DD := List(DD, x->List(x, y->List(y[1], z->Eval(Eval(z, min) +
		//               0*AlffVarT(F), 1/AlffVarT(F))) /
		//               Eval(Eval(y[2], min) + 0*AlffVarT(F),
		//                    1/AlffVarT(F)) ));
		DDN := [[[Evaluate(z, min) : z in y] : y in x] : x in DDN];
		DDN := [[[Evaluate(KT!z, 1/T) : z in y] : y in x] : x in DDN];

		DDD := [[Evaluate(z, min) : z in x] : x in DDD];
		DDD := [[Evaluate(KT!z, 1/T) : z in x] : x in DDD];

		DD := [[[n/DDD[j][i] : n in DDN[j][i]] : i in [1 .. #DDN[j]]] 
							: j in [1 .. #DDN]];

		// DD := List(DD, x->List(x, y->Sum([1..Length(y)],
		//               i->y[i]*Y^(i-1))));
		DD := [[&+[y[i]*Y^(i - 1) : i in [1 .. #y]] : y in x] : x in DD];

		// DG := AlffDivisor(Sum(DD[1], x->AlffEltMove(x,
		//                AlffOrderMaxFinite(G))*AlffOrderMaxFinite(G)),
		//                Sum(DD[1], x->AlffEltMove(x,
		//                 AlffOrderMaxInfty(G))*AlffOrderMaxInfty(G)));
		MOF := MaximalOrderFinite(G);
		id1 := [Numerator(y, MOF)/MOF!Denominator(y, MOF) : y in DD[1]];
		id1 := &+[y*MOF : y in id1];
		MOI := MaximalOrderInfinite(G);
		id2 := [Numerator(y, MOI)/MOI!Denominator(y, MOI) : y in DD[1]];
		id2 := &+[y*MOI : y in id2];
		DG := Divisor(id1, id2);

		Px := Decomposition(G, Zeros(G!BaseRing(G).1));
		for P in Px do
		    DG -:= Valuation(DG, P)*P + Minimum([Valuation(y, P) : y in DD[2]])*P;
		end for;
// print "DG = ", DG, "\n";

		assert Degree(D) eq Degree(DG);

		return DG;
	    end function;

	    F := G;

	end if;
    end if;

    if not assigned map1 then
	map1 := function(D)
	    return D;
	end function;
    end if;

    // infty := Filtered(AlffPlaceSplit(F, 1/AlffVarT(F)), x->AlffPlaceDeg(x)=1)
    p := Poles(BaseRing(F).1)[1];
    infty := Decomposition(F, p);
    infty := [x : x in infty | Degree(x) eq 1];

    // Sort(infty, LessEqual);
    Sort(~infty);
    infty := infty[1];
    r := 1;
    while Degree(MinimalPolynomial(Reverse(Basis(r*infty))[1])) lt 2 do
	r +:= 1;
    end while;

    EOF := EquationOrderFinite(F);

    // a := AlffEltMove(Reversed(AlffDivisorLBasis(r*infty))[1],
    //              AlffOrderEqFinite(F));
    a := Reverse(Basis(r*infty))[1];
    a := Numerator(a, EOF)/Denominator(a, EOF);

    // T := List([1..AlffDeg(F)], i->AlffEltToList(a^(i-1)));
    T := [a^i : i in [0 .. Degree(F) - 1]];
    TN := [Eltseq(Numerator(x, EOF)) : x in T];
    TD := [Denominator(x, EOF) : x in T];

    // T := List(T, a->a[1]/a[2]);
    T := [[TN[i][j]/TD[i] : j in [1 .. #TN[i]]] : i in [1 .. #TN]];

    T := Matrix(T);
    T := T^-1;
    G := FunctionField(MinimalPolynomial(a) : Check := false);

    map2 := function(D)
// DFF<d> := FunctionField(D);
// print "D = ", Support(D);
	// DG := List(AlffDivisorIdeals(D), x->AlffIdealBasis(x^-1));
	id1, id2 := Ideals(D);
// print "id1 = ", id1;
// print "id1^-1 = ", id1^-1;
// print "id2 = ", id2;
// print "id2^-1 = ", id2^-1;
	// Ideals of a divisor in magma are the inverse
	// of the ideals in kash
	DG := [Basis(id1), Basis(id2)];

	// DG := List(DG, x->List(x, y->AlffEltMove(y, AlffOrderEqFinite(F))));
	// DG := List(DG, x->List(x, y->AlffEltToList(y)));
	// DG := List(DG, x->List(x, y->y[1]/y[2]));
	DGN := [[Eltseq(Numerator(y, EOF)) : y in x] : x in DG];
	DGD := [[Denominator(y, EOF) : y in x] : x in DG];
	DG := [[[n/DGD[j][i] : n in DGN[j][i]] : i in [1 .. #DGN[j]]] 
							: j in [1 .. #DGN]];
// print "DG = ", DG;
	// DG := List(DG, x->List(x, y->ListApplyMatAdd(y, T)));
	DG := [[Matrix(1, #y, y) : y in x] : x in DG];
	DG := [[y*T : y in x] : x in DG];

	// DG := List(DG, x->List(x, y->AlffElt(AlffOrderEqFinite(G), y)));
	// matrix to sequence for coercion back to element
	DG := [[Eltseq(y) : y in x] : x in DG];
	DG := [[G!y : y in x] : x in DG];

	// DG := List(DG, x->List(x, y->AlffElt(AlffOrderEqFinite(G), y)));
	EOG := EquationOrderFinite(G);
	DGN := [[Numerator(y, EOG) : y in x] : x in DG];
	DGD := [[Denominator(y, EOG) : y in x] : x in DG];
	DG := [[DGN[j][i]/DGD[j][i] : i in [1 .. #DGN[j]]] : j in [1 .. #DGN]];
// print "DG = ", DG;

	// DG[1] := List(DG[1], y->AlffEltMove(y, AlffOrderMaxFinite(G)));
	MOF := MaximalOrderFinite(G);
	DN1 := [Numerator(y, MOF) : y in DG[1]];
	DD1 := [Denominator(y, MOF) : y in DG[1]];

	// DG[2] := List(DG[2], y->AlffEltMove(y, AlffOrderMaxInfty(G)));
	MOI := MaximalOrderInfinite(G);
	DN2 := [Numerator(y, MOI) : y in DG[2]];
	DD2 := [Denominator(y, MOI) : y in DG[2]];
	DG1 := [DN1[i]/DD2[i] : i in [1 .. #DN1]];
	DG2 := [DN2[i]/DD2[i] : i in [1 .. #DN2]];

// print "DG1 = ", DG1;
	// DG := List(DG, x->Sum(x, y->y*AlffEltOrder(y)));
	DG1 := &+[y*MOF : y in DG1];
	DG2 := &+[y*MOI : y in DG2];
// print "DG1 = ", DG1;
// print "DG2 = ", DG2;

	// DG should have two ideals by now
	DG := Divisor(DG1, DG2);
	S := Support(DG);
// print "Deg(D) = ", Degree(D);
// print "Deg(DG) = ", Degree(DG);
// print "DG = ", DG;
// print "S = ", S;
	assert Degree(D) eq Degree(DG);

	return DG;
    end function;

    map := function(D)
	D := map1(D);
	return map2(D);
    end function;

    return G, map;
end function;
