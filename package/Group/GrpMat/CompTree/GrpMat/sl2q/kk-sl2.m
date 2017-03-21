freeze;

// Peter Brooksbank's implementation of the algorithm by Kantor-Kassabov
// to recognize (P)SL(2,2^a).
// Modified by Csaba Schneider.

/* h is an element of GL(2,2^e) of odd order */
__square_root := function (h)
     K := BaseRing (Parent (h));
     a := h[1][1]; b := h[1][2]; c := h[2][1]; d := h[2][2];
     assert ((a + d) ne 0);
     sqrt_h := [ 
          [ SquareRoot (a) + SquareRoot (b*c/(a+d)) , b / SquareRoot (a+d) ],
	  [ c/SquareRoot (a+d) , SquareRoot (d) + SquareRoot (b*c/(a+d)) ] 
               ];
     sqrt_h := Generic (Parent (h))!Matrix (sqrt_h);
     assert sqrt_h^2 eq h;
return sqrt_h;  
end function;

/* g is an element of SL(2,2^e) and u = [ 1 0 ] */
/*                                      [ 1 1 ] */
__bold_B_matrix := function (g, u)
     v := __square_root (u * u^g) * g^-1;
     assert (u, v) eq Identity (Parent (g));
return v;
end function;

/* g is an element of a black box SL(2,2^e) and u is an involution */
// modified by csaba to return slp

__bold_B := function (g, wg, u, wu, k)
    v := (u * u^g)^(-k) * g^-1;
    wv := (wu*wu^wg)^-k*wg^-1;
    assert (u, v) eq Identity (Parent (g));
    // *****

    return v, wv;
end function;
    
    // modified by csaba to return SLP
    
__frak_b := function (x, wx, u, wu, r, wr, k)
        
    return (u * u^r)^(k+1) * (u^r * x)^(k+1), 
           (wu * wu^wr)^(k+1) * (wu^wr * wx)^(k+1);
               
end function;



/* find element of order 3 */
/* modified by csaba to return also the slp to the element */
                                 
__element_of_order_3 := function (G)
     found := false;
     count := 0;
     LIMIT := 100;
     
     P := RandomProcessWithWords( G );
     while (not found) and (count lt LIMIT) do
         count +:= 1;
         g, w := Random (P);
         o := Order (g);
         if (o mod 3) eq 0 then
            found := true;
            h0 := g^(o div 3); w := w^(o div 3);
         end if;
     end while;
     if not found then
         "did not find an element of order 3 in", LIMIT, "tries";
         return false, _;
     end if;
     //"found element of order 3 after", count, "tries.";
     assert Evaluate( w, GeneratorsSequence( G )) eq h0;
return true, h0, w;
end function;


/* find r, u, and subgroup isomorphic to PGL(2,2) */
/* modified by csaba to return slps */
                                 
BuildPGL22 := function (G, q, k)
        
     W := WordGroup( G );
     found, h0, wh0 := __element_of_order_3 (G);
     if not found then return false, _, _; end if;

     tt := Cputime ();
     S := GeneratorsSequence( G );

     if (q + 1) mod 3 eq 0 then

         assert exists (i){ i : i in [1..#S] | not h0^S[i] in { h0 , h0^2 } };
         g := S[i]; wg := W.i;   
                 
     else

         easy := exists (i){ i : i in [1..#S] | (h0, h0^S[i])^2 
                         ne Identity (G) };
         if easy then
             g := S[i]; wg := W.i;
         else
            "hard";
            assert exists (x,y){ <s,t> : s in [1..#S], t in [1..#S] | 
                    ((h0, h0^S[s]), (h0, h0^S[t])) 
                    ne Identity (G) };
            g := S[x] * S[y]; wg := W.x*W.y;
        end if; 

     end if;

     assert (h0, h0^g)^2 ne Identity (G);

     rp := (h0 * h0^g)^k * h0;
     wrp := (wh0*wh0^wg)^k*wh0;
     assert (Order (rp) eq 2) and (h0^rp eq h0^g);

     rm := (h0 * (h0^-1)^g)^k * h0;
     wrm := (wh0*(wh0^-1)^wg)^k*wh0;
     assert (Order (rm) eq 2) and (h0^rm eq (h0^-1)^g);

     r := rp * rm;
     wr := wrp*wrm;
     u := r * h0;
     wu := wr*wh0;
     assert #sub < G | [r,u] > eq 6;

//"constructed PGL(2,2) in time", Cputime (tt);
return true, r, wr, u, wu;
end function;



/* product of two black box field elements */
__product := function (x, y)
     if (x cmpeq 0) or (y cmpeq 0) then
         return 0;
     else 
         return x*y;
     end if;
end function;

/* sum of two black box field elements */
__sum := function (x, y, u, r, k)
    
    // trivial word to feed as dummy argument
    w0 := One( SLPGroup( 1 ));
    
     if x cmpeq 0 then 
         return y;
     elif y cmpeq 0 then
         return x;
     else
        v := u^x * u^y;
        if v eq Identity (Parent (u)) then
            return 0;
        else
            return __frak_b (u^x * u^y, w0, u, w0, r, w0, k);
        end if;
     end if;
end function;

/* the trace of a black box field element */
__trace := function (t, u, e)
     w := &* [ u^(t^(2^i)) : i in [0..e-1] ];
     if w eq Identity (Parent (u)) then
         return 0;
     else
         assert w eq u;
         return 1;
     end if;
end function;

/* write a given black field element as GF(2)-linear combination of a standard basis */
__linear_combination := function (t, s, u, e)
     traces := [ __trace (s^l, u, e) : l in [0..2*e-2] ];
     ts_traces := [ ];
     A := MatrixAlgebra (GF (2), e)!0;
     for j in [0..e-1] do
	 Append (~ts_traces, __trace (t*s^j, u, e));
         for i in [0..e-1] do
            A[i+1][j+1] := traces[1 + i + j];
	 end for;
     end for;
     sol := Vector (GF (2), ts_traces) * A^-1;
return [ Integers ()!sol[i] : i in [1..Degree (sol)] ];
end function;


/* 
   C is a of coefficients for a polynomial f;
   return the list of coefficients for the polynomial (a + bx) * f
*/
__update := function (C, a, b, u, r, k)
     D := [* 0 : i in [1..#C+1] *];
     D[1] := __product (a, C[1]);
     D[#D] := __product (b, C[#C]);
     for i in [2..#C] do
         x := __product (a, C[i]);
         y := __product (b, C[i-1]);
         D[i] := __sum (x, y, u, r, k);
     end for;
return D;
end function;

__degree := function (f, e)
     m := 1;
     while f^(2^m) ne f and m le e do
         m +:= 1;
     end while;
assert f^(2^m) eq f;
return m;
end function;


/*
   Find the minimal polynomial over GF(2) of a given element 
   sU of the black box field B/U.
*/ 
MinimalPolynomialOfBlackBoxFieldElement := function (R, f, u, r, k, e)

     // find the degree of the smallest field in which s lives
     m := __degree (f, e);

     // find the coefficients as black box field elements
     C := [* f^(2^(m-1)) , Identity (Parent (u)) *];
     for i in [0..m-2] do
         C := __update (C, f^(2^i), Identity (Parent (u)), u, r, k);
     end for;
     assert #C eq (m+1);

     // convert to a polynomial over GF(2)
     c := [ 0 : i in [1..m+1] ];
     for i in [1..m+1] do
         if not C[i] cmpeq 0 then
	    assert C[i] eq Identity (Parent (u));
            c[i] := 1;
         end if;
     end for;
     
return R!c;
end function;


/* construct a generator (and its min poly) for the black box field B/U */
BuildBlackBoxField := function (G, u, uw, r, rw, k, e)

    S := GeneratorsSequence( G );
    W := SLPGroup( 2 ); x := W.1; y := W.2;
    // build a list of 6 words representing the elements of L
    Lwords := {@ One( W ), x*y, (x*y)^2, x, x*y*x, (x*y)^2*x @};
    L := {@ Evaluate( w, [u, r] ) : w in Lwords @}; 
    
    // now we substitute the slps for u and r to obtain slps in 
    // the original generators of G
    Lwords := {@ Evaluate( w, [uw,rw] ) : w in Lwords @};

    // redifine W to be SLPGroup
    W := WordGroup( G );
  
     tt := Cputime ();
     Fgens := [ ];
     for s in [1..#S] do
         for a in [1..6] do
             for b in [1..6] do
		 g := L[a] * S[s] * L[b];
                 gw := Lwords[a]*W.s*Lwords[b];
                 assert Evaluate( Lwords[a], S ) eq L[a];
                 if (u * u^g)^2 ne Identity (G) then
		       x, xw := __bold_B (g, gw, u, uw, k);
  		     assert (x, u) eq Identity (G);
                     if not x eq Identity (G) then
		         h, hw := __frak_b (x, xw, u, uw, r, rw, k);
                         Append (~Fgens, <h,hw>);
                     end if;
                 end if;
	     end for;
         end for;
     end for;
//    "constructed black box field in time", Cputime (tt); 

     tt := Cputime ();
     Fgens := Set (Fgens);
     Fgens := [ f : f in Fgens ];
     degs := [ __degree (Fgens[i][1], e) : i in [1..#Fgens] ]; 

     if exists (l){ a : a in [1..#Fgens] | degs[a] eq e } then
         s := Fgens[l][1];
     else
         "   (no immediate field generator)";
         fac := Factorisation (e);
         Q := [ fac[i][1]^fac[i][2] : i in [1..#fac] ];
         s := Identity (G);
         for i in [1..#Q] do
            qi := Q[i];
            assert exists (li){ a : a in [1..#Fgens] | degs[a] mod qi eq 0 };
            mi := degs[li];
	    "   (not implemented yet)";
	end for;
     end if;

     R := PolynomialRing (GF (2));
     min_s := MinimalPolynomialOfBlackBoxFieldElement (R, s, u, r, k, e);
     assert Degree (min_s) eq e;
//     "found generator of black box field in time", Cputime (tt);

 return s, Fgens[l][2], min_s;
 end function;


//   standard generators are [ 1 0 ] , [ 0 1 ] , [ xi  0  ] 
//                           [ 1 1 ]   [ 1 0 ]   [ 0 1/xi ]   


/*
   write an SLP from standard generators to [ 1  0 ] 
                                            [ mu 1 ]

   here V is GF(q) as a GF(2)-space, with basis [ 1 , xi^2 , ... , xi^(2(e-1)) ],
   and X is an SLPGroup on 3 generators.
*/
__construct_transvection := function (mu, V, phi, X)
     c := Coordinates (V, mu @ phi);
     c := [ Integers ()!(c[i]) : i in [1..#c] ];
     slp := &* [ ((X.1)^((X.3)^(i-1)))^(c[i]) : i in [1..#c] ];
return slp;
end function;

/*
   write an SLP from standard generators to a given M in SL(2,q)
*/
__natural_rewrite := function (M, gens, K : EVAL := false)
  
     mat := M;
     _, _, e := IsPrimePower( #K );
     xi := K.1;
     V, phi := VectorSpace (K, GF (2), [ xi^(2*i) : i in [0..e-1] ] );
     X := SLPGroup (3);
     

     // make sure that M[2][2] is nonzero
     if mat[2][2] eq 0 then
         mat := mat * Generic (Parent (M))![1,1,0,1];
         slp := (X.1)^(X.2);
     else 
         slp := Identity (X);
     end if;

     // reduce to upper triangular
     mu := - mat[2][1] / mat[2][2];
     mat := mat * Generic (Parent (M))![1,0,mu,1];
     slp := slp * __construct_transvection (mu, V, phi, X);

     // reduce to diagonal
     mu := - mat[1][2] / mat[1][1];
     mat := mat * Generic (Parent (M))![1,mu,0,1];
     lslp := __construct_transvection (mu, V, phi, X);
     slp := slp * lslp^(X.2);

     // write SLP to the diagonal element
     mu := mat[1][1];
     lslp := __construct_transvection (1/mu, V, phi, X);
     dslp := lslp * __construct_transvection (mu, V, phi, X)^(X.2) * 
             lslp * (X.2);

     // construct the final SLP and decide what to do with it
     slp := dslp * slp^-1;
     if EVAL then
         return Evaluate (slp, gens );
     else
         return slp;
     end if;

end function;


__hat := function (g, gens, K )

     u := gens[1];
     r := gens[2];
     s := gens[3];
     q := #K;
     k := (q^2-2) div 2;
     _, _, e := IsPrimePower( q );

     // some functions require SLP argument; we pass a trivial one
     w0 := One( SLPGroup( 1 ));

     L := [ g , g*r , r*g , r*g*r ];
     undef := [ i : i in [1..4] | (u * u^L[i])^2 eq Identity (Parent (u)) ];
     zero := [ i : i in {1..4} diff Set (undef) | L[i]^2 eq Identity (Parent (u)) ];

     if (#undef eq 0) and (#zero eq 0) then   // A, B, C, D all defined and nonzero
			//"case 1";

         field_elts := [ ];
         for i in [1..4] do
              ui := __bold_B (L[i], w0, u, w0, k);
              if ui eq u^0 then
                  Append (~field_elts, K!1);
	      else
   	          ti := __frak_b (ui, w0, u, w0, r, w0, k)^2;
                  lc := __linear_combination (ti, s, u, e);
                  Append (~field_elts, K!lc + 1);
              end if;
         end for;


         A := field_elts[1]; 
         B := field_elts[2];
         C := field_elts[3];
         D := field_elts[4];

         Del := SquareRoot (A*D*(B+C)*(A+B+C+D));

         a := A*C*D / Del;
         b := D*(B+C) / Del;
         c := A*(B+C) / Del;
         d := A*B*D / Del;

         return SL (2, K)![ a, b , c , d ];

     end if;

     if #undef eq 1 then
         //"case 2";

         // make A the undefined element
         if undef[1] eq 1 then
             h := g;
         elif undef[1] eq 4 then
             h := r * g * r;
         elif undef[1] eq 2 then
             h := g * r;
         else 
             h := r * g;
         end if;
         assert (u * u^h)^2 eq Identity (Parent (u));

         L := [ h*r , r*h , r*h*r ];

         field_elts := [ ];
         for i in [1..3] do
	     ui := __bold_B (L[i], w0, u, w0, k);
             if ui eq u^0 then
                 Append (~field_elts, K!1);
             else
                 ti := __frak_b (ui, w0, u, w0, r, w0, k)^2;
                 lc := __linear_combination (ti, s, u, e);
                 Append (~field_elts, K!lc + 1);
             end if;
	 end for;

         B := field_elts[1];
         C := field_elts[2];
         D := field_elts[3];

         if (B*C eq 0) then

	     "not implemented yet";
             return 0;

         else

  	     Del := SquareRoot (B*C);
             aa := C / Del;
             bb := 0;
             cc := B*C / Del;
             dd := B / Del;
             // make necessary correction
             if undef[1] eq 1 then
                 a := aa; b := bb; c := cc; d := dd;
             elif undef[1] eq 4 then
                 a := dd; b := cc; c := bb; d := aa;
             elif undef[1] eq 2 then
                 a := bb; b := aa; c := dd; d := cc;
	     else
	         a := cc; b := dd; c := aa; d := bb;
             end if;

             return SL (2, K)![ a , b , c , d ];

        end if;

     end if;

     if #undef eq 2 then
	       // print "case 3";

         h := g * u;
         hhat := $$ (h, gens, K);

         return hhat * SL (2, K)![1,0,1,1];

     end if;


     if (#undef eq 0) and (#zero gt 0) then 
			//"case 4";

         h := g * s;
         hhat := $$ (h, gens, K);

         return hhat * SL (2, K)![K.1^-1,0,0,K.1];

     end if;

end function;


/*
   write an SLP from images of standard generators to a given g in G
*/
__black_box_rewrite := function (g, gens, K : EVAL := false)

     /*
        preimage of g has the form [ a b ] ... find this matrix
                                   [ c d ]
     */
  Embed( K, GF( #K ));
     ghat := __hat (g, gens, K );

     // write an SLP to ghat

     if EVAL then
         return ghat;
     else
         slp := __natural_rewrite (ghat, gens, K );
         assert g eq Evaluate (slp, gens );
         return slp;
     end if;

end function;

/* The Kantor-Kassabov recognition algorithm for PSL(2,2^e) */
RecogniseSL2_KK := function (G, q)

     vprint sl2q: "Apply Kantor-Kassabov black box algorithm";
     _, _, e := IsPrimePower( q );
     k := (q^2 - 2) div 2;

     /* 
        build subgroup of G isomorphic to PGL(2,2);
        this is the only step that's randomized.
     */
     flag, r, wr, u, wu := BuildPGL22 (G, q, k);
     assert Evaluate( wu, GeneratorsSequence( G )) eq u;
     if (not flag) then return false, _, _; end if;

     /* find a generator of the black box field */
     s, ws, min_s := BuildBlackBoxField (G, u, wu, r, wr, k, e);
     K := ext < GF (2) | min_s >; 
     Embed( K, GF( q ));
     xi := K.1;

/* 
     assert Evaluate( wr, GeneratorsSequence( G )) eq r;
     assert Evaluate( wu, GeneratorsSequence( G )) eq u;
     assert Evaluate( ws, GeneratorsSequence( G )) eq s;
*/
      
     /* set up inverse isomorphisms */

     alpha := pmap < Generic( G ) -> SL( 2, q ) | 
       g :-> __black_box_rewrite (g, [ u, r, s ], K : EVAL := true  )>;
       
     alpha1 := pmap < Generic( G ) -> WordGroup( G ) | 
       g :-> Evaluate( __black_box_rewrite (g, [ u, r, s ], K : EVAL := false ),
			    [wu,wr,ws] )>;

     beta := map < SL(2,q) -> Generic( G ) |
       M :-> __natural_rewrite ( M, [ u, r, s ], K :
                     EVAL := true) >; 
     
     beta1 := map< WordGroup( G ) -> Generic( G ) | 
              W :-> Evaluate( W, GeneratorsSequence( G ))>;
     
     // "completed data structure in time", Cputime (tt);

     return true, alpha, beta, alpha1, beta1;

end function;
