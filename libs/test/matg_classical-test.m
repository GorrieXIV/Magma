// AttachSpec ("../mgrp.spec");
SetVerbose ("CompositionTree", 0);
SetVerbose ("ClassicalRecognition", 0);

TestPerms := true;
TestSL := true;
TestSP := true;
TestSUEven := true;
TestSUOdd :=  true;
TestOmega := true;
TestOmegaPlus := true;
TestOmegaMinus := true;

MyExteriorPower := function (G, t)
   M := GModule (G);
   N := ExteriorPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

MySymmetricPower := function(G, t)
   M := GModule (G);
   N := SymmetricPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

TestPresentation := function (E, d, q, type)
   if type eq "A" then
      type := "SL";
      Q, R := ClassicalStandardPresentation (type, d, q);
   elif type eq "2A" then
      type := "SU";
      Q, R := ClassicalStandardPresentation (type, d, q);
   elif type eq "C" then
      type := "Sp";
      Q, R := ClassicalStandardPresentation (type, d, q);
   elif type eq "D" then
      type := "Omega+";
      Q, R := ClassicalStandardPresentation (type, d, q);
   elif type eq "2D" then
      type := "Omega-";
      Q, R := ClassicalStandardPresentation (type, d, q);
   else
      type := "Omega";
      Q, R := ClassicalStandardPresentation (type, d, q);
   end if;

   Z := Evaluate (R, E);
   // assert #Set (Z) eq 1;
   return #Set (Z), Z;
end function;

 
CheckWords := function (G, X, WX)
   flag := Evaluate (WX, UserGenerators (G)) eq UserGenerators (X);
   return flag;
end function;

RandomClassicalGroup := function( n, F, type )

    Gens := [];
    if type eq "A" then G := SL( n, F );end if;
    if type eq "B" then G := Omega( n, F ); end if;
    if type eq "C" then G := Sp( n, F ); end if;
    if type eq "D" then G := OmegaPlus( n, F ); end if;
    if type eq "2A" then G := SU( n, F ); end if;
    if type eq "2D" then G := OmegaMinus( n, F ); end if;
    for i in [ 1..10 ] do
        Gens[i] := Random( G );
    end for;
    K := sub< Generic( G ) | Gens >;
    return K;
end function;


if TestPerms then 
// Test PSL
for q in [ 2, 3, 4 ] do
    for n in [3,4,5,6] do
	"PSL *** n,q ***";[n,q];
	G := PSL( n, q );
	N := Degree( G );
	F := GF( q );
	// time e,w := ClassicalSolve( G, "SL", n, #F);
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "SL", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "A");
	assert a eq 1;
    end for;
end for;


// TestPSp
for q in [2, 3, 4, 5] do
    for n in [4,6] do
	"PSp ***n,q***";[n,q];
	G := PSp( n, q );
	N := Degree( G );
	F := GF( q );
	// time e,w := ClassicalSolve( G, "Sp", n, #F);
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Sp", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "C");
	assert a eq 1;
    end for;
end for;


// TestPSU
for q in [2, 3,4] do
    for n in [3,4, 5] do
	"PSU ***n,q***";[n,q];
        if n eq 3 and q eq 2 then continue; end if;
	G := PSU( n, q );
	N := Degree( G );
	// time e,w := ClassicalSolve( G, "SU", n, q );
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "SU", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1;
    end for;
end for;

// TestPO+
for q in [2, 3,4] do
    for n in [4,6, 8] do
	"PO+ ***n,q***";[n,q];
	G := POmegaPlus( n, q );
	N := Degree( G );
	F := GF( q );
	// time e,w := ClassicalSolve( G, "Omega+", n, q );
       time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Omega+", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "D");
	assert a eq 1;
    end for;
end for;

// TestPO-
for q in [2, 3,4] do
    for n in [4,6,8] do
	"PO- ***n,q***";[n,q];
	G := POmegaMinus( n, q );
	N := Degree( G );
	F := GF( q );
	// time e,w := ClassicalSolve( G, "Omega-", n, q);
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Omega-", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "2D");
	assert a eq 1;
    end for;
end for;

// TestPO
for q in [3, 5] do
    for n in [3,5,7] do
	"PO ***n,q***";[n,q];
	G := POmega( n, q );
	N := Degree( G );
	F := GF( q );
	// time e,w := ClassicalSolve( G, "Omega", n, q);
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Omega", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "B");
	assert a eq 1;
    end for;
end for;

end if;


if TestSL then 
A, B := GetSeed ();
"SL SEED = ", A, B;

// Test SL
for  q in [ 2, 3, 5, 7,8] do 
   for n in [2, 3, 4,5,6] do
	G := RandomClassicalGroup( n, GF(q), "A" );
	F := BaseRing( G );
	 "*** SL n,q,N ***"; n;q;
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "SL", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "A");
        assert a eq 1;
	H := MySymmetricPower( G, 2 );
	N := Degree( H );
	"*** SL n,q,N ***";n;q;N;
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SL", n, q );
	// time e,w := ClassicalSolve( H, "SL", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "A");
	assert a eq 1;
	H := MyExteriorPower( G, 2 );
        if IsTrivial (H) then continue; end if;
	N := Degree( H );
	"*** SL n,q,N ***";n;q;N;
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SL", n, q );
	// time e,w := ClassicalSolve( H, "SL", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "A");
	assert a eq 1;
    end for;
end for;

end if;

if TestSP then 

A, B := GetSeed ();
"SP SEED = ", A, B;

// Test Sp
for  q in [2,4, 5, 7,8,9] do 
    for n in [4, 6,8,10 ] do
	G := Sp( n, q );
	F := BaseRing( G );
	"*** Sp n,q,N ***";n;q;
	// e, w := ClassicalSolve( G, "Sp", n, q );
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Sp", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "C");
	assert a eq 1;
	H := MySymmetricPower( G,2 );
	N := Degree( H );
	"*** Sp n,q,N ***";n;q;N;
	// time e,w := ClassicalSolve( H, "Sp", n, q );
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "Sp", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "C");
	assert a eq 1;
	H := MyExteriorPower( G,2 );
	N := Degree( H );
	"*** Sp n,q,N ***";n;q;N;
	// time e,w := ClassicalSolve( H, "Sp", n, q );
	 time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "Sp", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "C");
	assert a eq 1;
    end for;
end for;

end if;

if TestSUEven then 

A, B := GetSeed ();
"SU Even SEED = ", A, B;

// Test SU EvenDim
for q in [2,3,4, 5, 7] do 
    for n in [4,6,8,10] do
	G := RandomClassicalGroup( n, GF( q^2 ), "2A" );;
	F := BaseRing( G );
	"*** SU n,q,N, NATREP ***";[n,q];
	// e, w := ClassicalSolve( G, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "SU", n, q );
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1; 
	H := MySymmetricPower( G,2 );
	N := Degree( H );
	"*** SU n,q,N, SYMPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SU", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1; 
	H := MyExteriorPower( G,2 );
	N := Degree( H );
	"*** SU n,q,N,EXTPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SU", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1; 
    end for;
end for;

end if;

if TestSUOdd then 

A, B := GetSeed ();
"SU Odd SEED = ", A, B;

// Test SU OddDim
for  q in [2,3,4, 7] do 
    for n in [3,5,7,9,11] do
	G := RandomClassicalGroup( n, GF(q^2), "2A" );
	F := BaseRing( G );
	"*** SU n,q,N, NATREP ***";[n,q];
	// e, w := ClassicalSolve( G, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "SU", n, q );
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1;
	H := MySymmetricPower( G,2 );
	N := Degree( H );
	"*** SU n,q,N, SYMPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SU", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1;
	H := MyExteriorPower( G,2 );
	N := Degree( H );
	"*** SU n,q,N,EXTPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "SU", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "SU", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation (e, n, q, "2A");
	assert a eq 1;
    end for;
end for;

end if;

if TestOmega then 
A, B := GetSeed ();
"Omega SEED = ", A, B;


// Test Omega
  for  q in [3, 7, 9] do
     for n in [3..11 by 2] do
        G := RandomClassicalGroup( n, GF(q), "B" );
        F := BaseRing( G );
        "*** Omega n,q,N, NATREP ***";[n,q];
        // e, w := ClassicalSolve( G, "Omega", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( G, "Omega", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "B");
        assert a eq 1;
        H := MySymmetricPower( G,2 );
        N := Degree( H );
        "*** Omega n,q,N, SYMPOW ***";[n,q,N];
        // time e,w := ClassicalSolve( H, "Omega", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "Omega", n, q );

        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation( e, n, q, "B" );a;
        assert a eq 1;
        H := MyExteriorPower( G,2 );
        N := Degree( H );
        "*** Omega n,q,N,EXTPOW ***";[n,q,N];
        // time e,w := ClassicalSolve( H, "Omega", n, q );
        time f,a,b,c,d,e, w := ClassicalConstructiveRecognition ( H, "Omega", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
        a := TestPresentation( e, n, q, "B" );a;
        assert a eq 1;
    end for;
end for;

end if;

if TestOmegaPlus  then 
A, B := GetSeed ();
"Omega+ SEED = ", A, B;

// Test Omega+ 
for q in [2,3,4,5,7, 8] do 
    for n in [4..10 by 2] do 
    // for n in [6, 8, 10, 12] do
	G := RandomClassicalGroup( n, GF(q), "D" );
	F := BaseRing( G );
	"*** Omega+ n,q,N, NATREP ***";[n,q];
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (G, "Omega+", n, q);
	// e, w := ClassicalSolve( G, "Omega+", n, q );
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "D");
	assert a eq 1;
	H := MySymmetricPower( G,2 );
	N := Degree( H );
	"*** Omega+ n,q,N, SYMPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "Omega+", n, q );
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (H, "Omega+", n, q);
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
	a := TestPresentation( e, n, q, "D" );a;
	assert a eq 1;
	H := MyExteriorPower( G,2 );
	N := Degree( H );
	"*** Omega+ n,q,N,EXTPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "Omega+", n, q );
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (H, "Omega+", n, q);
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
	a := TestPresentation( e, n, q, "D" );a;
	assert a eq 1;
    end for;
end for;

end if;

if TestOmegaMinus  then 

A, B := GetSeed ();
"Omega- SEED = ", A, B;

// Test Omega- 
for q in [2,3,4,5,7, 8] do 
    for n in [4..10 by 2] do 
	G := RandomClassicalGroup( n, GF(q), "2D" );
	F := BaseRing( G );
	"*** Omega- n,q,N, NATREP ***";[n,q];
	// e, w := ClassicalSolve( G, "Omega-", n, q );
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (G, "Omega-", n, q);
        "WORDS evaluate? "; assert e eq Evaluate (w, [G.i : i in [1..Ngens (G)]]);
        a := TestPresentation (e, n, q, "2D");
	assert a eq 1;
	H := MySymmetricPower( G,2 );
	N := Degree( H );
	"*** Omega- n,q,N, SYMPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "Omega-", n, q);
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (H, "Omega-", n, q);
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
	a := TestPresentation( e, n, q, "2D" );a;
	assert a eq 1;
	H := MyExteriorPower( G,2 );
	N := Degree( H );
	"*** Omega- n,q,N,EXTPOW ***";[n,q,N];
	// time e,w := ClassicalSolve( H, "Omega-", n, q );
        time f,a,b,c,d,e,w := ClassicalConstructiveRecognition (H, "Omega-", n, q);
        "WORDS evaluate? "; assert e eq Evaluate (w, [H.i : i in [1..Ngens (H)]]);
	a := TestPresentation( e, n, q, "2D" );a;
	assert a eq 1;
    end for;
end for;

end if;

quit;
