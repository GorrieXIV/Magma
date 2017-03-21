//Testing Procedures for SmallDegree

//SetEchoInput (true);

 AttachSpec("modules.spec");
load "construct.m";
SetVerbose("SmallDegree",1);

NElts := 5;
NEltsA := 0;

MyExteriorPower := function (G, t)
   M := GModule (G);
   N := ExteriorPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

MySymmetricPower := function (G, t)
   M := GModule (G);
   N := SymmetricPower (M, t);
   G := ActionGroup (N);
   return G;
end function;

testAltSL:=function()
	for q in [2, 3,4,5, 8,9, 25,27] do
	    for d in [4..10] do
			G := SL(d, q);
			G := MyAlternatingSquare(G);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SL", d,q);

			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;			
		end for;
	end for;
	return true;	
end function;

testSymSL:=function()
	for q in [2,3,5,7, 9, 25,27] do
		for d in [4..10] do
			G := SL(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SL", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testSymSU:=function()
	for q in [3, 5,7, 9, 25,27] do
		for d in [3..10] do
			G := SU(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SU", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testAltSOOdd:=function()
	for q in [3,5, 9, 25,27] do
		for d in [5..13 by 2] do
		       G := SO(d, q);
			G := MyExteriorPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testSymSOOdd:=function()
	for q in [3, 5,7, 9, 25,27] do
	    for d in [5..13 by 2] do
		       G := Omega(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testAltSOMinus:=function()
	for q in [3,4,5, 8,9, 25,27] do
		for d in [6..12 by 2] do
		       G := OmegaMinus(d, q);
			G := MyExteriorPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega-", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testSymSOMinus:=function()
	for q in [5,7, 9, 25,27] do
		for d in [6..12 by 2] do
		       G := OmegaMinus(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega-", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testAltSOPlus:=function()
	for q in [3, 4,5, 8,9, 25,27] do
		for d in [8..12 by 2] do
		       G := OmegaPlus(d, q);
			G := MyExteriorPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega+", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testSymSOPlus:=function()
	for q in [3,5,7, 9, 25,27] do
		for d in [8..14 by 2] do
		       G := OmegaPlus(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega+", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testAltSp:=function()
	for q in [3,4,5, 8,9, 25,27] do
		for d in [8..12 by 2] do
			G := Sp(d, q);
			G := MyExteriorPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Sp", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testSymSp:=function()
	for q in [2,3,4,5,7, 8,9, 25,27] do
		for d in [6..12 by 2] do
		       G := Sp(d, q);
			G := MySymmetricPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Sp", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testAltSU:=function()
	for q in [2,3,4,5, 8,9, 25,27] do
		for d in [5..12] do
// if d eq 6 and q eq 2 then continue d; end if;
			G := SU(d, q);
			G := MyExteriorPower (G, 2);
			S := Sections (G);
			m := [Degree (s): s in S];
			max, index := Maximum (m);
			G := S[index];
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SU", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testAdjointSL:=function()
	// for q in [2,3,4,7,8,9,2^5, 3^5,5^3] do
	for q in [2,3,4,7,8,9] do
           for d in [3..10 by 1] do
			G := SL(d, q);
			G := MyAdjointRepresentation(G);
			d, Degree (G), q;
G:=RandomConjugate (G);
time			f, H := RecogniseSmallDegree (G, "SL", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
if q eq 2 and d eq 3 then continue; end if;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testAdjointSU:=function()
	 for q in [3,4,5,7,8,9] do 
		// for d in [3,5,6,7,8,9,10,11,12] do
		for d in [3..11 by 1] do
		       G := SU(d, q);
			G := MyAdjointRepresentation(G);
G:=RandomConjugate (G);
			"PARAMS ", d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SU", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSL:=function()
	for qq in [2, 3,4,5, 8,9] do
		q:=qq^2;
		for d in [3..12] do
			G := SL(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SL", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);

			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testDualDeltaSL:=function()
	for qq in [2, 3,4,5, 8,9] do
		q:=qq^2;
		for d in [3..12] do
			G := SL(d, q);
			G := MyDualDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SL", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
assert Type (x) eq GrpMatElt;
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);

			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSU:=function()
	for qq in [2,3,4,5, 8,9] do
		q:=qq^2;
		// for d in [3..9 by 1] do
		for d in [3..11 by 1] do
// if d eq 4 and q eq 4 then continue; end if;
			G := SU(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SU", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;


testDualDeltaSU:=function()
	for qq in [2,3,4,5, 8,9] do
		q:=qq^2;
		for d in [3..11 by 1] do
			G := SU(d, q);
			G := MyDualDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "SU", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSOOdd:=function()
	for qq in [3,5, 7,9] do
		q:=qq^2;
		for d in [3..13 by 2] do
			G := Omega(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSOPlus:=function()
	for qq in [2,3,4,5, 7,9] do
		q:=qq^2;
		for d in [6..12 by 2] do
		       G := OmegaPlus(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Omega+", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSp:=function()
	for qq in [2,3,4,5, 7,8,9] do
		q:=qq^2;
		for d in [4..12 by 2] do
			G := Sp(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
time			f, H := RecogniseSmallDegree (G, "Sp", d,q);
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				// "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

testDeltaSOMinus:=function()
	for qq in [2,3,5, 7] do
		q:=qq^2;
		for d in [4..12 by 2] do
			G := OmegaMinus(d, q);
			G := MyDeltaRepresentation(G,1);
G:=RandomConjugate (G);
			d, Degree (G), q;
		time	f, H := RecogniseSmallDegree (G, "Omega-", d,q);
"Now completed ...";
if not f then continue; end if;
assert forall{x : x in Generators (H) | Determinant (x) eq 1};
			for k in [1..NElts] do
				 "k = ", k;
				a := Random (G);
				b := Random (G);
				c := a * b;
				flag,x := SmallDegreePreimage (G, a);
				flag,y := SmallDegreePreimage (G, b);
				flag,z := SmallDegreePreimage (G, c);
				assert IsScalar ((x * y) * z^-1);
			end for;
			for k in [1..NEltsA] do
				a:=Random(Generic(G));
				flag,x := SmallDegreePreimage (G, a);
				assert not flag;
			end for;		
		end for;
	end for;
	return true;	
end function;

test:=function()
"*** ALTSL";
	testAltSL(); 
"SYMSL";
	testSymSL(); 
"DeltaSL";
	testDeltaSL(); 
"DUALDELTA SL";
	testDualDeltaSL(); 
"Adjoint SL";
	testAdjointSL();

"Now SP";
"SYM SP";
	testSymSp(); 
"ALT SP";
	testAltSp(); 
"DELTA SP";
	testDeltaSp(); 

"NOW SU";
"AD SU";
	testAdjointSU(); 
"DELTA SU";
	testDeltaSU(); 
"DUAL SU";
	testDualDeltaSU(); 
"ALT SU";
	testAltSU(); 
"SYM SU";
	testSymSU(); 

"SO M";
"SYM SOM";
	testSymSOMinus();
"ALT SOM";
	testAltSOMinus();
"DELTA SOM";
	testDeltaSOMinus(); 

"SO P";
"SYM SOP";
	testSymSOPlus(); 
"ALT SOP";
	testAltSOPlus(); 
"DELTA SOP";
	testDeltaSOPlus(); 

"SO ODD";

"SYM SO ODD";
	testSymSOOdd();
"ALT SO ODD";
	testAltSOOdd(); 
"DELTA SO ODD";
	testDeltaSOOdd(); 

	return true;
end function;

