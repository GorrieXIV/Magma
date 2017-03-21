for d in [3..18 by 1] do
   for q in [2..1000] do 
      d, q;
      if IsOdd (q) and IsPrimePower (q) then
         if IsOdd (d) and IsOdd (q) then 
            Q, R := int_StandardPresentationForOmega (d, q);
            X := ClassicalStandardGenerators ("Omega", d, q);
            assert #Set (Evaluate (R, X)) eq 1;
         elif IsEven (d) then  
            Q, R := int_StandardPresentationForOmega (d, q: 
                    Type := "Omega+", Projective:=true);
            X := ClassicalStandardGenerators ("Omega+", d, q);
            assert #Set (Evaluate (R, X)) le 2;
assert forall{x : x in Set (Evaluate (R, X)) | IsScalar (x)};
if q mod 4 eq 3 then 
   n:= d div 2;
   if IsEven (n) then 
      z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 4 - 1]];
      z := z^(Order (X[3]) div 2);
assert IsScalar (z); assert Order (z) eq 2;
   else 
      z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 2 - 1]];
      z := z^(Order (X[3]) div 4);
      z := X[3]^0;
   end if;
else 
   z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 2 - 1]];
   z := z^(Order (X[3]) div 4);
assert IsScalar (z); assert Order (z) eq 2;
end if;
            Q, R := int_StandardPresentationForOmega (d, q: 
                    Projective := true, Type := "Omega-");
            X := ClassicalStandardGenerators ("Omega-", d, q);
if IsOdd (n) and q mod 4 eq 3 then 
 Y := ClassicalStandardGenerators ("Omega+", d, q);
 z := &*[Y[3]^(Y[8]^(2 * i)): i in [0..d div 4 - 1]];
 z := z^(Order (Y[3]) div 2);
 z *:= X[3]^(Order (X[3]) div 2);
assert IsScalar (z); assert Order (z) eq 2;
assert IsCentral (sub<Universe (X) | X >, z);
end if;
            assert #Set (Evaluate (R, X)) le 2;
assert forall{x : x in Set (Evaluate (R, X)) | IsScalar (x)};
            // assert #Set (Evaluate (R, X)) eq 1;
         end if;
      end if;
  end for;
end for;

/* 
if q mod 4 eq 3 then 
   n:= d div 2;
   if IsEven (n) then 
      z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 4 - 1]];
      z := z^(Order (X[3]) div 2);
assert IsScalar (z); assert Order (z) eq 2;
   else 
      z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 2 - 1]];
      z := z^(Order (X[3]) div 4);
      z := X[3]^0;
   end if;
else 
   z := &*[X[3]^(X[8]^(2 * i)): i in [0..d div 2 - 1]];
   z := z^(Order (X[3]) div 4);
assert IsScalar (z); assert Order (z) eq 2;
end if;
*/
  
/* 
if IsOdd( d div 2) then 
y := (X[8] * X[3] * X[8]^-1 * X[3])^2 * X[6] * X[3]^-1;   
z := z * y;
end if;
*/
