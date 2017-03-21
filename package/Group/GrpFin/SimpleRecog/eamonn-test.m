freeze;

q := 17;
i := 0;
repeat
     H := RandomConjugate (SU (3,q));
     f, m1, m2, m3, m4:= RecogniseSU3 (H, q);
     assert f; 
     e := Random (H);
     w:= m3 (e);
     f := Evaluate (w, [H.i : i in [1..Ngens (H)]]);
     assert IsScalar (e * f^-1);
     i +:= 1;
i;
until 1 eq 0;
