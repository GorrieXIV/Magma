freeze;

MatrixToAuto := function (G, m)
   d := Degree (m);
   return [G!m[i] : i in [1..d]];
end function;
