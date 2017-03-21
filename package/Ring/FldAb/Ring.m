freeze;
//
/* RingClassFields and stuff for non-maximal orders */


intrinsic RingClassField(O::RngOrd) -> FldAb
  {The ring class field of O as an abelian extension}

  require IsAbsoluteOrder(O): "Order must be defined over Z";

  f := Conductor(O);
  M := MaximalOrder(O);
  R, mR := RayClassGroup(M!!f);
  C, mC := RingClassGroup(O);

  h := InducedMap(mR, mC, map<PowerIdeal(M) -> PowerIdeal(O) | x:-> x meet O>, Minimum(f));

  q, mq := quo<R|Kernel(h)>;
  assert IsSurjective(h);

  return AbelianExtension(Inverse(mq)*mR);
end intrinsic;

/* 
 This is based on

   U_K -> (Z_K/f)^* -> Cl_f -> Cl -> 1

   U_K -> + (Z_K_p/f)^* /(O_p/f)^* -> Pic -> Cl -> 1
   
   1st sequence is for example in Cohen 2 (but follows trivially from the 
   usual definition)
   2nd sequence is e.g in Neukirch or Klueners/Pauli (Picard Groups)

   Using that (Z_K/f)^* = + (Z_K_p/f)^* is then follows

   that  Cl_f -> Pic is surjective! (and well defined)
*/     
