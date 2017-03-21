freeze;

/*
  This file contains all the low-level definitions for tensor categories (TenCat).
*/


// ------------------------------------------------------------------------------
//                                      Print
// ------------------------------------------------------------------------------
intrinsic Print( t::TenCat )
{Print t}
  if t`Contra then
    s := "Cotensor category of valence ";
  else
    s := "Tensor category of valence ";
  end if;
  s cat:= Sprintf( "%o (", Valence(t) );
  a := t`Arrows;
  i := t`Valence;
  stop := (t`Contra) select 1 else 0;
  while i ge stop do
    s cat:= ( i @ a eq 1 ) select "->" else (i @ a eq -1) select "<-" else "==";
    i -:= 1;
    s cat:= (i eq stop-1) select ")" else ",";
  end while;
  
  P := t`Repeats;
  if t`Contra then 
    assert {0} in P;
    Exclude(~P,{0}); 
  end if;
  i := #P;
  s cat:= " (";
  for X in P do
  	s cat:= Sprintf( "%o", X);
    i -:= 1;
    s cat:= (i eq 0) select ")" else ",";
  end for;

  printf s;
end intrinsic;

// ------------------------------------------------------------------------------
//                                    Compare
// ------------------------------------------------------------------------------
intrinsic 'eq'(TC1::TenCat, TC2::TenCat) -> BoolElt
{TC1 eq TC2}
  return (TC1`Valence eq TC2`Valence) and (TC1`Repeats eq TC2`Repeats) and forall{ x : x in Domain(TC1`Arrows) | (x @ TC1`Arrows) eq (x @ TC2`Arrows) };
end intrinsic;
