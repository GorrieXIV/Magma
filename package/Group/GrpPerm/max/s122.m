freeze;
import "sympreds.m": PointStabSp, IsotropicStabSp, SymplecticStab;
import "sympimprims.m":  GetWreathProd;
import "superfield.m": GammaSp;
 
PGL2_25 := function()
return
MatrixGroup<12,GF(2)|
Matrix(GF(2),12,12,\[0,1,1,1,1,0,1,1,1,1,1,0,1,1,0,1,1,
0,0,1,1,1,0,1,1,0,0,0,0,1,0,0,1,1,1,1,0,0,0,0,0,0,
1,0,0,1,1,1,0,1,1,0,1,0,1,0,0,0,1,1,1,1,1,0,1,1,0,
1,1,0,0,1,1,0,1,1,1,0,1,0,0,1,0,0,0,0,1,1,1,1,1,1,
0,0,1,1,0,0,0,1,1,1,0,0,0,0,1,1,0,0,1,0,1,1,1,1,0,
0,0,1,0,0,0,0,0,0,1,1,0,0,1,1,1,0,0,0,0,1,1,0,0,1,
1,0]),
Matrix(GF(2),12,12,\[1,1,1,1,0,0,1,0,1,1,1,1,1,1,1,1,1,
1,1,0,1,1,1,0,0,1,1,1,1,0,0,0,1,1,1,0,0,0,0,1,1,0,
0,0,0,0,1,0,0,0,0,1,0,1,1,1,1,1,0,0,1,1,0,1,1,0,0,
1,0,0,1,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,1,0,0,
0,1,0,1,1,0,1,0,0,1,1,0,1,1,1,0,0,1,1,0,1,1,0,0,1,
1,1,0,0,1,1,1,1,1,1,0,1,0,0,1,1,0,1,1,0,0,0,0,0,0,
0,0]),
Matrix(GF(2),12,12,\[1,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,
1,1,0,0,1,0,0,1,0,1,1,1,1,0,1,1,0,1,0,1,0,1,0,0,1,
1,0,0,1,0,0,1,0,1,1,1,1,1,0,0,1,0,0,1,0,0,0,0,0,0,
1,1,0,1,0,0,0,1,1,0,0,0,1,1,1,1,0,0,1,1,1,0,0,0,1,
0,1,0,0,1,1,1,0,1,1,0,1,0,1,1,0,1,0,0,1,1,1,0,1,1,
1,1,0,0,0,0,1,1,0,0,0,0,0,1,0,0,0,1,1,0,0,1,1,1,1,
1,1]) /*order=15600=2^4*3*5^2*13*/>;
end function;

S14 := function()
return
MatrixGroup<12,GF(2)|
Matrix(GF(2),12,12,\[0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,
0,0,0,0,1,1,0,1,1,1,0,0,0,0,0,0,1,0,1,0,0,0,1,0,0,
0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,
0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,
0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,
1,0,0,1,1,0,0,0,0,0,0,0,1,1,1,1,0,0,0,0,0,0,0,0,0,
1,0]),
Matrix(GF(2),12,12,\[1,0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,
0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,1,0,1,0,0,0,0,1,0,0,
0,1,0,1,0,0,0,0,0,0,1,0,1,0,1,0,0,0,0,0,0,0,0,1,0,
1,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,1,0,1,1,
1,0,0,0,0,0,0,1,0,0,0,1,1,1,0,0,0,0,1,0,0,0,0,0,1,
1,1,0,1,1,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,0,0,0,
0,0]),
Matrix(GF(2),12,12,\[0,0,0,0,0,0,0,0,0,0,1,1,1,1,0,0,0,
0,0,0,0,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,
0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,
0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,
0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,
1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,
1,0]) /*order=2^11*3^5*5^2*7^2*11*13*/>;
end function;
/*
Code to identify and get maximal subgroups of almost simple groups with
socle S(12,2)
*/

S122Identify := function(group:max:=true,Print:=0)
  //trivial aut gp makes life easier!
  A := PSp(12,2);
  iss, gens := StandardGenerators(A, "S122");
  A := sub< A | gens>;
  
  ims := [A.1, A.2];
  S := A;
  F, phi := FPGroupStrong(S);
  soc := Socle(group); assert soc eq group;
  if Print gt 1 then printf "group is S(12,2)"; end if;

  iss, gens := StandardGenerators(soc, "S122");
  if not iss then error "Standard generator error in S(12,2)"; end if;
  a:=gens[1]; b:=gens[2];
  soc := sub< soc | a,b >;
  newgens := [ group | a,b ];
  homom :=  hom< soc -> A | ims >;

  maximals:= [];
  if not max then 
    return homom, A, maximals, F, phi;
  end if;
    
  //Now for the maximals.  We work down the table in the book
  //These are subgroups of Sp(12,2), so we need a homomorphism
  iss, gens := StandardGenerators(Sp(12,2),"S122");
  sp := sub< GL(12,2) | gens >;
  sptoA := hom< sp->A | [A.1,A.2] >;

  //C1s
  Append(~maximals, sptoA(PointStabSp(12,2)));
  Append(~maximals, sptoA(IsotropicStabSp(12,2,2)));
  Append(~maximals, sptoA(IsotropicStabSp(12,2,3)));
  Append(~maximals, sptoA(IsotropicStabSp(12,2,4)));
  Append(~maximals, sptoA(IsotropicStabSp(12,2,5)));
  Append(~maximals, sptoA(IsotropicStabSp(12,2,6)));
  Append(~maximals, sptoA(SymplecticStab(12,2,2)));
  Append(~maximals, sptoA(SymplecticStab(12,2,4)));

  //C2s
  Append(~maximals, sptoA(GetWreathProd(12,2,3)));
  Append(~maximals, sptoA(GetWreathProd(12,2,2)));
  
  //C3s
  Append(~maximals, sptoA(GammaSp(12,2,2)));
  Append(~maximals, sptoA(GammaSp(12,2,3)));

  //C8s
  Append(~maximals, sptoA(SOPlus(12,2)));
  isit, form := SymplecticForm(SOMinus(12,2));
  assert isit;
  trans := GL(12,2)!CorrectForm(form,12,2,"symplectic");
  Append(~maximals, sptoA(SOMinus(12,2)^trans));

  //C9s
  Append(~maximals, sptoA(PGL2_25()));
  Append(~maximals, sptoA(S14()));

  return homom, A, maximals, F, phi;
end function;
