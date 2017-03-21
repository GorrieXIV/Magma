freeze;
 
/*
 * This file will contain the functions to construct the maximal
 * subgroups of an almost simple group $G$ with $PSL(6, 3) < G <
 * PGL2(6, 3) - note Aut(PSL)/PSL = 2x2
 */

import "gl2.m": PGL2;
import "reds.m": ReduciblesSL, SLStabOfHalfDim;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "psl2q.m": MakeHomomGeneral;
import "tensor.m": SLTensor;
import "classicals.m": NormOfO;



/*****************************************************************/
function L63Identify(group:  max:= true, Print:=0)

  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(6,3);
  sl := SL(6,3);
  apsl := PGL2(6,3);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 6, 3, 1, psl, apsl, factor : Print:=0);

  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    quot, proj := quo<apsl|psl>;
    delta := proj(apsl.1); //diagonal aut.
    iota := proj(apsl.3); assert Order(iota) eq 2;   //graph aut
    newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
    groupquot := sub< quot | [proj(g) : g in newgens] >; 
    is_novelty := not groupquot subset sub< quot | delta >; 
    if Print gt 1 then print "is_novelty = ",is_novelty; end if;
    c9 := groupquot subset sub< quot | delta*iota >;
    if Print gt 1 then print "c9 = ",c9; end if;
    invol := apsl.3;
  end if;

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  F, phi := FPGroupStrong(sub< psl | [ soc.i @ homom : i in [1..Ngens(soc)] ]>);

  //get apsl right
  newgens := [ apsl | group.i @ homom : i in [1..Ngens(group)] ];
  subapsl := sub< apsl | newgens >;
  for g in Generators(apsl) do if not g in subapsl then
     Append(~newgens,g); subapsl := sub< apsl | newgens >;
  end if; end for;
  apsl := subapsl;

  if not max then
    return homom, apsl, [], F, phi;
  end if;

  maximals:= [];

  if Print gt 1 then "getting reducibles"; end if;
  maximals cat:= [m@factor: m in ReduciblesSL(6, 3: Novelties:=is_novelty)];
  if is_novelty then
    maximals cat:= [ SLStabOfHalfDim(6, 3)@factor ]; //not a novelty!
  end if;

  if Print gt 1 then "getting imprimitives"; end if;
  Append(~maximals,ImprimsMeetSL(6, 3, 2)@factor);
  Append(~maximals,ImprimsMeetSL(6, 3, 3)@factor);

  if Print gt 1 then "getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(6, 3, 2)@factor);
  Append(~maximals, GammaLMeetSL(6, 3, 3)@factor);

  if Print gt 1 then "getting tensor product"; end if;
  Append(~maximals, SLTensor(2, 3, 3)@factor);

  if Print gt 1 then "getting symplectics"; end if;
  Append(~maximals, Sp(6,3)@factor);

  if Print gt 1 then "getting orthogonals"; end if;
  Append(~maximals, NormOfO(6, 3, 1)@factor);
  Append(~maximals, NormOfO(6, 3,-1)@factor);

  if c9 then
    if Print gt 1 then "getting psl33s"; end if;
    l33 := MatrixGroup<6, GF(3) |
    \[ 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 2, 0, 2, 0, 0, 0, 
    2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 1 ],
    \[ 2, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 1, 0, 
    1, 2, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0 ] > @ factor;
    maximals cat:= [l33, l33^invol];

    if Print gt 1 then "getting m12s"; end if;
    m12 := MatrixGroup<6, GF(3) |
    \[ 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1 ],
    \[ 0, 1, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 
    0, 1, 2, 0, 0, 1, 0, 1, 0, 2, 0, 0 ] > @ factor;
    maximals cat:= [m12, m12^invol];
  end if;

  return homom, apsl, maximals, F, phi;

end function;
