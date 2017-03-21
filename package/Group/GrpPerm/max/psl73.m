freeze;
 
/*
 * This file contains the functions to construct the maximal
 * subgroups of an almost simple group $G$ with $PSL(7, 3) < G <
 * PSL2(7, 3) - note Aut(PSL)/PSL = 2
 */

import "gl2.m": PSL2;
import "reds.m": ReduciblesSL;
import "imp_and_gamma.m": GammaLMeetSL;
import "psl2q.m": MakeHomomGeneral;

/*****************************************************************/
function L73Identify(group:  max:= true, Print:=0)

  if Print gt 1 then print "Making standard group"; end if;
  sl := SL(7,3);
  apsl := PSL2(7,3);
  factor := hom< sl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  homom, soc, group:=
       MakeHomomGeneral(group, 7, 3, 1, psl, apsl, factor : Print:=0);

  // Set up the subgroup of the outer automorphism group induced by group
  if max then
    is_novelty := #group eq #apsl;
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
  maximals cat:= [m@factor: m in ReduciblesSL(7, 3: Novelties:=is_novelty)];

  if Print gt 1 then "getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(7, 3, 7)@factor);

  if Print gt 1 then "getting orthogonal"; end if;
  Append(~maximals, SO(7,3)@factor);

  return homom, apsl, maximals, F, phi;

end function;
