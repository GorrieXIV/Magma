freeze;
 
import "gl2.m": PGammaL2;
import "reds.m": SLPointStab, SLStabOfNSpace, SLStabOfNSpaceMeetDual,
             SLStabOfNSpaceMissDual, SLStabOfHalfDim, SLPointMeetHyperplane,
             SLPointUnmeetHyperplane;
import "imp_and_gamma.m": ImprimsMeetSL, GammaLMeetSL;
import "psl2q.m": MakeHomomGeneral;

/**********************************************************************/

function Identification(d,group,Print)
// The initial part of the code common to all Ld_2Identify
  if Print gt 1 then print "Making standard group"; end if;
  gl := GL(d,2);
  sl := SL(d,2);
  apsl := PGammaL2(d,2);
  factor := hom< gl->apsl | apsl.1, apsl.2 >;
  psl := sl @ factor;

  if Print gt 1 then print "Setting up isomorphism"; end if;
  soc := Socle(group);
  /* Reduce number of generators of soc, and
   * rearrange generators of group to get those of soc coming first
   */
  newgens := [ group | Random(soc), Random(soc) ];
  while sub < soc | newgens > ne soc do
    x:=Random(soc);
    while x in sub < soc | newgens > do x:=Random(soc); end while;
    Append(~newgens,x);
  end while;
  soc := sub < soc | newgens >;
  for g in Generators(group) do
   if not g in sub< group | newgens > then Append(~newgens,g); end if;
  end for;
  group := sub< group | newgens >;
  homom:= MakeHomomGeneral(group, d, 2, 1, psl, apsl, factor : Print:=0);
  dh := Domain(homom);

  if Print gt 1 then print "Calling FPGroupStrong"; end if;
  temp := [dh.i : i in [1..Ngens(dh)] | dh.i in Socle(dh)];
  F, phi := FPGroupStrong(sub< psl | temp @ homom>);
  if Print gt 1 then print "Identifying group"; end if;
  // Also get the generators of apsl correct
  newgens := [ apsl | dh.i @ homom : i in [1..Ngens(dh)] ];
  type := #group eq #apsl select "psl.2" else "psl";
  if type eq "psl" then Append(~newgens,apsl.3); end if;
  invol := apsl.3; //outer involution
  if Print gt 1 then print "Type = ",type; end if;
  apsl := sub< apsl | newgens >;
  return apsl, homom, F, phi, factor, type, invol;
end function;

/*********************************************************************/
//functions for L7(2)

function L7_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(7,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(7, 2)@factor);
    for i in [2..6] do
      g:= SLStabOfNSpace(7, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(7, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(7, 2)@factor);
    for i in [2, 3] do
      Append(~maximals,SLStabOfNSpaceMissDual(7, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(7, 2,i)@factor);
    end for;
  end if;

  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(7, 2, 7)@factor);

  return homom, apsl, maximals, F, phi;
end function;


/*********************************************************************/
//functions for L8(2)

function L8_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(8,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(8, 2)@factor);
    for i in [2, 3] do
      g:= SLStabOfNSpace(8, 2, i); 
      Append(~maximals, g@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(8, 2)@factor);
    for i in [5..7] do
      g:= SLStabOfNSpace(8, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(8, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(8, 2)@factor);
    for i in [2, 3] do
      Append(~maximals,SLStabOfNSpaceMissDual(8, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(8, 2,i)@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(8, 2)@factor);
  end if;

  if Print gt 1 then print "Getting imprimitive"; end if;
  Append(~maximals, ImprimsMeetSL(8, 2, 2)@factor);

  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(8, 2, 2)@factor);

  if Print gt 1 then print "Getting classicals"; end if;
  Append(~maximals, Sp(8, 2)@factor);

  return homom, apsl, maximals, F, phi;
end function;

/***********************************************************/
//code for PSL(9, 2)

function L3_4()
  grp:=MatrixGroup<9, GF(2) |
    \[ 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 
    1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 
    0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 
    0, 1, 0, 1, 0, 0, 1 ],
    \[ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 
    1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 
    0, 0, 0, 1, 1, 0, 1 ]
        /* order = 120960 = 2^7 * 3^3 * 5 * 7 */ >;
  return grp;
end function;

function L9_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(9,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(9, 2)@factor);
    for i in [2..8] do
      g:= SLStabOfNSpace(9, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(9, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(9, 2)@factor);
    for i in [2, 3, 4] do
      Append(~maximals,SLStabOfNSpaceMissDual(9, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(9, 2,i)@factor);
    end for;
  end if;

  if Print gt 1 then print "Getting imprimitive"; end if;
  Append(~maximals, ImprimsMeetSL(9, 2, 3)@factor);

  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(9, 2, 3)@factor);

  if Print gt 1 then print "Getting tensor induced groups"; end if;
  Append(~maximals, TensorWreathProduct(SL(3, 2), Sym(2))@factor);

  if Print gt 1 then print "Getting C_9s"; end if;
  Append(~maximals, L3_4()@factor);
  return homom, apsl, maximals, F, phi;
end function;

/**********************************************************************/
//functions for L10(2)

function L10_2Identify(group: max:= true, Print:=0)

  L52:= MatrixGroup<10, GF(2) |
    \[ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1 ], 
    \[ 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0] /* order = 9999360 = 2^10 * 3^2 * 5 * 7 * 31 */ >;

  //I think that Colva has forgotten about M22.2 !

  M22_2:= MatrixGroup<10, GF(2) |
   \[ 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 
   0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 
   0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 
   1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1
   ],
   \[ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 
   0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 
   0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 
   1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0
   ]
        /* order = 887040 = 2^8 * 3^2 * 5 * 7 * 11 */ >;
 
  apsl, homom, F, phi, factor, type, invol := Identification(10,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(10, 2)@factor);
    for i in [2..4] do
      g:= SLStabOfNSpace(10, 2, i); 
      Append(~maximals, g@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(10, 2)@factor);
    for i in [6..9] do
      g:= SLStabOfNSpace(10, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(10, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(10, 2)@factor);
    for i in [2..4] do
      Append(~maximals,SLStabOfNSpaceMissDual(10, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(10, 2,i)@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(10, 2)@factor);
  end if;

  if Print gt 1 then print "Getting imprimitive"; end if;
  Append(~maximals, ImprimsMeetSL(10, 2, 2)@factor);

  if Print gt 1 then print "Getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(10, 2, 2)@factor);
  Append(~maximals, GammaLMeetSL(10, 2, 5)@factor);

  if Print gt 1 then print "Getting classical"; end if;
  Append(~maximals, Sp(10, 2)@factor);

  if Print gt 1 then print "Getting L5_2"; end if;
  Append(~maximals, L52@factor);

  if type eq "psl" then
    if Print gt 1 then print "Getting M22.2s"; end if;
    Append(~maximals, M22_2@factor);
    Append(~maximals, (M22_2@factor)^invol);
  end if;

  return homom, apsl, maximals, F, phi;
end function;

/****************************************************************/
//functions for L11(2)

function M24()
  grp:= MatrixGroup<11, GF(2) |
    \[ 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1 ],
    \[ 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
    0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 
    1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 ]
        /* order = 244823040 = 2^10 * 3^3 * 5 * 7 * 11 * 23 */ >;
  grp`Order := 244823040;
  grp2 := MatrixGroup<11, GF(2)| Transpose(grp.-1), Transpose(grp.-2) >;
  grp2`Order := 244823040;
  return grp, grp2;
end function;

function L11_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(11,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(11, 2)@factor);
    for i in [2..10] do
      g:= SLStabOfNSpace(11, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(11, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(11, 2)@factor);
    for i in [2..5] do
      Append(~maximals,SLStabOfNSpaceMissDual(11, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(11, 2,i)@factor);
    end for;
  end if;
  
  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(11, 2, 11)@factor);

  if type eq "psl" then
      if Print gt 1 then print "Getting C_9s"; end if;
      g1, g2 := M24();
      Append(~maximals, g1@factor);
      Append(~maximals, g2@factor);
  end if;
  return homom, apsl, maximals, F, phi;
end function;

/**********************************************************************/
//functions for L12(2)

function TP()
  grp:= MatrixGroup<12, GF(2) |
    \[ 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 
    1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 
    0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 
    0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 ],
    \[ 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 
    1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 
    0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 
    1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 
    1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0 ]
        /* order = 3386880 = 2^9 * 3^3 * 5 * 7^2 */ >;
  return grp;
end function;

function L12_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(12,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(12, 2)@factor);
    for i in [2..5] do
      g:= SLStabOfNSpace(12, 2, i); 
      Append(~maximals, g@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(12, 2)@factor);
    for i in [7..11] do
      g:= SLStabOfNSpace(12, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(12, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(12, 2)@factor);
    for i in [2..5] do
      Append(~maximals,SLStabOfNSpaceMissDual(12, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(12, 2,i)@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(12, 2)@factor);
  end if;

  if Print gt 1 then print "Getting imprimitive"; end if;
  for i in [2, 3, 4] do
    Append(~maximals, ImprimsMeetSL(12, 2, i)@factor);
  end for;

  if Print gt 1 then print "Getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(12, 2, 2)@factor);
  Append(~maximals, GammaLMeetSL(12, 2, 3)@factor);

  if Print gt 1 then print "Getting tensor product"; end if;
  Append(~maximals, TP()@factor);

  if Print gt 1 then print "Getting classical"; end if;
  Append(~maximals, Sp(12, 2)@factor);

  return homom, apsl, maximals, F, phi;
end function;

function L13_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(13,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(13, 2)@factor);
    for i in [2..12] do
      g:= SLStabOfNSpace(13, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(13, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(13, 2)@factor);
    for i in [2..6] do
      Append(~maximals,SLStabOfNSpaceMissDual(13, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(13, 2,i)@factor);
    end for;
  end if;
  
  if Print gt 1 then print "Getting semilinear"; end if;
  Append(~maximals, GammaLMeetSL(13, 2, 13)@factor);

  return homom, apsl, maximals, F, phi;
end function;

function L14_2Identify(group: max:= true, Print:=0)
 
  apsl, homom, F, phi, factor, type := Identification(14,group,Print);

  maximals := [];
  if not max then
    return homom, apsl, maximals, F, phi;
  end if;

  if Print gt 1 then print "Getting reducibles"; end if;
  if type eq "psl" then
    Append(~maximals, SLPointStab(14, 2)@factor);
    for i in [2..6] do
      g:= SLStabOfNSpace(14, 2, i); 
      Append(~maximals, g@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(14, 2)@factor);
    for i in [8..13] do
      g:= SLStabOfNSpace(14, 2, i); 
      Append(~maximals, g@factor);
    end for;
  else
    Append(~maximals, SLPointMeetHyperplane(14, 2)@factor);
    Append(~maximals, SLPointUnmeetHyperplane(14, 2)@factor);
    for i in [2..6] do
      Append(~maximals,SLStabOfNSpaceMissDual(14, 2,i)@factor);
      Append(~maximals,SLStabOfNSpaceMeetDual(14, 2,i)@factor);
    end for;
    Append(~maximals, SLStabOfHalfDim(14, 2)@factor);
  end if;

  if Print gt 1 then print "Getting imprimitive"; end if;
  Append(~maximals, ImprimsMeetSL(14, 2, 2)@factor);

  if Print gt 1 then print "Getting semilinears"; end if;
  Append(~maximals, GammaLMeetSL(14, 2, 2)@factor);
  Append(~maximals, GammaLMeetSL(14, 2, 7)@factor);

  if Print gt 1 then print "Getting classical"; end if;
  Append(~maximals, Sp(14, 2)@factor);

  return homom, apsl, maximals, F, phi;
end function;
