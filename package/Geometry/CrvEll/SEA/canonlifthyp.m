
freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    CANONICAL LIFT TRACE ALGORITHMS                 //
//			FOR p with X0(p) ELLIPTIC		      //
//			     OR HYPERELLIPTIC			      //
//                             Mike Harrison                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "canonliftgen.m" : SatohNorm;

/**************** Data ****************************************/

  // For each p, we use modular functions t,s that generate
  //  the function field with equation s^2=f(t) where f is
  //  a monic poly in Z[x] of degree 2g+2. t|wp=t &s|wp=-s.
  //  2j(z)=U(t)-B(t)s, 2j(pz)=U(t)+B(t)s for U,B monic in Z[x]
  //  of degrees p & p-g-1. f(x) = s(x)^2 mod p for a monic
  //  poly s in (Z/pZ)[x] of degree g+1. 
  //  U(x)=x^p+x-2c, B(x)s(x)=x^p-x, j=t-c jp=t^p-c mod p
  //  for some c in Z/pZ.
  // For each p, we store U,B,f,s & c. We don't work with p=37
  //  where the hyperelliptic involution isn't wp.


HypPols := recformat<
    f	: RngUPolElt,  // polynomial in Z[x]
    U	: RngUPolElt,  // polynomial in Z[x]
    B	: RngUPolElt,  // polynomial in Z[x]
    sp	: RngUPolElt,  // polynomial in GF(p)[x]
    spd	: RngUPolElt   // derivative of sp
>;

PRIMS := \[11,17,19,23,29,31,41,47,59,71];

FS := [
  \[ -7, 12, 2, -16, 1 ], \[ -16, -28, -27, -6, 1 ],
  \[ -8, 20, -8, -8, 1 ], \[ -7, 10, -11, 2, 2, -8, 1 ],
  \[ -7, 8, 8, 2, -12, -4, 1 ], \[ -3, -14, -11, 18, 6, -8, 1 ],
  \[ -8, -20, -15, 8, 20, 10, -8, -4, 1 ],
  \[ -11, 28, -38, 30, -13, -16, 19, -24, 11, -6, 1 ],
  \[ -8, -4, 20, -24, -3, 40, -62, 40, 3, -28, 22, -8, 1 ],
  \[ -7, 6, -27, 40, -58, 66, -66, 40, 15, -48, 66, -66, 37, -10, 1 ]
];

US := [
  \[ -6750, 24300, 40095, -187407, 132066, 133056, -177408, 69630,
    -12716, 1188, -55, 1 ],
  \[ 3456, 38880, 118728, -20502, -704684, -1364046, -885700, 337331,
    760818, 154615, -197744, -39542, 30532, 102, -2108, 425, -34, 1 ],
  \[ 16000, -22400, -337440, 475456, 1562104, -1988616, -3025294, 3245960,
    2833014, -2420087, -1140950, 932406, 129580, -180443, 21090, 11153,
    -4066, 570, -38, 1 ],
  \[ -6750, 48600, -83835, -170775, 1115109, -2492280, 2732814, -116403,
    -4877702, 8362616, -6612454, 302266, 5423124, -6447728, 3209696,
    336674, -1470068, 953856, -336927, 74221, -10465, 920, -46, 1 ],
  \[ -6750, -12150, 281880, 570024, -1754181, -5229135, 2357613, 19103721,
    9708910, -31795426, -38397537, 19207947, 54103270, 9216142, -37142939,
   -18871083, 14041394, 10954634, -3592085, -3427365, 853818, 622398,
   -189399, -53679, 26680, -580, -1421, 319, -29, 1 ],
  \[ 108000, 475200, -7053120, -27353408, 90884374, 303670296, -665806437,
    -1361301729, 3259359840, 2249261823, -9368721606, 2279583264, 13054272515,
    -12759480061, -4169029296, 14390047139, -7803693550, -2988803682,
    6239473912, -3296588360, 134066754, 908915598, -685615437, 294482733,
    -87483178, 18983315, -3052818, 361336, -30659, 1767, -62, 1 ],
  \[ 16000, 67200, -465760, -2966432, -1742664, 20985112, 46140990, -31732934,
    -217030548, -147139488, 436080674, 745775322, -271341362, -1542677562,
    -605560447, 1832223375, 1772593672, -1270633050, -2400692229, 343522723,
    2179745361, 282422801, -1503727029, -421357697, 879637411, 261059095,
   -462271351, -61715127, 193718727, -24135265, -49355103, 20512341, 3613289,
   -4706595, 1099661, 163057, -162483, 46617, -7544, 738, -41, 1 ],
  \[ -65536, 688128, -2502656, -96256, 38598656, -187217920, 508021120,
    -845669120, 552981696, 1469334304, -5945275904, 11705275552, -14673798654,
    9100068184, 8421580132, -34288012648, 56657584158, -60426283952,
    36612252089, 9942017442, -60791892299, 93046207239, -92028642340,
    59196883097, -10454018992, -33364599371, 57280402355, -57873890484,
    41879296232, -20241250112, 2065827049, 8435506655, -11611941072,
    10182603298, -7040645261, 4071881378, -2013138357, 856757031, -313468474,
    97893151, -25770006, 5617769, -990431, 136864, -14194, 1034, -47, 1 ],
  \[ 16000, -67200, -783520, 5573376, -5127336, -60792184, 241324042,
    -170978932, -1262437160, 4310971231, -3953349811, -10887235780,
    41679530185, -51342089572, -33068562195, 230682514316, -372641172307,
    121615007703, 682044179678, -1549365239197, 1373184591667, 614906882627,
    -3566756201696, 4920423266916, -2342393877496, -3589340274442,
    8772457933356, -8488557160148, 1742977715620, 7131088674129,
    -11643540780203, 8512399456274, -315658868113, -6917286294515,
    8713332734648, -5190227733987, -54249978263, 3397583328372,
    -3658171840037, 1987950394792, -179519591637, -748989116551, 800595050760,
    -459184355769, 134398080099, 28871590941, -64236756338, 46651654354,
    -23352309386, 9059054346, -2830320860, 721829600, -150487052, 25475079,
    -3452149, 365800, -29205, 1652, -59, 1 ],
  \[ -6750, 97200, -603855, 2263977, -4854483, -2486349, 75190491, -399596520,
    1441975423, -4089818964, 9450153463, -17516526653, 23635982289,
    -11859874932, -53385529273, 230566737711, -585283867605, 1136695427037,
    -1753961304140, 2020891913264, -1147488305875, -1930304898882,
    8102336330029, -17218530732347, 27006964902986, -32365758791872,
    25902000374138, -468390635342, -46332664858222, 107139839089502,
    -162234735929274, 182582147217312, -140033523896938, 22513210292184,
    152367877270246, -334009986053250, 451855980915164, -443144048889720,
    284518400252142, -11142427766850, -289840331821002, 512373447321402,
    -576967281819172, 466024421705696, -230395084854230, -36287337331916,
    241209603962570, -330646545417814, 304702155703516, -205131886553392,
    87504290135653, 5131997859077, -54867900326127, 66216047255551,
    -54817285755105, 36239054778472, -20052219750661, 9464634765852,
    -3841191816845, 1343947848527, -405138280373, 104923131180, -23228729413,
    4364552115, -689157169, 90223321, -9613968, 812240, -52327, 2414, -71, 1 ]
];


BS := [
  \[ 0, -12150, 27135, 10665, -48573, 29313, -7187, 843, -47, 1 ],
  \[ 0, -5184, -43200, -113108, -82670, 94612, 190227, 41547, -80070,
    -18242, 17292, 24, -1548, 350, -31, 1 ],
  \[ 0, 33600, -8160, -292400, 23472, 791244, 39282, -847909, -47024,
    392654, -24046, -82469, 19162, 4833, -2652, 446, -34, 1 ],
  \[ 0, 12150, -72495, 168588, -144045, -254034, 930982, -1256170,
    604358, 693650, -1563176, 1271974, -225188, -444070, 421050, -184350, 
    47754, -7696, 759, -42, 1 ],
  \[ 0, -24300, -57510, 257850, 839187, -373185, -3602119, -2371192, 5865017,
    8434433, -2363779, -10263744, -2746015, 5976011, 3151075, -2093854,
    -1356433, 569525, 299477, -129484, -28279, 19043, -895, -1076, 273,
    -27, 1 ],
  \[ 0, 712800, 1216080, -18430560, -15262464, 168899202, -12931221,
    -720077416, 624871714, 1239052988, -2259335558, 68648452, 2679085427,
    -2318039014, -229246628, 1710545918, -1243026758, 211524870, 296674626,
    -291810274, 145889932, -48916468, 11793961, -2085662, 269348, -24778,
    1540, -58, 1 ],
  \[ 0, 44800, 167040, -447040, -2734272, -1104272, 13488360, 21067652,
    -24681704, -83929974, -8986886, 169059382, 127641266, -196479899,
    -283039783, 124573790, 366614063, -12946368, -332987597, -58867672,
    241909907, 60568430, -155045647, -17919564, 79114945, -12025938,
    -24060781, 11190142, 1979597, -2931764, 750233, 110144, -122263, 37484,
    -6439, 666, -39, 1 ],
  \[ 0, 114688, -1114112, 4854784, -11205632, 7426048, 42663936, -182555136,
    394092544, -508851472, 213245648, 743315936, -2203729384, 3409478688,
    -3280008936, 1139839970, 2576264698, -6272528962, 8005203155, -6671665088,
    2744569094, 1996771588, -5520074039, 6637395180, -5455622885, 3028415830,
    -601645255, -1012737914, 1632999370, -1525982346, 1093778952, -644352392,
    319489974, -134176208, 47566499, -14083902, 3424200, -667810, 101271,
    -11438, 901, -44, 1 ],
  \[ 0, -56000, 320800, 391440, -7693120, 21125500, 11515130, -204780145,
    486681785, -102547033, -2147060784, 5552726794, -4419031758, -9431888681,
    33728080307, -42367773552, -2994127157, 105330637610, -188172973931,
    127559513693, 123083802224, -421097252069, 490425751691, -161944881372,
    -408669953969, 799965143719, -668167261718, 69589638764, 563644022562,
    -787681290965, 505670881115, 2900924856, -364669742737, 407962360532,
    -223582547975, 9985786664, 102435489491, -105519055992, 58212400117,
    -14331637533, -6742538722, 10205452686, -6853903214, 3244679736,
    -1188153136, 347102566, -81626216, 15409226, -2307408, 268126, -23322,
    1429, -55, 1 ],
  \[ 0, 12150, -163215, 1115640, -5311143, 18820224, -50700172, 99823812,
    -102454041, -183909134, 1354660714, -4462311942, 10695310224,
    -20015395554, 28262441676, -23240987282, -17879387475, 124501604946,
    -315187724212, 564766450688, -765154573538, 705985549104, -115433273216,
    -1206098873334, 3175185881748, -5228317292044, 6292310032120,
    -5077451367560, 719644756530, 6451571564682, -14460150103020,
    19999710623352, -19681838601268, 11819712227412, 2180981559572,
    -17790742756618, 29025463386612, -31179247603548, 23207078145510,
    -8345354986332, -7468523752270, 18486966963350, -21719818051100,
    17831212433536, -10100011266030, 2336962513536, 2906983627184,
    -4989755986066, 4711466210012, -3361479243242, 1952316811463,
    -948555371584, 389878900245, -136099552242, 40341734984, -10121407164,
    2136756509, -376218102, 54551634, -6399080, 591884, -41538, 2078, -66, 1 ]
];

SS := [
  \[ 2, 3, 1 ], \[ 16, 14, 1 ], \[ 7, 15, 1 ], \[ 19, 16, 19, 1 ],
  \[ 14, 21, 27, 1 ], \[ 20, 26, 27, 1 ], \[ 19, 34, 35, 39, 1 ],
  \[ 41, 29, 38, 1, 44, 1 ], \[ 46, 41, 48, 57, 3, 55, 1 ],
  \[ 63, 44, 65, 0, 68, 6, 66, 1 ]
];

CS := \[9,6,18,17,11,2,36,9,24,38];

/*******************************************************************/

function NormParam(t,s,pols,use_log)
   /* 
      trace is +/- Sqrt(Norm(p*
       ( (U'(t)-B'(t)s-B(t)f'(t)/2s)/(U'(t)+B'(t)s+B(t)f'(t)/2s) ) )
      the top term being a p-adic unit (=2 mod p) and the bottom
      one precisely divisible by p.
   */

    Bfds := (Evaluate(pols`B,t)*Evaluate(Derivative(pols`f),t))
		div (s+s);
    Bds := s*Evaluate(Derivative(pols`B),t);
    Uds := Evaluate(Derivative(pols`U),t);
    c := (Uds-Bds-Bfds) div ShiftValuation(Uds+Bds+Bfds,-1);
    c := ChangePrecision(R,Precision(R)-1)!c where R is Parent(c);
    return SquareRoot(use_log select SatohNorm(c) else Norm(c));

end function;



/*********** Harley-style recursive code ********************/

DIRECT_LIM := 7;

/*
    Recursively solves for h the eqn Dy*Frob(h)+Dx*h+E=0
    to the precision prec of E,Dx,Dy - Dx=0 & Dy=2 mod p assumed
*/
function recurseA(E,Dx,Dy)

  R := Parent(E);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    r_fld, red := ResidueClassField(R);
//assert (red(Dx) eq 0) and (red(Dy) eq 2);
    v := E;
    inc_x := R!0;
    half := 1/r_fld!2;
    for i := 0 to prec - 1 do
      dx := R!Root(-red(v)*half,p);
      dy := GaloisImage(dx,1);
      inc_x +:= ShiftValuation(dx,i);
      if i lt prec-1 then
          v := ShiftValuation(v+Dx*dx+Dy*dy,-1);
      end if;
    end for;
    return inc_x;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // first recursion
    inc_x := R!recurseA(R1!E,R1!Dx,R1!Dy);
    inc_y := GaloisImage(inc_x,1);
    //update Eval
    tmp := ShiftValuation(E+Dx*inc_x+Dy*inc_y,-prec3);
    //second recursion
    ChangePrecision(~R1,prec2);
    inc_x1 := R!recurseA(R1!tmp,R1!Dx,R1!Dy);

    return inc_x+ShiftValuation(inc_x1,prec3);
  end if;

end function;

function hyp_recurse(t,s,pols)

  R := Parent(t);
  prec := Precision(R);
  if prec le DIRECT_LIM then
    p := Prime(R);
    _, red := ResidueClassField(R);
    spdt := Evaluate(pols`spd,red(t));
    sinv := 1/(u+u) where u is red(s);
    for i := 1 to prec - 1 do
	U := Evaluate(pols`U,t);
	B := Evaluate(pols`B,t);
	if i eq 1 then val := sinv*red(B); end if;
	f := Evaluate(pols`f,t);
	s +:= ShiftValuation(R!(sinv*tmp),i) where
	        tmp is red(ShiftValuation(f-s^2,-i));
	a,b := Explode([U-x,U+x]) where x is B*s;
	a :=red(ShiftValuation(GaloisImage(a,1)-b,-i));
	dt := Root(-a,p)/2;
	t +:= ShiftValuation(R!dt,i);
	s +:= ShiftValuation(R!(dt*spdt),i);
    end for;
    return t,s;
  else
    prec2 := prec div 2;
    prec3 := prec-prec2;
    R1 := ChangePrecision(R,prec3);
    // first recursion
    t,s := Explode([R!u,R!v]) where 
		u,v := hyp_recurse(R1!t,R1!s,pols);
    //compute new values to half precision
    ChangePrecision(~R1,prec2);
    sinv := 1 div (u+u) where u is R1!s;
    s +:= ShiftValuation(R!(sinv*tmp),prec3) where tmp is
	R1!ShiftValuation(Evaluate(pols`f,t)-s^2,-prec3);
    B := Evaluate(pols`B,t);
    U := Evaluate(pols`U,t);
    tmp1,tmp2 := Explode([U-x,U+x]) where x is B*s;
    E := R1!ShiftValuation(GaloisImage(tmp1,1)-tmp2,-prec3);
    B := R1!B;
    v := sinv*Evaluate(Derivative(pols`f),R1!t);
    Ud := Evaluate(Derivative(pols`U),R1!t);
    tmp1,tmp2 := Explode([-Ud-x,GaloisImage(Ud-x,1)]) where x is
	R1!s*R1!Evaluate(Derivative(pols`B),R1!t) + B*v;

    //second recursion
    dt := recurseA(E,tmp1,tmp2);
    return t+ShiftValuation(R!dt,prec3), 
			s+ShiftValuation(R!(dt*v),prec3);
  end if;

end function;


/************* END OF RECURSIVE HARLEY FUNCTIONS *****************/

function BasicGNBLift(t,s,pols,W)
  K := Parent(t);
  R := ChangePrecision(K,W);
  vprintf SEA,3: "Getting to initial precision %o.. ",W;
  tyme := Cputime();
   // W should be less DIRECT_LIM!
  t,s := hyp_recurse(R!t,R!s,pols);
  vprintf SEA,3 : "Time %o\n",Cputime()-tyme;
  return t,s;
end function;

/* 
   LERCIER/LUBITZ NEWTON LIFT METHOD.
   prec0 is the precision that the input t,s is correct to.
   precAdjs is the boolean list of adjustments to get to
   the final precision exactly:
   ie if precAdjs = [boo1,boo2,...], the precision sequence
      is  prec1 := 2*prec0 - (1 if boo1 else 0)
          prec2 := 2*prec1 - (1 if boo2 else 0)  ....
*/
function LercierLift(t,s,pols,prec0,precAdjs)

  K := Parent(t);
  p := Prime(K);
  n := Degree(K);

  prec := prec0;
  R := ChangePrecision(K,prec);
  t := R!t; s := R!s;
  for boo in precAdjs do

    precinc := prec - (boo select 1 else 0);
    vprintf SEA,4: "Increasing precision from %o to %o.. ",prec,prec+precinc;
    tyme := Cputime();
    R := ChangePrecision(K,prec+precinc);

    //x1 := R!x;
    //y := GaloisImage(x1,1);
    //Eval,Ex,Ey := E3(E,x1,y,Parent(x),prec);
    //Dyinv := (-Ey)^-1;
   
    R1 := ChangePrecision(Parent(t),precinc); 
    t := R!t; s := R!s;
    //compute E,Dx,Dy s.t. the t increment (p^prec)*h sats
    // Dy*Frob(h)=Dx*h+E mod p^precinc
    sinv := 1 div (u+u) where u is R1!s;
    s +:= ShiftValuation(R!(sinv*tmp),prec) where tmp is
	R1!ShiftValuation(Evaluate(pols`f,t)-s^2,-prec);
    B := Evaluate(pols`B,t);
    U := Evaluate(pols`U,t);
    tmp1,tmp2 := Explode([U-x,U+x]) where x is B*s;
    E := R1!ShiftValuation(GaloisImage(tmp1,1)-tmp2,-prec)
	      where tmp1,tmp2 := Explode([U-x,U+x]) 
		where x is B*s;
    B := R1!B;
    v := sinv*Evaluate(Derivative(pols`f),R1!t);
    Ud := Evaluate(Derivative(pols`U),R1!t);
    Dx,Dy := Explode([-Ud-x,GaloisImage(x-Ud,1)]) where x is
	R1!s*R1!Evaluate(Derivative(pols`B),R1!t) + B*v;
    Dyinv := Dy^(-1);

    a1 := Dx * Dyinv;
    b1 := E * Dyinv;
    
    exp := 1;
    seq := Prune(Intseq(precinc,2));
    a := a1;
    b := b1;

    for i := #seq to 1 by -1 do
      tmp := GaloisImage(a,exp);
      b := GaloisImage(b,exp) + tmp*b;
      a *:= tmp;
      exp *:= 2;
      if seq[i] eq 1 then
        tmp := GaloisImage(a,1);
        b := GaloisImage(b,1) + tmp*b1;
        a := a1*tmp;
        exp +:= 1;
      end if;
    end for;

    dt := GaloisImage(b,n-precinc);
    t := t + ShiftValuation(R!dt,prec);
    s := s + ShiftValuation(R!(dt*v),prec);
    prec +:= precinc;
    vprintf SEA,4 : "Time: %o\n",Cputime()-tyme;
    
  end for;

  return t,s;
  
end function;


function CanonicalLiftTraceMain(j)

  // j a non-supersingular jInv in GF(p^n), p odd. n>=3 is assumed!
  // The function returns +/- the trace of Frobenius on an ordinary
  // elliptic curve/GF(p^n) with that j invariant.

  vprint SEA, 1: "Computing trace via canonical lift.";
  tracetime := Cputime();
  n := Degree(Parent(j));
  p := Characteristic(Parent(j));

  precfin := Ceiling(n/2)+1;
  if (p lt 17) or IsEven(n) then precfin +:= 1; end if;

  vprintf SEA, 4: "Getting Modular Data. Time: ";
  tyme := Cputime();
  ind := Index(PRIMS,p);
  pols := rec< HypPols | f := R!FS[ind], U := R!US[ind], B := R!BS[ind],
	    sp := s, spd := Derivative(s) > where s is
	    PolynomialRing(GF(p))!SS[ind] where R is
		PolynomialRing(Integers());
  t := j+CS[ind];
  s := Evaluate(pols`sp,t);
  vprintf SEA, 4: "%o.\n",Cputime()-tyme;

  if n ge 3 then
    gnb_type := 1;
    R := pAdicQuotientRing(p,1);
    while gnb_type le 2 do //possible GNB types
     booGNB := HasGNB(R,n,gnb_type);
     if booGNB then break; end if;
     gnb_type +:= 1;
    end while;
  else
    booGNB := false;
  end if;
  if booGNB and (gnb_type eq 2) /*and (n le 50)*/ then
    booGNB := false;
  end if;
  // compute Norm(1+x) as exp(trace(log(1+x))) ?
  use_log := false; 


  if booGNB then  // will use GNB basis for local ring
    vprintf SEA, 1: "Working with Gaussian normal basis type %o\n",gnb_type;
    precmid := precfin;
    bAdjs := [Booleans()|];
    while precmid gt 3 do
      Append(~bAdjs,IsOdd(precmid));
      precmid := Ceiling(precmid/2);
    end while;
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    R := UnramifiedExtension(
	pAdicQuotientRing(p, precfin), n : GNBType := gnb_type
    );
    Embed(Parent(t),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;
    if GetVerbose("SEA") ge 3 then
      printf "\nPerforming basic lift\n";
      if #bAdjs gt 0 then printf "to reach precision %o.\n",precmid; end if;
      tyme := Cputime();
    end if;
    t,s := BasicGNBLift(R!t,R!s,pols,precmid);
    if #bAdjs gt 0 then
      vprint SEA, 3: "Beginning full NewtonLift phase.\n";
      Reverse(~bAdjs);
      t,s := LercierLift(R!t,R!s,pols,precmid,bAdjs);
    end if;
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
  else // will use non-Cyclotomic basis for local ring
    vprint SEA, 1: "Working with simple pAdic basis.";
    vprintf SEA, 2: "Constructing unramified p-adic extension. Time: ";
    tyme := Cputime();
    R := UnramifiedExtension(
	pAdicQuotientRing(p, precfin), n : Cyclotomic := false
      );
    Embed(Parent(t),ResidueClassField(R));
    vprintf SEA, 2: "%o.\n",Cputime()-tyme;
    vprintf SEA, 3: "Using Harley's recursive method.\n";
    tyme := Cputime();
    t,s := hyp_recurse(R!t,R!s,pols);
    vprintf SEA, 3: "Total lifting time: %o.\n",Cputime()-tyme;
  end if;

  vprint SEA,3 : "Computing norm.. ";
  tyme := Cputime();
  c := NormParam(t,s,pols,use_log);// precision reduced by 1 here!
  vprintf SEA, 3: "Time: %o.\n",Cputime()-tyme;
  c := Integers()!c;
  if c gt Isqrt(4*p^n) then
    c := c - p^(precfin-1);
  end if;

  vprintf SEA,1 : "Total trace time: %o\n",Cputime(tracetime);
  return c;
  
end function;

intrinsic ECCanonicalLiftTraceHyp(E::CrvEll) -> RngIntElt
{}
    return CanonicalLiftTraceMain(jInvariant(E));
end intrinsic;
