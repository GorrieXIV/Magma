
freeze;

function coeff_sym2_deg3(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2); c3:=Coefficient(ef,3);
  C1:=c1^2-c2; ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1^2*c2-c2^2-c1*c3; ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^3*c3+c2^3-4*c1*c2*c3+2*c3^2;
  ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c3*(c1*c2^2-4*c2*c3)+c3^2*(-c1^2+3*c2);
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=(c2^2-c1*c3)*c3^2; ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c3^4; return Polynomial([1,-C1,C2,-C3,C4,-C5,C6]); end function;

function coeff_sym3_deg3(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2); c3:=Coefficient(ef,3);
  C1:=c1^3-2*c1*c2+c3; ANS:=ANS+C1*T; if d eq 1 then return ANS; end if;
  C2:=c1^4*c2-3*c1^2*c2^2-c1^3*c3+2*c2^3+2*c1*c2*c3;
  ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^6*c3+c1^3*c2^3-7*c1^4*c2*c3-2*c1*c2^4+10*c1^2*c2^2*c3+
      5*c1^3*c3^2-11*c1*c2*c3^2+3*c3^3;
  ANS:=ANS+C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c1^5*c2^2*c3-c1^6*c3^2-3*c1^3*c2^3*c3+c1^4*c2*c3^2+c2^6-4*c1*c2^4*c3+
      13*c1^2*c2^2*c3^2-2*c1^3*c3^3+2*c2^3*c3^2-13*c1*c2*c3^3+3*c3^4;
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c3*(c1^5*c2^2*c3-c1^6*c3^2+c1^2*c2^5-8*c1^3*c2^3*c3+7*c1^4*c2*c3^2-c2^6+
          7*c1*c2^4*c3-5*c1^3*c3^3-5*c2^3*c3^2+4*c1*c2*c3^3);
  ANS:=ANS+C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c3^2*(c1^6*c3^2+c1^2*c2^5-3*c1^3*c2^3*c3-4*c1^4*c2*c3^2-c2^6+c1*c2^4*c3+
            13*c1^2*c2^2*c3^2+2*c1^3*c3^3-2*c2^3*c3^2-13*c1*c2*c3^3+3*c3^4);
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c3^3*(c1^3*c2^3*c3-2*c1^4*c2*c3^2+c2^6-7*c1*c2^4*c3+10*c1^2*c2^2*c3^2+
            5*c2^3*c3^2-11*c1*c2*c3^3+3*c3^4);
  ANS:=ANS+C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c3^5*(c1*c2^4-3*c1^2*c2^2*c3+2*c1^3*c3^2-c2^3*c3+2*c1*c2*c3^2);
  ANS:=ANS+C8*T^8; if d eq 8 then return ANS; end if;
  C9:=c3^7*(c2^3-2*c1*c2*c3+c3^2);
  ANS:=ANS+C9*T^9; if d eq 9 then return ANS; end if;
  C10:=c3^10;
  return Polynomial([1,C1,C2,C3,C4,C5,C6,C7,C8,C9,C10]); end function;

function coeff_sym4_deg3(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  _,c1,c2,c3:=Explode(Coefficients(ef));
  C1:=c1^4-3*c1^2*c2+c2^2+2*c1*c3;
  ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1^6*c2-5*c1^4*c2^2-c1^5*c3+7*c1^2*c2^3+
      6*c1^3*c2*c3-2*c2^4-8*c1*c2^2*c3-c1^2*c3^2+2*c2*c3^2;
  ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^9*c3+c1^6*c2^3-10*c1^7*c2*c3-5*c1^4*c2^4+31*c1^5*c2^2*c3+5*c3^4+
      8*c1^6*c3^2+7*c1^2*c2^5-31*c1^3*c2^3*c3-43*c1^4*c2*c3^2-2*c2^6+
      2*c1*c2^4*c3+57*c1^2*c2^2*c3^2+14*c1^3*c3^3-5*c2^3*c3^2-31*c1*c2*c3^3;
  ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c1^9*c2^2*c3-c1^10*c3^2-7*c1^7*c2^3*c3+5*c1^8*c2*c3^2+c1^4*c2^6+
      11*c1^5*c2^4*c3+8*c1^6*c2^2*c3^2-5*c1^7*c3^3-3*c1^2*c2^7+
      c1^3*c2^5*c3-42*c1^4*c2^3*c3^2-3*c1^5*c2*c3^3+c2^8+2*c1*c2^6*c3+
      4*c1^2*c2^4*c3^2+65*c1^3*c2^2*c3^3-c2^5*c3^2-9*c1*c2^3*c3^3
      -41*c1^2*c2*c3^4+2*c2^2*c3^4+8*c1*c3^5;
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c1^10*c2^2*c3^2-c1^11*c3^3+c1^7*c2^5*c3-13*c1^8*c2^3*c3^2+
      12*c1^9*c2*c3^3-5*c1^5*c2^6*c3+48*c1^6*c2^4*c3^2-31*c1^7*c2^2*c3^3
     -11*c1^8*c3^4+7*c1^3*c2^7*c3-61*c1^4*c2^5*c3^2-16*c1^5*c2^3*c3^3+
      66*c1^6*c2*c3^4+c2^10-12*c1*c2^8*c3+54*c1^2*c2^6*c3^2+
      40*c1^3*c2^4*c3^3-53*c1^4*c2^2*c3^4-28*c1^5*c3^5+7*c2^7*c3^2
     -81*c1*c2^5*c3^3+60*c1^2*c2^3*c3^4+29*c1^3*c2*c3^5+28*c2^4*c3^4
     -51*c1*c2^2*c3^5-2*c1^2*c3^6+8*c2*c3^6;
  ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c1^12*c3^4+c1^8*c2^5*c3^2-3*c1^9*c2^3*c3^3-10*c1^10*c2*c3^4
     -6*c1^6*c2^6*c3^2+15*c1^7*c2^4*c3^3+50*c1^8*c2^2*c3^4+7*c1^9*c3^5+
      c1^3*c2^9*c3+3*c1^4*c2^7*c3^2+8*c1^5*c2^5*c3^3-164*c1^6*c2^3*c3^4
     -57*c1^7*c2*c3^5-2*c1*c2^10*c3+9*c1^2*c2^8*c3^2-46*c1^3*c2^6*c3^3+
      173*c1^4*c2^4*c3^4+255*c1^5*c2^2*c3^5+15*c1^6*c3^6+3*c2^9*c3^2
     -21*c1*c2^7*c3^3+63*c1^2*c2^5*c3^4-377*c1^3*c2^3*c3^5-136*c1^4*c2*c3^6+
      13*c2^6*c3^4-27*c1*c2^4*c3^5+291*c1^2*c2^2*c3^6+23*c1^3*c3^7+
      4*c2^3*c3^6-93*c1*c2*c3^7+10*c3^8;
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c1^10*c2^3*c3^4-2*c1^11*c2*c3^5+c1^7*c2^6*c3^3-13*c1^8*c2^4*c3^4+
      21*c1^9*c2^2*c3^5+c1^10*c3^6+c1^4*c2^9*c3^2-13*c1^5*c2^7*c3^3+
      67*c1^6*c2^5*c3^4-72*c1^7*c2^3*c3^5-27*c1^8*c2*c3^6-3*c1^2*c2^10*c3^2+
      30*c1^3*c2^8*c3^3-101*c1^4*c2^6*c3^4+5*c1^5*c2^4*c3^5+
      166*c1^6*c2^2*c3^6+8*c1^7*c3^7+2*c2^11*c3^2-16*c1*c2^9*c3^3+
      15*c1^2*c2^7*c3^4+175*c1^3*c2^5*c3^5-200*c1^4*c2^3*c3^6-116*c1^5*c2*c3^7+
      14*c2^8*c3^4-65*c1*c2^6*c3^5-84*c1^2*c2^4*c3^6+206*c1^3*c2^2*c3^7+
      29*c1^4*c3^8+28*c2^5*c3^6+14*c1*c2^3*c3^7-81*c1^2*c2*c3^8+12*c1*c3^9;
  ANS:=ANS-C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c1^9*c2^4*c3^5-3*c1^10*c2^2*c3^6+2*c1^11*c3^7+c1^6*c2^7*c3^4
     -13*c1^7*c2^5*c3^5+30*c1^8*c2^3*c3^6-16*c1^9*c2*c3^7+c1^3*c2^10*c3^3
     -13*c1^4*c2^8*c3^4+67*c1^5*c2^6*c3^5-101*c1^6*c2^4*c3^6+
      15*c1^7*c2^2*c3^7+14*c1^8*c3^8-2*c1*c2^11*c3^3+21*c1^2*c2^9*c3^4
     -72*c1^3*c2^7*c3^5+5*c1^4*c2^5*c3^6+175*c1^5*c2^3*c3^7-65*c1^6*c2*c3^8+
      c2^10*c3^4-27*c1*c2^8*c3^5+166*c1^2*c2^6*c3^6-200*c1^3*c2^4*c3^7
     -84*c1^4*c2^2*c3^8+28*c1^5*c3^9+8*c2^7*c3^6-116*c1*c2^5*c3^7+
      206*c1^2*c2^3*c3^8+14*c1^3*c2*c3^9+29*c2^4*c3^8-81*c1*c2^2*c3^9+
      12*c2*c3^10;
  ANS:=ANS+C8*T^8; if d eq 8 then return ANS; end if;
  C9:=c1^9*c2^3*c3^7-2*c1^10*c2*c3^8+c1^5*c2^8*c3^5-6*c1^6*c2^6*c3^6+
      3*c1^7*c2^4*c3^7+9*c1^8*c2^2*c3^8+3*c1^9*c3^9-3*c1^3*c2^9*c3^5+
      15*c1^4*c2^7*c3^6+8*c1^5*c2^5*c3^7-46*c1^6*c2^3*c3^8-21*c1^7*c2*c3^9+
      c2^12*c3^4-10*c1*c2^10*c3^5+50*c1^2*c2^8*c3^6-164*c1^3*c2^6*c3^7+
      173*c1^4*c2^4*c3^8+63*c1^5*c2^2*c3^9+13*c1^6*c3^10+7*c2^9*c3^6
     -57*c1*c2^7*c3^7+255*c1^2*c2^5*c3^8-377*c1^3*c2^3*c3^9-27*c1^4*c2*c3^10+
      15*c2^6*c3^8-136*c1*c2^4*c3^9+291*c1^2*c2^2*c3^10+4*c1^3*c3^11+
      23*c2^3*c3^10-93*c1*c2*c3^11+10*c3^12;
  ANS:=ANS-C9*T^9; if d eq 9 then return ANS; end if;
  C10:=c1^10*c3^10+c1^5*c2^7*c3^7-5*c1^6*c2^5*c3^8+7*c1^7*c2^3*c3^9
      -12*c1^8*c2*c3^10+c1^2*c2^10*c3^6-13*c1^3*c2^8*c3^7+48*c1^4*c2^6*c3^8
      -61*c1^5*c2^4*c3^9+54*c1^6*c2^2*c3^10+7*c1^7*c3^11-c2^11*c3^6+
       12*c1*c2^9*c3^7-31*c1^2*c2^7*c3^8-16*c1^3*c2^5*c3^9+40*c1^4*c2^3*c3^10
      -81*c1^5*c2*c3^11-11*c2^8*c3^8+66*c1*c2^6*c3^9-53*c1^2*c2^4*c3^10+
       60*c1^3*c2^2*c3^11+28*c1^4*c3^12-28*c2^5*c3^10+29*c1*c2^3*c3^11
      -51*c1^2*c2*c3^12-2*c2^2*c3^12+8*c1*c3^13;
  ANS:=ANS+C10*T^10; if d eq 10 then return ANS; end if;
  C11:=c1^6*c2^4*c3^10-3*c1^7*c2^2*c3^11+c1^8*c3^12+c1^2*c2^9*c3^8
      -7*c1^3*c2^7*c3^9+11*c1^4*c2^5*c3^10+c1^5*c2^3*c3^11+2*c1^6*c2*c3^12
      -c2^10*c3^8+5*c1*c2^8*c3^9+8*c1^2*c2^6*c3^10-42*c1^3*c2^4*c3^11+
       4*c1^4*c2^2*c3^12-c1^5*c3^13-5*c2^7*c3^10-3*c1*c2^5*c3^11+
       65*c1^2*c2^3*c3^12-9*c1^3*c2*c3^13-41*c1*c2^2*c3^13+2*c1^2*c3^14+
       8*c2*c3^14;
  ANS:=ANS-C11*T^11; if d eq 11 then return ANS; end if;
  C12:=c1^3*c2^6*c3^11-5*c1^4*c2^4*c3^12+7*c1^5*c2^2*c3^13-2*c1^6*c3^14+
       c2^9*c3^10-10*c1*c2^7*c3^11+31*c1^2*c2^5*c3^12-31*c1^3*c2^3*c3^13+
       2*c1^4*c2*c3^14+8*c2^6*c3^12-43*c1*c2^4*c3^13+57*c1^2*c2^2*c3^14
      -5*c1^3*c3^15+14*c2^3*c3^14-31*c1*c2*c3^15+5*c3^16;
  ANS:=ANS+C12*T^12; if d eq 12 then return ANS; end if;
  C13:=c1*c2^6*c3^13-5*c1^2*c2^4*c3^14+7*c1^3*c2^2*c3^15-2*c1^4*c3^16
      -c2^5*c3^14+6*c1*c2^3*c3^15-8*c1^2*c2*c3^16-c2^2*c3^16+2*c1*c3^17;
  ANS:=ANS-C13*T^13; if d eq 13 then return ANS; end if;
  C14:=c2^4*c3^16-3*c1*c2^2*c3^17+c1^2*c3^18+2*c2*c3^18;
  ANS:=ANS+C14*T^14; if d eq 14 then return ANS; end if;
  C15:=c3^20; return Polynomial([1,-C1,C2,-C3,C4,-C5,C6,-C7,C8,-C9,C10,
				   -C11,C12,-C13,C14,-C15]); end function;

function euler_d3_symk(L,ef,p,d,m)
 if m eq 0 then return Polynomial([1,-1]); end if;
 if m eq 1 then return ef; end if;
 if m eq 2 then return coeff_sym2_deg3(L,ef,p,d); end if;
 if m eq 3 then return coeff_sym3_deg3(L,ef,p,d); end if;
 if m eq 4 then return coeff_sym4_deg3(L,ef,p,d); end if;
 assert false; end function;

function coeff_sym21_deg3(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2); c3:=Coefficient(ef,3);
  C1:=c1*c2-c3; ANS:=ANS+C1*T; if d eq 1 then return ANS; end if;
  C2:=c1^3*c3+c2^3-3*c1*c2*c3+c3^2;
  ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c3*(c1^2*c2^2-3*c3*c1*c2+2*c3^2);
  ANS:=ANS+C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c3^2*(2*c1^2*c2^2-2*c1^3*c3-2*c2^3+2*c1*c2*c3-2*c3^2);
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c3^3*(c1^2*c2^2-3*c1*c2*c3+2*c3^2);
  ANS:=ANS+C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c3^4*(c1^3*c3+c2^3-3*c1*c2*c3+c3^2);
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c3^6*(c1*c2-c3); ANS:=ANS+C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c3^8; return Polynomial([1,C1,C2,C3,C4,C5,C6,C7,C8]); end function;

function coeff_sym11_deg4(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2);
  c3:=Coefficient(ef,3); c4:=Coefficient(ef,4);
  C1:=c2; ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1*c3-c4; ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c3^2+c1^2*c4-2*c2*c4; ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c4*(c1*c3-c4); ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c2*c4^2; ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c4^3; return Polynomial([1,-C1,C2,-C3,C4,-C5,C6]); end function;

function coeff_sym2_deg4(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2);
  c3:=Coefficient(ef,3); c4:=Coefficient(ef,4);
  C1:=c1^2-c2; ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1^2*c2-c2^2-c1*c3+c4;
  ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^3*c3+c2^3-4*c1*c2*c3+2*c3^2;
  ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c1^4*c4+c1*c2^2*c3-c1^2*c3^2-4*c1^2*c2*c4-c2*c3^2+
      c2^2*c4+5*c1*c3*c4-2*c4^2;
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c1^2*c2^2*c4-c1^3*c3*c4+c2^2*c3^2-2*c2^3*c4-c1*c3^3+
      c1^2*c4^2+c3^2*c4+2*c2*c4^2;
  ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c1*c2^2*c3*c4-c1^2*c3^2*c4-c1^2*c2*c4^2+c3^4-4*c2*c3^2*c4+
      c2^2*c4^2+5*c1*c3*c4^2-2*c4^3;
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c4*(c2^3*c4+c1*c3^3-4*c1*c2*c3*c4+2*c1^2*c4^2);
  ANS:=ANS-C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c4^2*(c2*c3^2-c2^2*c4-c1*c3*c4+c4^2);
  ANS:=ANS+C8*T^8; if d eq 8 then return ANS; end if;
  C9:=c4^3*(c3^2-c2*c4); ANS:=ANS-C9*T^9; if d eq 9 then return ANS; end if;
  C10:=c4^5;
  return Polynomial([1,-C1,C2,-C3,C4,-C5,C6,-C7,C8,-C9,C10]); end function;

function coeff_sym22_deg4(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2);
  c3:=Coefficient(ef,3); c4:=Coefficient(ef,4);
  C1:=c2^2-c1*c3; ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1*c2^2*c3-c1^2*c3^2-c1^2*c2*c4-c2*c3^2+4*c1*c3*c4-2*c4^2;
  ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^2*c2^3*c4+c1^3*c3^3-4*c1^3*c2*c3*c4+2*c1^4*c4^2+c2^3*c3^2
     -2*c2^4*c4-4*c1*c2*c3^3+7*c1*c2^2*c3*c4+2*c1^2*c3^2*c4-3*c1^2*c2*c4^2+
      2*c3^4-3*c2*c3^2*c4+c2^2*c4^2-c1*c3*c4^2;
  ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c1^4*c2*c3^2*c4-c1^4*c2^2*c4^2-c1^5*c3*c4^2+c1*c2^4*c3*c4+c1^2*c2*c3^4
     -8*c1^2*c2^2*c3^2*c4+3*c1^2*c2^3*c4^2-2*c1^3*c3^3*c4+11*c1^3*c2*c3*c4^2
     -c1^4*c4^3-c2^2*c3^4+3*c2^3*c3^2*c4-3*c2^4*c4^2-c1*c3^5+11*c1*c2*c3^3*c4
     -8*c1*c2^2*c3*c4^2-5*c1^2*c3^2*c4^2-6*c1^2*c2*c4^3-c3^4*c4-6*c2*c3^2*c4^2+
      8*c2^2*c4^3+8*c1*c3*c4^3-3*c4^4;
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c1^6*c3^2*c4^2-c1^6*c2*c4^3+c1^3*c2^2*c3^3*c4-c1^3*c2^3*c3*c4^2
     -8*c1^4*c2*c3^2*c4^2+7*c1^4*c2^2*c4^3+c2^6*c4^2-c1*c2^3*c3^3*c4
     -4*c1*c2^4*c3*c4^2+c1^2*c3^6-8*c1^2*c2*c3^4*c4+27*c1^2*c2^2*c3^2*c4^2
     -8*c1^2*c2^3*c4^3+10*c1^3*c3^3*c4^2-13*c1^3*c2*c3*c4^3+c1^4*c4^4
     -c2*c3^6+7*c2^2*c3^4*c4-8*c2^3*c3^2*c4^2+2*c2^4*c4^3-13*c1*c2*c3^3*c4^2+
      c1*c2^2*c3*c4^3-12*c1^2*c3^2*c4^3+11*c1^2*c2*c4^4+c3^4*c4^2+
      11*c2*c3^2*c4^3-4*c2^2*c4^4+4*c1*c3*c4^4;
  ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c1^8*c4^4+c1^5*c2*c3^3*c4^2-c1^5*c2^2*c3*c4^3-c1^6*c3^2*c4^3
     -7*c1^6*c2*c4^4+c1^2*c2^4*c3^2*c4^2-c1^2*c2^5*c4^3+c1^3*c2*c3^5*c4
     -9*c1^3*c2^2*c3^3*c4^2+7*c1^3*c2^3*c3*c4^3-c1^4*c3^4*c4^2+
      7*c1^4*c2*c3^2*c4^3+15*c1^4*c2^2*c4^4+8*c1^5*c3*c4^4-c2^5*c3^2*c4^2+
      2*c2^6*c4^3-c1*c2^2*c3^5*c4+7*c1*c2^3*c3^3*c4^2-10*c1*c2^4*c3*c4^3
     -c1^2*c3^6*c4+7*c1^2*c2*c3^4*c4^2+5*c1^2*c2^2*c3^2*c4^3
     -12*c1^2*c2^3*c4^4-2*c1^3*c3^3*c4^3-46*c1^3*c2*c3*c4^4-3*c1^4*c4^5+
      c3^8-7*c2*c3^6*c4+15*c2^2*c3^4*c4^2-12*c2^3*c3^2*c4^3+2*c2^4*c4^4+
      8*c1*c3^5*c4^2-46*c1*c2*c3^3*c4^3+52*c1*c2^2*c3*c4^4+32*c1^2*c3^2*c4^4+
      16*c1^2*c2*c4^5-3*c3^4*c4^3+16*c2*c3^2*c4^4-16*c2^2*c4^5-32*c1*c3*c4^5+
      8*c4^6;
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c1^7*c2*c3*c4^4-c1^8*c4^5+c1^4*c2^3*c3^2*c4^3-c1^4*c2^4*c4^4+
      c1^5*c3^5*c4^2-4*c1^5*c2*c3^3*c4^3-4*c1^5*c2^2*c3*c4^4+
      c1^6*c3^2*c4^4+5*c1^6*c2*c4^5+c1^2*c2^3*c3^4*c4^2-5*c1^2*c2^4*c3^2*c4^3+
      4*c1^2*c2^5*c4^4-4*c1^3*c2*c3^5*c4^2+11*c1^3*c2^2*c3^3*c4^3+
      5*c1^3*c2^3*c3*c4^4-2*c1^4*c3^4*c4^3+14*c1^4*c2*c3^2*c4^4
     -8*c1^4*c2^2*c4^5-10*c1^5*c3*c4^5-c2^4*c3^4*c4^2+4*c2^5*c3^2*c4^3
     -3*c2^6*c4^4+c1*c2*c3^7*c4-4*c1*c2^2*c3^5*c4^2+5*c1*c2^3*c3^3*c4^3
     -4*c1*c2^4*c3*c4^4+c1^2*c3^6*c4^2+14*c1^2*c2*c3^4*c4^3
     -51*c1^2*c2^2*c3^2*c4^4+2*c1^2*c2^3*c4^5-8*c1^3*c3^3*c4^4+
      23*c1^3*c2*c3*c4^5+5*c1^4*c4^6-c3^8*c4+5*c2*c3^6*c4^2-8*c2^2*c3^4*c4^3+
      2*c2^3*c3^2*c4^4+6*c2^4*c4^5-10*c1*c3^5*c4^3+23*c1*c2*c3^3*c4^4+
      19*c1*c2^2*c3*c4^5-15*c1^2*c2*c4^6+5*c3^4*c4^4-15*c2*c3^2*c4^5
     -4*c2^2*c4^6+4*c1*c3*c4^6;
  ANS:=ANS-C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c1^6*c2^3*c4^5+c1^7*c3^3*c4^4-3*c1^7*c2*c3*c4^5+c1^8*c4^6+
      c1^4*c2^2*c3^4*c4^3-c1^4*c2^3*c3^2*c4^4-6*c1^4*c2^4*c4^5
     -9*c1^5*c2*c3^3*c4^4+20*c1^5*c2^2*c3*c4^5+c1^6*c3^2*c4^5
     -6*c1^6*c2*c4^6-c1^2*c2^3*c3^4*c4^3-2*c1^2*c2^4*c3^2*c4^4+
     12*c1^2*c2^5*c4^5+c1^3*c3^7*c4^2-9*c1^3*c2*c3^5*c4^3+
     32*c1^3*c2^2*c3^3*c4^4-32*c1^3*c2^3*c3*c4^5+12*c1^4*c3^4*c4^4
    -27*c1^4*c2*c3^2*c4^5+11*c1^4*c2^2*c4^6+5*c1^5*c3*c4^6+c2^3*c3^6*c4^2
    -6*c2^4*c3^4*c4^3+12*c2^5*c3^2*c4^4-8*c2^6*c4^5-3*c1*c2*c3^7*c4^2+
    20*c1*c2^2*c3^5*c4^3-32*c1*c2^3*c3^3*c4^4-c1*c2^4*c3*c4^5+c1^2*c3^6*c4^3
   -27*c1^2*c2*c3^4*c4^4+56*c1^2*c2^2*c3^2*c4^5-11*c1^2*c2^3*c4^6
   -14*c1^3*c3^3*c4^5+5*c1^3*c2*c3*c4^6-3*c1^4*c4^7+c3^8*c4^2
    -6*c2*c3^6*c4^3+11*c2^2*c3^4*c4^4-11*c2^3*c3^2*c4^5+19*c2^4*c4^6+
     5*c1*c3^5*c4^4+5*c1*c2*c3^3*c4^5-24*c1*c2^2*c3*c4^6+
    13*c1^2*c3^2*c4^6+6*c1^2*c2*c4^7-3*c3^4*c4^5+6*c2*c3^2*c4^6
    -8*c2^2*c4^7-8*c1*c3*c4^7+2*c4^8;
  ANS:=ANS+C8*T^8; if d eq 8 then return ANS; end if;
  C9:=c1^6*c2^2*c3^2*c4^5-3*c1^7*c2*c3*c4^6+2*c1^8*c4^7+2*c1^4*c2^2*c3^4*c4^4
    -9*c1^4*c2^3*c3^2*c4^5+c1^4*c2^4*c4^6-c1^5*c3^5*c4^4-2*c1^5*c2*c3^3*c4^5+
    20*c1^5*c2^2*c3*c4^6+2*c1^6*c3^2*c4^6-12*c1^6*c2*c4^7+c1^2*c2^2*c3^6*c4^3
    -9*c1^2*c2^3*c3^4*c4^4+21*c1^2*c2^4*c3^2*c4^5-4*c1^2*c2^5*c4^6
    -2*c1^3*c2*c3^5*c4^4+20*c1^3*c2^2*c3^3*c4^5-36*c1^3*c2^3*c3*c4^6+
    8*c1^4*c3^4*c4^5-30*c1^4*c2*c3^2*c4^6+17*c1^4*c2^2*c4^7+10*c1^5*c3*c4^7+
    c2^4*c3^4*c4^4-4*c2^5*c3^2*c4^5+2*c2^6*c4^6-3*c1*c2*c3^7*c4^3+
    20*c1*c2^2*c3^5*c4^4-36*c1*c2^3*c3^3*c4^5+8*c1*c2^4*c3*c4^6+
    2*c1^2*c3^6*c4^4-30*c1^2*c2*c3^4*c4^5+56*c1^2*c2^2*c3^2*c4^6+
    5*c1^2*c2^3*c4^7-3*c1^3*c3^3*c4^6-6*c1^3*c2*c3*c4^7-8*c1^4*c4^8+
    2*c3^8*c4^3-12*c2*c3^6*c4^4+17*c2^2*c3^4*c4^5+5*c2^3*c3^2*c4^6
    -6*c2^4*c4^7+10*c1*c3^5*c4^5-6*c1*c2*c3^3*c4^6-27*c1*c2^2*c3*c4^7+
    10*c1^2*c3^2*c4^7+7*c1^2*c2*c4^8-8*c3^4*c4^6+7*c2*c3^2*c4^7+
    6*c2^2*c4^8-6*c1*c3*c4^8;
  ANS:=ANS-C9*T^9; if d eq 9 then return ANS; end if;
  C10:=2*c1^6*c2^2*c3^2*c4^6-2*c1^6*c2^3*c4^7-2*c1^7*c3^3*c4^6+
    2*c1^7*c2*c3*c4^7-2*c1^8*c4^8+2*c1^4*c2^2*c3^4*c4^5-14*c1^4*c2^3*c3^2*c4^6+
    12*c1^4*c2^4*c4^7+4*c1^5*c2*c3^3*c4^6-6*c1^5*c2^2*c3*c4^7+8*c1^6*c3^2*c4^7+
    10*c1^6*c2*c4^8+2*c1^2*c2^2*c3^6*c4^4-14*c1^2*c2^3*c3^4*c4^5+
    34*c1^2*c2^4*c3^2*c4^6-22*c1^2*c2^5*c4^7-2*c1^3*c3^7*c4^4+
    4*c1^3*c2*c3^5*c4^5+18*c1^3*c2^2*c3^3*c4^6-14*c1^3*c2^3*c3*c4^7
    -10*c1^4*c3^4*c4^6-10*c1^4*c2*c3^2*c4^7-18*c1^4*c2^2*c4^8-24*c1^5*c3*c4^8
    -2*c2^3*c3^6*c4^4+12*c2^4*c3^4*c4^5-22*c2^5*c3^2*c4^6+12*c2^6*c4^7+
    2*c1*c2*c3^7*c4^4-6*c1*c2^2*c3^5*c4^5-14*c1*c2^3*c3^3*c4^6+
    20*c1*c2^4*c3*c4^7+8*c1^2*c3^6*c4^5-10*c1^2*c2*c3^4*c4^6
    -42*c1^2*c2^2*c3^2*c4^7+40*c1^2*c2^3*c4^8+36*c1^3*c3^3*c4^7+
    60*c1^3*c2*c3*c4^8+14*c1^4*c4^9-2*c3^8*c4^4+10*c2*c3^6*c4^5
    -18*c2^2*c3^4*c4^6+40*c2^3*c3^2*c4^7-36*c2^4*c4^8-24*c1*c3^5*c4^6+
    60*c1*c2*c3^3*c4^7-42*c1*c2^2*c3*c4^8-78*c1^2*c3^2*c4^8-30*c1^2*c2*c4^9+
    14*c3^4*c4^7-30*c2*c3^2*c4^8+32*c2^2*c4^9+56*c1*c3*c4^9-12*c4^10;
  ANS:=ANS+C10*T^10; if d eq 10 then return ANS; end if;
  C11:=c1^6*c2^2*c3^2*c4^7-3*c1^7*c2*c3*c4^8+2*c1^8*c4^9+
    2*c1^4*c2^2*c3^4*c4^6-9*c1^4*c2^3*c3^2*c4^7+c1^4*c2^4*c4^8
    -c1^5*c3^5*c4^6-2*c1^5*c2*c3^3*c4^7+20*c1^5*c2^2*c3*c4^8+2*c1^6*c3^2*c4^8
   -12*c1^6*c2*c4^9+c1^2*c2^2*c3^6*c4^5-9*c1^2*c2^3*c3^4*c4^6+
   21*c1^2*c2^4*c3^2*c4^7-4*c1^2*c2^5*c4^8-2*c1^3*c2*c3^5*c4^6+
   20*c1^3*c2^2*c3^3*c4^7-36*c1^3*c2^3*c3*c4^8+8*c1^4*c3^4*c4^7
   -30*c1^4*c2*c3^2*c4^8+17*c1^4*c2^2*c4^9+10*c1^5*c3*c4^9+c2^4*c3^4*c4^6
   -4*c2^5*c3^2*c4^7+2*c2^6*c4^8-3*c1*c2*c3^7*c4^5+20*c1*c2^2*c3^5*c4^6
   -36*c1*c2^3*c3^3*c4^7+8*c1*c2^4*c3*c4^8+2*c1^2*c3^6*c4^6
   -30*c1^2*c2*c3^4*c4^7+56*c1^2*c2^2*c3^2*c4^8+5*c1^2*c2^3*c4^9
   -3*c1^3*c3^3*c4^8-6*c1^3*c2*c3*c4^9-8*c1^4*c4^10+2*c3^8*c4^5
   -12*c2*c3^6*c4^6+17*c2^2*c3^4*c4^7+5*c2^3*c3^2*c4^8-6*c2^4*c4^9+
   10*c1*c3^5*c4^7-6*c1*c2*c3^3*c4^8-27*c1*c2^2*c3*c4^9+10*c1^2*c3^2*c4^9+
   7*c1^2*c2*c4^10-8*c3^4*c4^8+7*c2*c3^2*c4^9+6*c2^2*c4^10-6*c1*c3*c4^10;
  ANS:=ANS-C11*T^11; if d eq 11 then return ANS; end if;
  C12:=c1^6*c2^3*c4^9+c1^7*c3^3*c4^8-3*c1^7*c2*c3*c4^9+c1^8*c4^10+
    c1^4*c2^2*c3^4*c4^7-c1^4*c2^3*c3^2*c4^8-6*c1^4*c2^4*c4^9
   -9*c1^5*c2*c3^3*c4^8+20*c1^5*c2^2*c3*c4^9+c1^6*c3^2*c4^9-6*c1^6*c2*c4^10
   -c1^2*c2^3*c3^4*c4^7-2*c1^2*c2^4*c3^2*c4^8+12*c1^2*c2^5*c4^9+c1^3*c3^7*c4^6
   -9*c1^3*c2*c3^5*c4^7+32*c1^3*c2^2*c3^3*c4^8-32*c1^3*c2^3*c3*c4^9+
   12*c1^4*c3^4*c4^8-27*c1^4*c2*c3^2*c4^9+11*c1^4*c2^2*c4^10+5*c1^5*c3*c4^10+
   c2^3*c3^6*c4^6-6*c2^4*c3^4*c4^7+12*c2^5*c3^2*c4^8-8*c2^6*c4^9
   -3*c1*c2*c3^7*c4^6+20*c1*c2^2*c3^5*c4^7-32*c1*c2^3*c3^3*c4^8
   -c1*c2^4*c3*c4^9+c1^2*c3^6*c4^7-27*c1^2*c2*c3^4*c4^8+56*c1^2*c2^2*c3^2*c4^9
   -11*c1^2*c2^3*c4^10-14*c1^3*c3^3*c4^9+5*c1^3*c2*c3*c4^10-3*c1^4*c4^11+
   c3^8*c4^6-6*c2*c3^6*c4^7+11*c2^2*c3^4*c4^8-11*c2^3*c3^2*c4^9+19*c2^4*c4^10+
   5*c1*c3^5*c4^8+5*c1*c2*c3^3*c4^9-24*c1*c2^2*c3*c4^10+13*c1^2*c3^2*c4^10+
   6*c1^2*c2*c4^11-3*c3^4*c4^9+6*c2*c3^2*c4^10-8*c2^2*c4^11-8*c1*c3*c4^11+
   2*c4^12;
  ANS:=ANS+C12*T^12; if d eq 12 then return ANS; end if;
  C13:=c1^7*c2*c3*c4^10-c1^8*c4^11+c1^4*c2^3*c3^2*c4^9-c1^4*c2^4*c4^10+
    c1^5*c3^5*c4^8-4*c1^5*c2*c3^3*c4^9-4*c1^5*c2^2*c3*c4^10+c1^6*c3^2*c4^10+
    5*c1^6*c2*c4^11+c1^2*c2^3*c3^4*c4^8-5*c1^2*c2^4*c3^2*c4^9+
    4*c1^2*c2^5*c4^10-4*c1^3*c2*c3^5*c4^8+11*c1^3*c2^2*c3^3*c4^9+
    5*c1^3*c2^3*c3*c4^10-2*c1^4*c3^4*c4^9+14*c1^4*c2*c3^2*c4^10
    -8*c1^4*c2^2*c4^11-10*c1^5*c3*c4^11-c2^4*c3^4*c4^8+4*c2^5*c3^2*c4^9
    -3*c2^6*c4^10+c1*c2*c3^7*c4^7-4*c1*c2^2*c3^5*c4^8+5*c1*c2^3*c3^3*c4^9
    -4*c1*c2^4*c3*c4^10+c1^2*c3^6*c4^8+14*c1^2*c2*c3^4*c4^9
    -51*c1^2*c2^2*c3^2*c4^10+2*c1^2*c2^3*c4^11-8*c1^3*c3^3*c4^10+
    23*c1^3*c2*c3*c4^11+5*c1^4*c4^12-c3^8*c4^7+5*c2*c3^6*c4^8
    -8*c2^2*c3^4*c4^9+2*c2^3*c3^2*c4^10+6*c2^4*c4^11-10*c1*c3^5*c4^9+
    23*c1*c2*c3^3*c4^10+19*c1*c2^2*c3*c4^11-15*c1^2*c2*c4^12+5*c3^4*c4^10
    -15*c2*c3^2*c4^11-4*c2^2*c4^12+4*c1*c3*c4^12;
  ANS:=ANS-C13*T^13; if d eq 13 then return ANS; end if;
  C14:=c1^8*c4^12+c1^5*c2*c3^3*c4^10-c1^5*c2^2*c3*c4^11-c1^6*c3^2*c4^11
    -7*c1^6*c2*c4^12+c1^2*c2^4*c3^2*c4^10-c1^2*c2^5*c4^11+c1^3*c2*c3^5*c4^9
    -9*c1^3*c2^2*c3^3*c4^10+7*c1^3*c2^3*c3*c4^11-c1^4*c3^4*c4^10+
    7*c1^4*c2*c3^2*c4^11+15*c1^4*c2^2*c4^12+8*c1^5*c3*c4^12-c2^5*c3^2*c4^10+
    2*c2^6*c4^11-c1*c2^2*c3^5*c4^9+7*c1*c2^3*c3^3*c4^10-10*c1*c2^4*c3*c4^11
    -c1^2*c3^6*c4^9+7*c1^2*c2*c3^4*c4^10+5*c1^2*c2^2*c3^2*c4^11
   -12*c1^2*c2^3*c4^12-2*c1^3*c3^3*c4^11-46*c1^3*c2*c3*c4^12-3*c1^4*c4^13+
   c3^8*c4^8-7*c2*c3^6*c4^9+15*c2^2*c3^4*c4^10-12*c2^3*c3^2*c4^11+2*c2^4*c4^12+
   8*c1*c3^5*c4^10-46*c1*c2*c3^3*c4^11+52*c1*c2^2*c3*c4^12+32*c1^2*c3^2*c4^12+
   16*c1^2*c2*c4^13-3*c3^4*c4^11+16*c2*c3^2*c4^12-16*c2^2*c4^13-32*c1*c3*c4^13+
   8*c4^14;
  ANS:=ANS+C14*T^14; if d eq 14 then return ANS; end if;
  C15:=c1^6*c3^2*c4^12-c1^6*c2*c4^13+c1^3*c2^2*c3^3*c4^11-c1^3*c2^3*c3*c4^12
    -8*c1^4*c2*c3^2*c4^12+7*c1^4*c2^2*c4^13+c2^6*c4^12-c1*c2^3*c3^3*c4^11
    -4*c1*c2^4*c3*c4^12+c1^2*c3^6*c4^10-8*c1^2*c2*c3^4*c4^11+
    27*c1^2*c2^2*c3^2*c4^12-8*c1^2*c2^3*c4^13+10*c1^3*c3^3*c4^12
    -13*c1^3*c2*c3*c4^13+c1^4*c4^14-c2*c3^6*c4^10+7*c2^2*c3^4*c4^11
    -8*c2^3*c3^2*c4^12+2*c2^4*c4^13-13*c1*c2*c3^3*c4^12+c1*c2^2*c3*c4^13
    -12*c1^2*c3^2*c4^13+11*c1^2*c2*c4^14+c3^4*c4^12+11*c2*c3^2*c4^13
    -4*c2^2*c4^14+4*c1*c3*c4^14;
  ANS:=ANS-C15*T^15; if d eq 15 then return ANS; end if;
  C16:=c1^4*c2*c3^2*c4^13-c1^4*c2^2*c4^14-c1^5*c3*c4^14+c1*c2^4*c3*c4^13+
    c1^2*c2*c3^4*c4^12-8*c1^2*c2^2*c3^2*c4^13+3*c1^2*c2^3*c4^14
    -2*c1^3*c3^3*c4^13+11*c1^3*c2*c3*c4^14-c1^4*c4^15-c2^2*c3^4*c4^12+
    3*c2^3*c3^2*c4^13-3*c2^4*c4^14-c1*c3^5*c4^12+11*c1*c2*c3^3*c4^13
    -8*c1*c2^2*c3*c4^14-5*c1^2*c3^2*c4^14-6*c1^2*c2*c4^15-c3^4*c4^13
    -6*c2*c3^2*c4^14+8*c2^2*c4^15+8*c1*c3*c4^15-3*c4^16;
  ANS:=ANS+C16*T^16; if d eq 16 then return ANS; end if;
  C17:=c1^2*c2^3*c4^15+c1^3*c3^3*c4^14-4*c1^3*c2*c3*c4^15+2*c1^4*c4^16+
    c2^3*c3^2*c4^14-2*c2^4*c4^15-4*c1*c2*c3^3*c4^14+7*c1*c2^2*c3*c4^15+
    2*c1^2*c3^2*c4^15-3*c1^2*c2*c4^16+2*c3^4*c4^14-3*c2*c3^2*c4^15+
    c2^2*c4^16-c1*c3*c4^16;
  ANS:=ANS-C17*T^17; if d eq 17 then return ANS; end if;
  C18:=c1*c2^2*c3*c4^16-c1^2*c3^2*c4^16-c1^2*c2*c4^17-c2*c3^2*c4^16+
    4*c1*c3*c4^17-2*c4^18;
  ANS:=ANS+C18*T^18; if d eq 18 then return ANS; end if;
  C19:=c2^2*c4^18-c1*c3*c4^18;
  ANS:=ANS-C19*T^19; if d eq 19 then return ANS; end if;
  C20:=c4^20; f:=Polynomial([1,-C1,C2,-C3,C4,-C5,C6,-C7,C8,-C9,C10,
			       -C11,C12,-C13,C14,-C15,C16,-C17,C18,-C19,C20]);
  return f; end function;

function coeff_sym11_deg5(L,ef,p,d)
  BR:=BaseRing(ef); P:=PowerSeriesRing(BR,d+1); T:=P.1; ANS:=P!1;
  c1:=Coefficient(ef,1); c2:=Coefficient(ef,2);
  c3:=Coefficient(ef,3); c4:=Coefficient(ef,4); c5:=Coefficient(ef,5);
  C1:=c2; ANS:=ANS-C1*T; if d eq 1 then return ANS; end if;
  C2:=c1*c3-c4; ANS:=ANS+C2*T^2; if d eq 2 then return ANS; end if;
  C3:=c1^2*c4+c3^2-2*c2*c4-c1*c5;
  ANS:=ANS-C3*T^3; if d eq 3 then return ANS; end if;
  C4:=c1^3*c5+c1*c3*c4-3*c3*c5-3*c1*c2*c5-c4^2+4*c3*c5;
  ANS:=ANS+C4*T^4; if d eq 4 then return ANS; end if;
  C5:=c1^2*c3*c5+c2*c4^2-2*c2*c3*c5-2*c1*c4*c5+2*c5^2;
  ANS:=ANS-C5*T^5; if d eq 5 then return ANS; end if;
  C6:=c1*c2*c4*c5-c1^2*c5^2+c4^3-3*c3*c4*c5+c2*c5^2;
  ANS:=ANS+C6*T^6; if d eq 6 then return ANS; end if;
  C7:=c2^2*c5^2+c1*c4^2*c5-2*c1*c3*c5^2-c4*c5^2;
  ANS:=ANS-C7*T^7; if d eq 7 then return ANS; end if;
  C8:=c5^2*(c2*c4-c1*c5); ANS:=ANS+C8*T^8; if d eq 8 then return ANS; end if;
  C9:=c3*c5^3; ANS:=ANS-C9*T^9; if d eq 9 then return ANS; end if;
  C10:=c5^4;
  return Polynomial([1,-C1,C2,-C3,C4,-C5,C6,-C7,C8,-C9,C10]); end function;

