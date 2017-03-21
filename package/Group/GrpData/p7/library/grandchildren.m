freeze;

import "group6.0.m": Group6_0;

GrandChildren1 := function (p: Process := true, Select := func<x|true>)
   L := Group6_0 (p: Process := Process, Select := Select);
   if Type (L) ne BoolElt then 
      vprint Orderp7, 1: "Group 1 has 1 grandchild of order p^7";
   end if;
   return L;
end function;

import "group6.366.m": Group6_366;

GrandChildren2 := function (p: Process := true, Select := func<x|true>)
   L := Group6_366 (p : Process := Process, Select := Select);
   if Type (L) ne BoolElt then 
      vprint Orderp7, 1: "Group 2 has 4 grandchildren of order p^7";
   end if;
   return L;
end function;

import "group6.368.m": Group6_368;
import "group6.369.m": Group6_369;
import "group6.370.m": Group6_370;
import "group6.371.m": Group6_371;
import "group6.372.m": Group6_372;
import "group6.373.m": Group6_373;
import "group6.374.m": Group6_374;
import "group6.375.m": Group6_375;
import "group6.376.m": Group6_376;
import "group6.377.m": Group6_377;
import "group6.378.m": Group6_378;
import "group6.379.m": Group6_379;
import "group6.380.m": Group6_380;
import "group6.381.m": Group6_381;
import "group6.382.m": Group6_382;
import "group6.383.m": Group6_383;

GrandChildren3 := function (p: Process := true, Select := func<x|true>)

    if p lt 5 then "Only valid for p>3"; return []; end if;

    L := [];
    M := Group6_368 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_369 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_370 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_371 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_372 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_373 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_374 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_375 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_376 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_377 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_378 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_379 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_380 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_381 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_382 (p: Process := Process, Select := Select); Append (~L, M);
    M := Group6_383 (p: Process := Process, Select := Select); Append (~L, M);

    vprint Orderp7, 1: "Group 3 has 15p+41+16gcd(p-1,3)+4gcd(p-1,4) =",
                       15*p+41+16*Gcd(p-1,3)+4*Gcd(p-1,4),
                       "grandchildren of order p^7";
    return L;
end function;

import "group6.384.m": Group6_384;

GrandChildren4 := function (p: Process := true, Select := func<x|true>) 
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := Group6_384 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 4 has 2 grandchildren of order p^7";
   return L;
end function;

import "group6.386.m": Group6_386;
import "group6.388.m": Group6_388;

GrandChildren5 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then print "Only valid for p>3"; return []; end if;

   L := [];
   Append (~L, Group6_386 (p: Process := Process, Select := Select));
   Append (~L, Group6_388 (p: Process := Process, Select := Select));
   vprint Orderp7, 1: "Group 5 has 5p+10+2gcd(p-1,3)+gcd(p-1,4) =",
            5*p+10+2*Gcd(p-1,3)+Gcd(p-1,4),
           "grandchildren of order p^7";
   return L;
end function;

import "group6.394.m": Group6_394;
import "group6.399.m": Group6_399;
import "group6.404.m": Group6_404;

GrandChildren6 := function (p : Process := true, Select := func<x|true>)
   if p lt 7 then "Only valid for p>5"; return []; end if;

   L := [];
   M := Group6_394 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_399 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_404 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1:"Group 6 has p^3+3p^2+8p+18+5gcd(p-1,3)+(p+5)gcd(p-1,4)+3gcd(p-1,5)+ 2gcd(p-1,8)+gcd(p-1,9) =", 
   p^3+3*p^2+8*p+18+5*Gcd(p-1,3)+(p+5)*Gcd(p-1,4)+ 3*Gcd(p-1,5)+2*Gcd(p-1,8)+Gcd(p-1,9),
   "grandchildren of order p^7";

   return L;
end function;

import "group6.420.m": Group6_420;
import "group6.421.m": Group6_421;
import "group6.424.m": Group6_424;

GrandChildren7 := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then print "Only valid for p>5"; return []; end if;
   L := [];
   M := Group6_420 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_421 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_424 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 7 has 3p^2+4p+(p+1)gcd(p-1,3)+gcd(p-1,4) =",
    3*p^2+4*p+(p+1)*Gcd(p-1,3)+Gcd(p-1,4), "grandchildren of order p^7";

   return L;
end function;

import "group6.408.m": Group6_408;
import "group6.411.m": Group6_411;
import "group6.412.m": Group6_412;

GrandChildren8 := function (p : Process := true, Select := func<x|true>)

   if p lt 7 then print "Only valid for p>5"; return []; end if;

   L := [];
   M := Group6_408 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_411 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_412 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 8 has (p^2+2p+1+(p+5)gcd(p-1,3)+(p+3)gcd(p-1,4))/2 =",
  (p^2+2*p+1+(p+5)*Gcd(p-1,3)+(p+3)*Gcd(p-1,4))/2,"grandchildren of order p^7";
   return L;
end function;

import "group6.414.m": Group6_414;
import "group6.417.m": Group6_417;
import "group6.418.m": Group6_418;

GrandChildren9 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then print "Only valid for p>5"; return []; end if;

   L := [];
   M := Group6_414 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_417 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_418 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 9 has (p^2+2p+1+(p+5)gcd(p-1,3)+(p+3)gcd(p-1,4))/2 =",
  (p^2+2*p+1+(p+5)*Gcd(p-1,3)+(p+3)*Gcd(p-1,4))/2, "grandchildren of order p^7";

   return L;
end function;

import "group6.425.m": Group6_425;
import "group6.426.m": Group6_426;

GrandChildren10 := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then print "Only valid for p>5"; return []; end if;

   L := [];
   M := Group6_425 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_426 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 10 has p+3 =",p+3,"grandchildren of order p^7";
   return L;
end function;


import "group6.427.m": Group6_427;

GrandChildren11 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_427 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 11 has p+1 =",p+1,"grandchildren of order p^7";
   return L;
end function;

import "group6.428.m": Group6_428;

GrandChildren12 := function (p : Process := true, Select := func<x|true>)
   if p lt 7 then print "Only valid for p>5"; end if;
   L := Group6_428 (p: Process := Process, Select := Select);
   vprint Orderp7, 2: "Group 12 has 3 grandchildren of order p^7";
   return  L;
end function;

import "group6.431.m": Group6_431;

GrandChildren14 := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_431 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 14 has 4 grandchildren of order p^7";
   return  L;
end function;

import "group6.435.m": Group6_435;
import "group6.436.m": Group6_436;
import "group6.442.m": Group6_442;
import "group6.445.m": Group6_445;

GrandChildren15 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;

   L := []; 
   M := Group6_435 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_436 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_442 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_445 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 15 has 4p+5+(p+7)gcd(p-1,3)+3gcd(p-1,4)+2gcd(p-1,5) =",
   4*p+5+(p+7)*Gcd(p-1,3)+3*Gcd(p-1,4)+2*Gcd(p-1,5), "grandchildren of order p^7";
   return L;
end function;

import "group6.448.m": Group6_448;

GrandChildren16 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_448 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 16 has (p+1)/2 =",(p+1)/2,"grandchildren of order p^7";
   return L;
end function;

import "group6.451.m": Group6_451;

GrandChildren17 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_451 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 17 has (p+1)/2 =",(p+1)/2,"grandchildren of order p^7";
   return L;
end function;

import "group6.454.m": Group6_454;
import "group6.455.m": Group6_455;
import "group6.459.m": Group6_459;
import "group6.460.m": Group6_460;

GrandChildren18 := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := [];
   M := Group6_454 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_455 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_459 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_460 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 18 has 7p+9+4gcd(p-1,3)+6gcd(p-1,4)+2gcd(p-1,5) =",
   7*p+9+4*Gcd(p-1,3)+6*Gcd(p-1,4)+2*Gcd(p-1,5), "grandchildren of order p^7";
   return L;
end function;

import "group6.467.m": Group6_467;

GrandChildren19 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_467 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 19 has 2 grandchildren of order p^7";
   return L;
end function;

import "group6.518.m": Group6_518;

GrandChildren20 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_518 (p: Process := Process, Select := Select);

   vprint Orderp7, 1: "Group 20 has 2 grandchildren of order p^7";
   return L;
end function;

import "group6.469.m": Group6_469;
import "group6.475.m": Group6_475;

GrandChildren21 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;

   L := [];
   M := Group6_469 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_475 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 21 has 4p+3+2gcd(p-1,3)+4gcd(p-1,5)+gcd(p-1,7)+gcd(p-1,8) =",
   4*p+3+2*Gcd(p-1,3)+4*Gcd(p-1,5)+Gcd(p-1,7)+Gcd(p-1,8), 
   "grandchildren of order p^7";
  return L;
end function;

import "group6.507.m": Group6_507;

GrandChildren22  := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then "Only valid for p>5"; return []; end if;

   L := Group6_507 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 22 has 2p^2+p+2pgcd(p-1,3)+pgcd(p-1,5) =",
   2*p^2+p+2*p*Gcd(p-1,3)+p*Gcd(p-1,5), "grandchildren of order p^7";

   return L;
end function;

/* 3 */ import "group6.85.m":Group6_85;
/* 3 */ import "group6.86.m":Group6_86;
/* 3 */ import "group6.87.m":Group6_87;
/* 3 */ import "group6.88.m": Group6_88;
/* 3 */ import "group6.89.m": Group6_89;
/* 3 */ import "group6.90.m": Group6_90;
/* 3 */ import "group6.91.m": Group6_91;
/* 3 */ import "group6.92.m": Group6_92;
/* 3 */ import "group6.93.m": Group6_93;
/* 3 */ import "group6.94.m": Group6_94;
/* 3 */ import "group6.95.m": Group6_95;
/* 3 */ import "group6.96.m": Group6_96;
/* 3 */ import "group6.97.m": Group6_97;
/* 3 */ import "group6.98.m": Group6_98;
/* 3 */ import "group6.99.m": Group6_99;
/* 3 */ import "group6.100.m": Group6_100;
/* 3 */ import "group6.101.m": Group6_101;
/* 3 */ import "group6.102.m": Group6_102;
/* 3 */ import "group6.103.m": Group6_103;
/* 3 */ import "group6.104.m": Group6_104;
/* 3 */ import "group6.105.m": Group6_105;
/* 3 */ import "group6.106.m": Group6_106;
/* 3 */ import "group6.108.m": Group6_108;
/* 3 */ import "group6.109.m": Group6_109;
/* 3 */ import "group6.110.m": Group6_110;
/* 3 */ import "group6.111.m": Group6_111;
/* 3 */ import "group6.112.m": Group6_112;
/* 3 */ import "group6.113.m": Group6_113;
/* 3 */ import "group6.114.m": Group6_114;
/* 3 */ import "group6.115.m": Group6_115;
/* 3 */ import "group6.116.m": Group6_116;
/* 3 */ import "group6.117.m": Group6_117;

GrandChildren23 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_85 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_86 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_87 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_88 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_89 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_90 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_91 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_92 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_93 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_94 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_95 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_96 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_97 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_98 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_99 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_100 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_101 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_102 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_103 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_104 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_105 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_106 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_108 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_109 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_110 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_111 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_112 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_113 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_114 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_115 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_116 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_117 (p: Process := Process, Select := Select); Append (~L, M);

   vprint Orderp7, 1: "Group 23 has 2p^2+63p+362+(p+19)gcd(p-1,3)+5gcd(p-1,4)+gcd(p-1,5) =",
       2*p^2+63*p+362+(p+19)*Gcd(p-1,3)+5*Gcd(p-1,4)+Gcd(p-1,5),
      "grandchildren of order p^7";
   return L;
end function;

import "group6.118.m": Group6_118;
import "group6.119.m": Group6_119;
import "group6.120.m": Group6_120;
import "group6.121.m": Group6_121;
import "group6.122.m": Group6_122;
import "group6.125.m": Group6_125;
import "group6.127.m": Group6_127;
import "group6.131.m": Group6_131;
import "group6.132.m": Group6_132;
import "group6.133.m": Group6_133;
import "group6.134.m": Group6_134;
import "group6.135.m": Group6_135;
import "group6.138.m": Group6_138;
import "group6.139.m": Group6_139;
import "group6.140.m": Group6_140;
import "group6.142.m": Group6_142;
import "group6.143.m": Group6_143;
import "group6.144.m": Group6_144;
import "group6.146.m": Group6_146;
import "group6.148.m": Group6_148;
import "group6.150.m": Group6_150;
import "group6.151.m": Group6_151;
import "group6.152.m": Group6_152;
import "group6.153.m": Group6_153;
import "group6.154.m": Group6_154;
import "group6.155.m": Group6_155;
import "group6.156.m": Group6_156;
import "group6.157.m": Group6_157;
import "group6.158.m": Group6_158;
import "group6.159.m": Group6_159;
import "group6.160.m": Group6_160;
import "group6.160.m": Group6_160A;
import "group6.161.m": Group6_161;
import "group6.162.m": Group6_162;
import "group6.163.m": Group6_163;
import "group6.168.m": Group6_168;
import "group6.172.m": Group6_172;
import "group6.173.m": Group6_173;
import "group6.174.m": Group6_174;
import "group6.175.m": Group6_175;
import "group6.176.m": Group6_176;
import "group6.178.m": Group6_178;
import "group6.179.m": Group6_179;

GrandChildren24 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then print "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_118 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_119 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_120 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_121 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_122 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_125 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_127 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_131 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_132 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_133 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_134 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_135 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_138 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_139 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_140 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_142 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_143 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_144 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_146 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_148 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_150 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_151 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_152 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_153 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_154 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_155 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_156 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_157 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_158 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_159 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_160 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_160A (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_161 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_162 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_163 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_168 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_172 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_173 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_174 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_175 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_176 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_178 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_179 (p: Process := Process, Select := Select); Append (~L, M);

   vprint Orderp7, 1: "Group 24 has p^4+4p^3+17p^2+39p+72+(p^2+9p+47)gcd(p-1,3)+(2p+8)gcd(p-1,4)";
      "+2gcd(p-1,5)+gcd(p-1,7) =",
       p^4+4*p^3+17*p^2+39*p+72+(p^2+9*p+47)*Gcd(p-1,3)+
           (2*p+8)*Gcd(p-1,4)+2*Gcd(p-1,5)+Gcd(p-1,7),
      "grandchildren of order p^7";
   return L;
end function;

import "group6.182.m": Group6_182;
import "group6.183.m": Group6_183;

GrandChildren25 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_182 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_183 (p: Process := Process, Select := Select);
   Append (~L, M);
   vprint Orderp7, 1: "Group 25 has 6 grandchildren of order p^7";
   return L;
end function;

import "group6.184.m": Group6_184;
import "group6.187.m": Group6_187;
import "group6.188.m": Group6_188;
import "group6.189.m": Group6_189;
import "group6.190.m": Group6_190;
import "group6.191.m": Group6_191;
import "group6.192.m": Group6_192;
import "group6.197.m": Group6_197;
import "group6.198.m": Group6_198;

GrandChildren26 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_184 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_187 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_188 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_189 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_190 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_191 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_192 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_197 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_198 (p: Process := Process, Select := Select); Append (~L, M);

   vprint Orderp7, 1: "Group 26 has 5p+49+11gcd(p-1,3)+4gcd(p-1,4) =",
       5*p+49+11*Gcd(p-1,3)+4*Gcd(p-1,4), "grandchildren of order p^7";
   return L;
end function;

import "group6.207.m": Group6_207; 

GrandChildren27 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then print "Only valid for p>3"; end if;
   L := Group6_207 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 27 has 5 grandchildren of order p^7";
   return L;
end function;

import "group6.212.m": Group6_212;
import "group6.215.m": Group6_215;

GrandChildren28 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_212 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_215 (p: Process := Process, Select := Select);
   Append (~L, M);
   vprint Orderp7, 1: "Group 28 has 7 grandchildren of order p^7";
   return L;
end function;

import "group6.216.m": Group6_216;
import "group6.218.m": Group6_218;
import "group6.222.m": Group6_222;

GrandChildren29 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_216 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_218 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_222 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 29 has 2p+20+7gcd(p-1,3)+3gcd(p-1,4) =",
   2*p+20+7*Gcd(p-1,3)+3*Gcd(p-1,4), "grandchildren of order p^7";
   return L;
end function;

import "group6.228.m": Group6_228; 

GrandChildren30 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := Group6_228 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 30 has p+1 =",p+1,"grandchildren of order p^7";
   return L;
end function;

import "group6.231.m": Group6_231;
import "group6.256.m": Group6_256;
import "group6.261.m": Group6_261;

GrandChildren31 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_231 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_256 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_261 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 31 has p^2+9p+36+(p^2+5p+29)gcd(p-1,3)+(p+7)gcd(p-1,4)+gcd(p-1,7)";
      "+gcd(p-1,8) =",
       p^2+9*p+36+(p^2+5*p+29)*Gcd(p-1,3)+(p+7)*Gcd(p-1,4)+Gcd(p-1,7)+Gcd(p-1,8),
      "grandchildren of order p^7";
    return L;
end function;

import "group6.267.m": Group6_267;
import "group6.269.m": Group6_269;
import "group6.271.m": Group6_271;
import "group6.273.m": Group6_273;
import "group6.274.m": Group6_274;
import "group6.275.m": Group6_275;
import "group6.276.m": Group6_276;
import "group6.277.m": Group6_277;
import "group6.278.m": Group6_278;
import "group6.279.m": Group6_279;
import "group6.280.m": Group6_280;

GrandChildren32 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_267 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_269 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_271 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_273 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_274 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_275 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_276 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_277 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_278 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_279 (p: Process := Process, Select := Select); Append (~L, M);
   M := Group6_280 (p: Process := Process, Select := Select); Append (~L, M);

   vprint Orderp7, 1: "Group 32 has 10p+16+(2p+7)gcd(p-1,3)+2gcd(p-1,4)+2gcd(p-1,5) =",
   10*p+16+(2*p+7)*Gcd(p-1,3)+2*Gcd(p-1,4)+2*Gcd(p-1,5), "grandchildren of order p^7";
   return L;
end function;

import "group6.281.m": Group6_281;
import "group6.282.m": Group6_282;
import "group6.289.m": Group6_289;
import "group6.290.m": Group6_290;

GrandChildren33 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_281 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_282 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_289 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_290 (p: Process := Process, Select := Select);
   Append (~L, M);
   vprint Orderp7, 1: "Group 33 has p^3+5p^2+13p+6+3gcd(p-1,3) =",
       p^3+5*p^2+13*p+6+3*Gcd(p-1,3),"grandchildren of order p^7";
   return L;
end function;

import "group6.294.m": Group6_294;
import "group6.295.m": Group6_295;
import "group6.296.m": Group6_296;
import "group6.297.m": Group6_297;
import "group6.298.m": Group6_298;
import "group6.299.m": Group6_299;
import "group6.303.m": Group6_303;
import "group6.304.m": Group6_304;
import "group6.305.m": Group6_305;
import "group6.312.m": Group6_312;
import "group6.313.m": Group6_313;

GrandChildren34 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_294 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_295 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_296 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_297 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_298 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_299 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_303 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_304 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_305 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_312 (p : Process := Process, Select := Select); Append (~L, M);
   M := Group6_313 (p : Process := Process, Select := Select); Append (~L, M);

    vprint Orderp7, 1: "Group 34 has 2p^2+14p+10+(2p+8)gcd(p-1,3)+7gcd(p-1,4)+gcd(p-1,5) =",
       2*p^2+14*p+10+(2*p+8)*Gcd(p-1,3)+7*Gcd(p-1,4)+Gcd(p-1,5),
      "grandchildren of order p^7";
    return L;
end function;

import "group6.322.m":Group6_322;

GrandChildren36  := function (p: Process := true, Select := func<x|true>)
   if p lt 7 then "Only valid for p>5"; return []; end if;

   L := Group6_322 (p: Process := Process, Select := Select);

   vprint Orderp7, 1: "Group 36 has 3 grandchildren of order p^7";
   return L;
end function;

import "group6.325.m": Group6_325;
import "group6.326.m": Group6_326;
import "group6.327.m": Group6_327;
import "group6.328.m": Group6_328;

GrandChildren37 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := [];
   M := Group6_325 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_326 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_327 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_328 (p: Process := Process, Select := Select);
   Append (~L, M);

vprint Orderp7, 1: "Group 37 has p^2+10p+34+(p+14)gcd(p-1,3)+13gcd(p-1,4)+6gcd(p-1,5)+gcd(p-1,7) =",
       p^2+10*p+34+(p+14)*Gcd(p-1,3)+13*Gcd(p-1,4)+6*Gcd(p-1,5)+Gcd(p-1,7),
      "grandchildren of order p^7";
   return L;
end function;

import "group6.362.m":Group6_362;

GrandChildren38 := function (p: Process := true, Select := func<x|true>)

   if p lt 7 then "Only valid for p>5"; return []; end if;
   L := Group6_362 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 38 has p^2+7p+3+2gcd(p-1,3)+3gcd(p-1,4)+gcd(p-1,5) =",
       p^2+7*p+3+2*Gcd(p-1,3)+3*Gcd(p-1,4)+Gcd(p-1,5),
      "grandchildren of order p^7";
   return L;
end function;

/* 3 */ import "group6.9.m":Group6_9;
/* 3 */ import "group6.10.m":Group6_10;
/* 3 */ import "group6.11.m":Group6_11;
/* 3 */ import "group6.12.m":Group6_12;
/* 3 */ import "group6.13.m":Group6_13;
/* 3 */ import "group6.14.m":Group6_14;
/* 3 */ import "group6.15.m":Group6_15;
/* 3 */ import "group6.16.m":Group6_16;
/* 3 */ import "group6.17.m":Group6_17;
/* 3 */ import "group6.18.m":Group6_18;
/* 3 */ import "group6.19.m": Group6_19;
/* 3 */ import "group6.20.m":Group6_20;
/* 3 */ import "group6.21.m":Group6_21;
/* 3 */ import "group6.23.m":Group6_23;
/* 3 */ import "group6.24.m":Group6_24;
/* 3 */ import "group6.29.m":Group6_29;
/* 3 */ import "group6.33.m":Group6_33;
/* 3 */ import "group6.34.m":Group6_34;
/* 3 */ import "group6.35.m":Group6_35;
/* 3 */ import "group6.36.m":Group6_36;
/* 3 */ import "group6.48.m":Group6_48;
/* 3 */ import "group6.51.m":Group6_51;
/* 3 */ import "group6.52.m":Group6_52;
/* 3 */ import "group6.60.m":Group6_60;

GrandChildren39 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_9 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_10 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_11 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_12 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_13 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_14 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_15 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_16 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_17 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_18 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_19 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_20 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_21 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_23 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_24 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_29 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_33 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_34 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_35 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_36 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_48 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_51 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_52 (p:Process := Process, Select := Select); Append (~L, M);
   M := Group6_60 (p:Process := Process, Select := Select); Append (~L, M);

   vprint Orderp7, 1: "Group 39 has p^3+13p^2+96p+595+(3p+21)gcd(p-1,3)+(p+11)gcd(p-1,4)";
      "+gcd(p-1,5) =",
       p^3+13*p^2+96*p+595+(3*p+21)*Gcd(p-1,3)+(p+11)*Gcd(p-1,4)+Gcd(p-1,5),
      "grandchildren of order p^7";
   return L;
end function;

import "group6.63.m": Group6_63;

GrandChildren40 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := Group6_63 (p: Process := Process, Select := Select);
   vprint Orderp7, 1: "Group 40 has 4 grandchildren of order p^7";
   return L;
end function;

import "group6.67.m":Group6_67;
import "group6.72.m":Group6_72;

GrandChildren41 := function (p: Process := true, Select := func<x|true>)

   if p lt 5 then "Only valid for p>3"; return []; end if;

   L := [];
   M := Group6_67 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_72 (p: Process := Process, Select := Select);
   Append (~L, M);

   vprint Orderp7, 1: "Group 41 has 35+(p+15)gcd(p-1,3)+4gcd(p-1,4) =",
       35+(p+15)*Gcd(p-1,3)+4*Gcd(p-1,4),"grandchildren of order p^7";
                                                                                
   return L;
end function;

import "group6.2.m":Group6_2;
import "group6.3.m":Group6_3;

GrandChildren42 := function (p: Process := true, Select := func<x|true>)
   if p lt 5 then "Only valid for p>3"; return []; end if;
   L := [];
   M := Group6_2 (p: Process := Process, Select := Select);
   Append (~L, M);
   M := Group6_3 (p: Process := Process, Select := Select);
   Append (~L, M);
   vprint Orderp7, 1: "Group 42 has 30 grandchildren of order p^7";
   return L;
end function;
