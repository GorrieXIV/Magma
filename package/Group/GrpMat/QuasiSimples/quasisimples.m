freeze;

/* Intrinsic to return matrix groups arising from files in c9lins
 * database. We use the same group names as in the ATLAS database.
 */

forward MatGp;
intrinsic QuasisimpleMatrixGroup
          (name :: MonStgElt, dim :: RngIntElt, char :: RngIntElt :
             OverZ := "", Automorphisms:=false, RepNo:=-1, Print:=0) -> GrpMat
{Matrix group from quasisimple groups database}
   require char eq 0 or IsPrime(char) : "Characteristic must be 0 or a prime";
   return MatGp(name, dim, char : OverZ := OverZ,
             Automorphisms:=Automorphisms, RepNo:=RepNo, Print:=Print);
end intrinsic;

MatGp := function(name, d, char : OverZ := "", Print := 0,
                                     Automorphisms:=false, RepNo:=-1);
/* For characteristic 0, defaultfield is irreducible group over number field
 * of minimal dimension over Q.
 * If OverZ is true (defaultfield for char p?) write it over Z.
 * If automorphisms is true then the group G returned is extended by all
 * outer automorphisms that stabilise the module. This can result in
 * extra central elements.
 * RepNo is only needed if there is more than one equivalence classes
 * of representations with the same group and dimension
 * The default value of -1 means RepNo was not specified by the user.
 */
  
  if OverZ cmpeq "" then
    defaultfield := true;
    OverZ := char ne 0;
  else defaultfield := false;
  end if;
  param := <name,d,Abs(RepNo)>;
  //deal with A_n of degree n-1 generically for n>=7
  setfile := false;
  if name[1] eq "A" then
    n := StringToInteger(Substring(name,2,#name));
    if n ge 7 and d eq n-1 then
      if Abs(RepNo) ne 1 then
        error "There is only one such representation.";
      end if;
      Z := Integers();
      mat1 := PermutationMatrix(Z, Sym(n-1)!(1,2,3));
      L := rec < recformat< F: GrpFP, AI: SeqEnum, G: GrpMat > |
          F := FreeGroup(2) >;
      if IsOdd(n) then
         L`AI := [ [ a^-1, b ] ]
                     where a is (L`F).1 where b is (L`F).2;
         mat2 := MatrixAlgebra(Z,n-1)!0;
         mat2[1][1]:=1; mat2[2][2]:=1;
         for i in [1..n-1] do mat2[i][3]:= -1; end for;
         for i in [3..n-2] do mat2[i][i+1]:= 1; end for;
      else
         L`AI := [ [ a^-1, b*a^-1*(a,b)^2 ] ]
                     where a is (L`F).1 where b is (L`F).2;
         mat2 := MatrixAlgebra(Z,n-1)!0;
         mat2[1][1]:=1;
         for i in [1..n-1] do mat2[i][2]:= -1; end for;
         for i in [2..n-2] do mat2[i][i+1]:= 1; end for;
      end if;
      L`G := sub< GL(n-1,Integers()) | mat1, mat2 >;
      setfile := true;
    end if;
  end if;
     
  if not setfile then
    file := case < param |
//first batch are working up through group order
      <"A5",3,1>: "a5d3nf",
      <"A5",4,1>: "a5d4",
      <"A5",5,1>: "a5d5",
      <"2A5",2,1>: "sl25d2nf",
      <"2A5",4,1>: "sl25d4nf",
      <"2A5",6,1>: "sl25d6nf",
      <"L27",3,1>: "l27d3nf",
      <"L27",6,1>: "l27d6",
      <"L27",7,1>: "l27d7",
      <"L27",8,1>: "l27d8",
      <"2L27",4,1>: "sl27d4nf",
      <"2L27",6,1>: "sl27d6nf",
      <"2L27",8,1>: "sl27d8nf",
      <"A6",5,1>: "a6d5",
      <"A6",8,1>: "a6d8nf",
      <"A6",9,1>: "a6d9",
      <"A6",10,1>: "a6d10",
      <"2A6",4,1>: "2a6d4nf",
      <"2A6",8,1>: "2a6d8nf",
      <"2A6",10,1>: "2a6d10nf",
      <"3A6",3,1>: "3a6d3nf",
      <"3A6",6,1>: "3a6d6nf",
      <"3A6",9,1>: "3a6d9nf",
      <"3A6",15,1>: "3a6d15nf",
      <"6A6",6,1>: "6a6d6nf",
      <"6A6",12,1>: "6a6d12nf",
      <"L28",7,1>: "l28d7a",
      <"L28",7,2>: "l28d7bnf",
      <"L28",8,1>: "l28d8",
      <"L28",9,1>: "l28d9nf",
      <"L211",5,1>: "l211d5nf",
      <"L211",10,1>: "l211d10a",
      <"L211",10,2>: "l211d10b",
      <"L211",11,1>: "l211d11",
      <"L211",12,1>: "l211d12nf",
      <"2L211",6,1>: "sl211d6nf",
      <"2L211",10,1>: "sl211d10anf",
      <"2L211",10,2>: "sl211d10bnf",
      <"2L211",12,1>: "sl211d12nf",
      <"L213",7,1>: "l213d7nf",
      <"L213",12,1>: "l213d12nf",
      <"L213",13,1>: "l213d13",
      <"L213",14,1>: "l213d14a",
      <"L213",14,2>: "l213d14b",
      <"2L213",6,1>: "sl213d6nf",
      <"2L213",12,1>: "sl213d12nf",
      <"2L213",14,1>: "sl213d14anf",
      <"2L213",14,2>: "sl213d14bnf",
      <"L217",9,1>: "l217d9nf",
      <"L217",16,1>: "l217d16a",
      <"L217",16,2>: "l217d16bnf",
      <"L217",17,1>: "l217d17",
      <"L217",18,1>: "l217d18a",
      <"L217",18,2>: "l217d18bnf",
      <"2L217",8,1>: "sl217d8nf",
      <"2L217",16,1>: "sl217d16anf",
      <"2L217",16,2>: "sl217d16bnf",
      <"2L217",18,1>: "sl217d18nf",
      <"A7",6,1>: "a7d6",
      <"A7",10,1>: "a7d10nf",
      <"A7",14,1>: "a7d14a",
      <"A7",14,2>: "a7d14b",
      <"A7",15,1>: "a7d15",
      <"A7",21,1>: "a7d21",
      <"A7",35,1>: "a7d35",
      <"2A7",4,1>: "2a7d4nf",
      <"2A7",14,1>: "2a7d14nf",
      <"2A7",20,1>: "2a7d20anf",
      <"2A7",20,2>: "2a7d20bnf",
      <"2A7",36,1>: "2a7d36nf",
      <"3A7",6,1>: "3a7d6nf",
      <"3A7",15,1>: "3a7d15anf",
      <"3A7",15,2>: "3a7d15bnf",
      <"3A7",21,1>: "3a7d21anf",
      <"3A7",21,2>: "3a7d21bnf",
      <"3A7",24,1>: "3a7d24nf",
      <"6A7",6,1>: "6a7d6nf",
      <"6A7",24,1>: "6a7d24nf",
      <"6A7",36,1>: "6a7d36nf",
      <"L219",9,1>: "l219d9nf",
      <"L219",18,1>: "l219d18anf",
      <"L219",18,2>: "l219d18bnf",
      <"L219",19,1>: "l219d19",
      <"L219",20,1>: "l219d20a",
      <"L219",20,2>: "l219d20bnf",
      <"2L219",10,1>: "sl219d10nf",
      <"2L219",18,1>: "sl219d18anf",
      <"2L219",18,2>: "sl219d18bnf",
      <"2L219",20,1>: "sl219d20anf",
      <"2L219",20,2>: "sl219d20bnf",
      <"L216",15,1>: "l216d15nf",
      <"L216",16,1>: "l216d16",
      <"L216",17,1>: "l216d17a",
      <"L216",17,2>: "l216d17bnf",
      <"L216",17,3>: "l216d17cnf",
      <"L33",12,1>: "l33d12",
      <"L33",13,1>: "l33d13",
      <"L33",16,1>: "l33d16nf",
      <"L33",26,1>: "l33d26a",
      <"L33",26,2>: "l33d26bnf",
      <"L33",27,1>: "l33d27",
      <"L33",39,1>: "l33d39",
      <"U33",6,1>: "u33d6nf",
      <"U33",7,1>: "u33d7a",
      <"U33",7,2>: "u33d7bnf",
      <"U33",14,1>: "u33d14",
      <"U33",21,1>: "u33d21a",
      <"U33",21,2>: "u33d21bnf",
      <"U33",27,1>: "u33d27",
      <"U33",28,1>: "u33d28nf",
      <"U33",32,1>: "u33d32nf",
      <"L223",11,1>: "l223d11nf",
      <"L223",22,1>: "l223d22a",
      <"L223",22,2>: "l223d22b",
      <"L223",22,3>: "l223d22c",
      <"L223",22,4>: "l223d22dnf",
      <"L223",23,1>: "l223d23",
      <"L223",24,1>: "l223d24nf",
      <"2L223",12,1>: "sl223d12nf",
      <"2L223",22,1>: "sl223d22anf",
      <"2L223",22,2>: "sl223d22bnf",
      <"2L223",24,1>: "sl223d24nf",
      <"L225",13,1>: "l225d13",
      <"L225",24,1>: "l225d24nf",
      <"L225",25,1>: "l225d25",
      <"L225",26,1>: "l225d26a",
      <"L225",26,2>: "l225d26b",
      <"L225",26,3>: "l225d26c",
      <"L225",26,4>: "l225d26dnf",
      <"2L225",12,1>: "sl225d12nf",
      <"2L225",24,1>: "sl225d24nf",
      <"2L225",26,1>: "sl225d26anf",
      <"2L225",26,2>: "sl225d26bnf",
      <"M11",10,1>: "m11d10a",
      <"M11",10,2>: "m11d10bnf",
      <"M11",11,1>: "m11d11",
      <"M11",16,1>: "m11d16nf",
      <"M11",44,1>: "m11d44",
      <"M11",45,1>: "m11d45",
      <"M11",55,1>: "m11d55",
      <"L227",13,1>: "l227d13nf",
      <"L227",26,1>: "l227d26anf",
      <"L227",26,2>: "l227d26bnf",
      <"L227",27,1>: "l227d27",
      <"L227",28,1>: "l227d28nf",
      <"2L227",14,1>: "sl227d14nf",
      <"2L227",26,1>: "sl227d26anf",
      <"2L227",26,2>: "sl227d26bnf",
      <"2L227",28,1>: "sl227d28nf",
      <"L229",15,1>: "l229d15nf",
      <"L229",28,1>: "l229d28a",
      <"L229",28,2>: "l229d28bnf",
      <"L229",28,3>: "l229d28cnf",
      <"L229",29,1>: "l229d29",
      <"L229",30,1>: "l229d30anf",
      <"L229",30,2>: "l229d30bnf",
      <"2L229",14,1>: "sl229d14nf",
      <"2L229",28,1>: "sl229d28anf",
      <"2L229",28,2>: "sl229d28bnf",
      <"2L229",28,3>: "sl229d28cnf",
      <"2L229",30,1>: "sl229d30anf",
      <"2L229",30,2>: "sl229d30bnf",
      <"L231",15,1>: "l231d15nf",
      <"L231",30,1>: "l231d30a",
      <"L231",30,2>: "l231d30bnf",
      <"L231",30,3>: "l231d30cnf",
      <"L231",31,1>: "l231d31",
      <"L231",32,1>: "l231d32a",
      <"L231",32,2>: "l231d32bnf",
      <"L231",32,3>: "l231d32cnf",
      <"2L231",16,1>: "sl231d16nf",
      <"2L231",30,1>: "sl231d30nf",
      <"2L231",32,1>: "sl231d32anf",
      <"2L231",32,2>: "sl231d32bnf",
      <"2L231",32,3>: "sl231d32cnf",
      <"A8",7,1>: "a8d7",
      <"A8",14,1>: "a8d14",
      <"A8",20,1>: "a8d20",
      <"A8",21,1>: "a8d21a",
      <"A8",21,2>: "a8d21bnf",
      <"A8",28,1>: "a8d28",
      <"A8",35,1>: "a8d35",
      <"A8",45,1>: "a8d45",
      <"A8",56,1>: "a8d56",
      <"A8",64,1>: "a8d64",
      <"A8",70,1>: "a8d70",
      <"2A8",8,1>: "2a8d8",
      <"2A8",24,1>: "2a8d24nf",
      <"2A8",48,1>: "2a8d48nf",
      <"2A8",56,1>: "2a8d56nf",
      <"2A8",64,1>: "2a8d64nf",
      <"L34",20,1>: "l34d20",
      <"L34",35,1>: "l34d35",
      <"L34",45,1>: "l34d45",
      <"L34",63,1>: "l34d63nf",
      <"L34",64,1>: "l34d64",
      <"2L34",10,1>: "2l34d10nf",
      <"2L34",28,1>: "2l34d28nf",
      <"2L34",36,1>: "2l34d36",
      <"2L34",64,1>: "2l34d64",
      <"2L34",70,1>: "2l34d70",
      <"2L34",90,1>: "2l34d90",
      <"3L34",15,1>: "3l34d15nf",
      <"3L34",21,1>: "3l34d21nf",
      <"3L34",45,1>: "3l34d45nf",
      <"3L34",63,1>: "3l34d63nf",
      <"3L34",84,1>: "3l34d84nf",
      <"4aL34",8,1>: "4al34d8nf",
      <"4aL34",56,1>: "4al34d56nf",
      <"4aL34",64,1>: "4al34d64nf",
      <"4bL34",20,1>: "4bl34d20nf",
      <"4bL34",28,1>: "4bl34d28nf",
      <"4bL34",36,1>: "4bl34d36nf",
      <"4bL34",64,1>: "4bl34d64nf",
      <"4bL34",80,1>: "4bl34d80nf",
      <"6L34",6,1>: "6l34d6nf",
      <"6L34",36,1>: "6l34d36nf",
      <"6L34",42,1>: "6l34d42nf",
      <"6L34",60,1>: "6l34d60nf",
      <"6L34",90,1>: "6l34d90nf",
      <"12aL34",24,1>: "12al34d24nf",
      <"12aL34",48,1>: "12al34d48nf",
      <"12aL34",120,1>: "12al34d120nf",
      <"12bL34",36,1>: "12bl34d36nf",
      <"12bL34",48,1>: "12bl34d48nf",
      <"12bL34",60,1>: "12bl34d60nf",
      <"12bL34",84,1>: "12bl34d84nf",
      <"U42",5,1>: "u42d5nf",
      <"U42",6,1>: "u42d6",
      <"U42",10,1>: "u42d10nf",
      <"U42",15,1>: "u42d15a",
      <"U42",15,2>: "u42d15b",
      <"U42",20,1>: "u42d20",
      <"U42",24,1>: "u42d24",
      <"U42",30,1>: "u42d30a",
      <"U42",30,2>: "u42d30bnf",
      <"U42",40,1>: "u42d40nf",
      <"U42",45,1>: "u42d45nf",
      <"U42",60,1>: "u42d60",
      <"U42",64,1>: "u42d64",
      <"U42",81,1>: "u42d81",
      <"2U42",4,1>: "2u42d4nf",
      <"2U42",20,1>: "2u42d20anf",
      <"2U42",20,2>: "2u42d20bnf",
      <"2U42",20,3>: "2u42d20cnf",
      <"2U42",36,1>: "2u42d36nf",
      <"2U42",60,1>: "2u42d60anf",
      <"2U42",60,2>: "2u42d60bnf",
      <"2U42",64,1>: "2u42d64nf",
      <"2U42",80,1>: "2u42d80nf",
      <"Sz8",14,1>: "sz8d14nf",
      <"Sz8",35,1>: "sz8d35nf",
      <"Sz8",64,1>: "sz8d64",
      <"Sz8",65,1>: "sz8d65nf",
      <"Sz8",91,1>: "sz8d91",
      <"2Sz8",40,1>: "2sz8d40nf",
      <"2Sz8",56,1>: "2sz8d56nf",
      <"2Sz8",64,1>: "2sz8d64",
      <"2Sz8",104,1>: "2sz8d104",
      <"L232",31,1>: "l232d31a",
      <"L232",31,2>: "l232d31bnf",
      <"L232",31,3>: "l232d31cnf",
      <"L232",32,1>: "l232d32",
      <"L232",33,1>: "l232d33nf",
//now start working up by degree - omit A_n in dimension n-1
      <"6aU43",6,1>: "6au43d6nf",
      <"2J2",6,1>: "2j2d6nf",
      <"S62",7,1>: "s62d7",
      <"2A9",8,1>: "2a9d8",
      <"2S62",8,1>: "2s62d8",
      <"2O8p2",8,1>: "2o8+2d8",
      <"U52",10,1>: "u52d10nf",
      <"2M12",10,1>: "2m12d10nf",
      <"2M22",10,1>: "2m22d10nf",
      <"U52",11,1>: "u52d11nf",
      <"M12",11,1>: "m12d11",
      <"U34",12,1>: "u34d12nf",
      <"2S45",12,1>: "sp45d12nf",
      <"2G24",12,1>: "2g24d12nf",
      <"2M12",12,1>: "2m12d12",
      <"6Suz",12,1>: "6suzd12nf",
      <"U34",13,1>: "u34d13nf",
      <"S45",13,1>: "s45d13nf",
      <"S63",13,1>: "s63d13nf",
      <"2S63",14,1>: "sp63d14nf",
      <"G23",14,1>: "g23d14",
      <"2J2",14,1>: "2j2d14nf",
      <"J2",14,1>: "j2d14nf",
      <"3aU43",15,1>: "3au43d15nf",
      <"S62",15,1>: "s62d15",
      <"2A10",16,1>: "2a10d16",
      <"2A11",16,1>: "2a11d16nf",
      <"M12",16,1>: "m12d16nf",
      <"S44",18,1>: "s44d18",
      <"3J3",18,1>: "3j3d18nf",
      <"2L237",18,1>: "sl237d18nf",
      <"2L241",20,1>: "sl241d20nf",
      <"U35",20,1>: "u35d20nf",
      <"2U43",20,1>: "2u43d20nf",
      <"4U43",20,1>: "4u43d20nf",
      <"A9",21,1>: "a9d21nf",
      <"U35",21,1>: "u35d21",
      <"3U35",21,1>: "3u35d21anf",
      <"3U35",21,2>: "3u35d21bnf",
      <"3aU43",21,1>: "3au43d21nf",
      <"U43",21,1>: "u43d21",
      <"3U62",21,1>: "3u62d21nf",
      <"S62",21,1>: "s62d21a",
      <"S62",21,2>: "s62d21b",
      <"M22",21,1>: "m22d21",
      <"3M22",21,1>: "3m22d21nf",
      <"J2",21,1>: "j2d21nf",
      <"L241",21,1>: "l241d21nf",
      <"L243",21,1>: "l243d21nf",
      <"U62",22,1>: "u62d22",
      <"M23",22,1>: "m23d22",
      <"HS",22,1>: "hsd22",
      <"McL",22,1>: "mcld22",
      <"2L243",22,1>: "sl243d22nf",
      <"M24",23,1>: "m24d23",
      <"Co3",23,1>: "co3d23",
      <"Co2",23,1>: "co2d23",
      <"L247",23,1>: "l247d23nf",
      <"2L247",24,1>: "sl247d24nf",
      <"2L249",24,1>: "sl249d24nf",
      <"2Co1",24,1>: "2co1d24",
      <"2S47",24,1>: "sp47d24nf",
      <"L249",25,1>: "l249d25",
      <"S47",25,1>: "s47d25nf",
      <"L43",26,1>: "l43d26",
      <"TD42",26,1>: "t3d42d26",
      <"TF42",26,1>: "t2f42d26nf",
      <"A9",27,1>: "a9d27",
      <"S62",27,1>: "s62d27",
      <"3O73",27,1>: "3o73d27nf",
      <"3G23",27,1>: "3g23d27nf",
      <"TF42",27,1>: "t2f42d27nf",
      <"L253",27,1>: "l253d27nf",
      <"A9",28,1>: "a9d28",
      <"U35",28,1>: "u35d28",
      <"O8p2",28,1>: "o8+2d28",
      <"2Ru",28,1>: "2rud28nf",
      <"L259",29,1>: "l259d29nf",
      <"L35",30,1>: "l35d30",
      <"L52",30,1>: "l52d30",
      <"2L261",30,1>: "sl261d30",
      <"L35",31,1>: "l35d31a",
      <"L35",31,2>: "l35d31bnf",
      <"L261",31,1>: "l261d31nf",
      <"2A12",32,1>: "2a12d32nf",
      <"2M12",32,1>: "2m12d32nf",
      <"2A13",32,1>: "2a13d32nf",
      <"L267",33,1>: "l267d33nf",
      <"O8m2",34,1>: "o8-2d34",
      <"S44",34,1>: "s44d34",
      <"2L267",34,1>: "sl267d34nf",
      <"A9",35,1>: "a9d35",
      <"A10",35,1>: "a10d35",
      <"U43",35,1>: "u43d35",
      <"S62",35,1>: "s62d35a",
      <"S62",35,2>: "s62d35b",
      <"S82",35,1>: "s82d35",
      <"O8p2",35,1>: "o8+2d35",
      <"L271",35,1>: "l271d35nf",
      <"A10",36,1>: "a10d36",
      <"3bU43",36,1>: "3bu43d36nf",
      <"12bU43",36,1>: "12bu43d36nf",
      <"J2",36,1>: "j2d36",
      <"L237",36,1>: "l237d36nf",
      <"2L237",36,1>: "sl237d36nf",
      <"2L271",36,1>: "sl271d36nf",
      <"L237",37,1>: "l237d37",
      <"L237",38,1>: "l237d38a",
      <"L237",38,2>: "l237d38b",
      <"L237",38,3>: "l237d38cnf",
      <"L237",38,4>: "l237d38dnf",
      <"2L237",38,1>: "sl237d38anf",
      <"2L237",38,2>: "sl237d38bnf",
      <"2L237",38,3>: "sl237d38cnf",
      <"L279",39,1>: "l279d39nf",
      <"L43",39,1>: "l43d39",
      <"U34",39,1>: "u34d39nf",
      <"L241",40,1>: "l241d40a",
      <"L241",40,2>: "l241d40bnf",
      <"L241",40,3>: "l241d40cnf",
      <"2L241",40,1>: "sl241d40anf",
      <"2L241",40,2>: "sl241d40bnf",
      <"2L241",40,3>: "sl241d40cnf",
      <"2L279",40,1>: "sl279d40nf",
      <"2L281",40,1>: "sl281d40nf",
      <"2L43",40,1>: "2l43d40",
      <"S45",40,1>: "s45d40",
      <"2S49",40,1>: "sp49d40nf",
      <"2S83",40,1>: "sp83d40nf",
      <"L241",41,1>: "l241d41",
      <"L281",41,1>: "l281d41",
      <"L283",41,1>: "l283d41",
      <"S49",41,1>: "s49d41",
      <"S83",41,1>: "s83d41nf",
      <"A9",42,1>: "a9d42",
      <"A10",42,1>: "a10d42",
      <"U37",42,1>: "u37d42nf",
      <"U72",42,1>: "u72d42nf",
      <"L241",42,1>: "l241d42a",
      <"L241",42,2>: "l241d42b",
      <"L241",42,3>: "l241d42c",
      <"U37",43,1>: "u37d43a",
      <"U37",43,2>: "u37d43bnf",
      <"U72",43,1>: "u72d43nf",
      <"L243",43,1>: "l243d43",
      <"L243",44,1>: "l243d44",
      <"A11",44,1>: "a11d44",
      <"2M12",44,1>: "2m12d44",
      <"U52",44,1>: "u52d44",
      <"L289",45,1>: "l289d45",
      <"A11",45,1>: "a11d45",
      <"3bU43",45,1>: "3bu43d45",
      <"M12",45,1>: "m12d45",
      <"M22",45,1>: "m22d45nf",
      <"3M22",45,1>: "3m22d45nf",
      <"M23",45,1>: "m23d45nf",
      <"M24",45,1>: "m24d45nf",
      <"L247",46,1>: "l247d46a",
      <"L247",46,2>: "l247d46b",
      <"L247",46,3>: "l247d46c",
      <"L247",46,4>: "l247d46d",
      <"L247",46,5>: "l247d46e",
      <"L247",47,1>: "l247d47",
      <"2A8",48,1>: "2a8d48nf",
      <"A9",48,1>: "a9d48",
      <"2A9",48,1>: "2a9d48nf",
      <"2A10",48,1>: "2a10d48nf",
      <"3U35",48,1>: "3u35d48nf",
      <"2S62",48,1>: "2s62d48",
      <"L249",48,1>: "l249d48",
      <"L297",49,1>: "l297d49",
      <"L249",49,1>: "l249d49",
      <"L249",50,1>: "l249d50a",
      <"L249",50,2>: "l249d50b",
      <"L249",50,3>: "l249d50c",
      <"L249",50,4>: "l249d50d",
      <"L249",50,5>: "l249d50e",
      <"S44",50,1>: "s44d50",
      <"O8p2",50,1>: "o8+2d50",
      <"2J2",50,1>: "2j2d50nf",
      <"U44",51,1>: "u44d51nf",
      <"S44",51,1>: "s44d51nf",
      <"S82",51,1>: "s82d51",
      <"O8m2",51,1>: "o8-2d51",
      <"He",51,1>: "hed51nf",
      <"L253",52,1>: "l253d52",
      <"L43",52,1>: "l43d52",
      <"U34",52,1>: "u34d52nf",
      <"U44",52,1>: "u44d52",
      <"2S45",52,1>: "sp45d52nf",
      <"TD42",52,1>: "t3d42d52",
      <"2F42",52,1>: "2f42d52",
      <"L253",53,1>: "l253d53",
      <"A12",54,1>: "a12d54",
      <"M12",54,1>: "m12d54",
      <"A12",55,1>: "a12d55",
      <"M12",55,1>: "m12d55a",
      <"M12",55,2>: "m12d55b",
      <"M22",55,1>: "m22d55",
      <"U52",55,1>: "u52d55a",
      <"U52",55,2>: "u52d55bnf",
      <"A9",56,1>: "a9d56",
      <"2A9",56,1>: "2a9d56",
      <"L37",56,1>: "l37d56",
      <"U38",56,1>: "u38d56nf",
      <"2U43",56,1>: "2u43d56",
      <"2U62",56,1>: "2u62d56",
      <"S62",56,1>: "s62d56",
      <"2O8p2",56,1>: "2o8+2d56",
      <"2M22",56,1>: "2m22d56",
      <"4M22",56,1>: "4m22d56nf",
      <"J1",56,1>: "j1d56nf",
      <"2J2",56,1>: "2j2d56nf",
      <"2HS",56,1>: "2hsd56",
      <"L37",57,1>: "l37d57",
      <"3L37",57,1>: "3l37d57nf",
      <"U38",57,1>: "u38d57nf",
      <"3U38",57,1>: "3u38d57nf",
      <"L259",58,1>: "l259d58a",
      <"L259",58,2>: "l259d58b",
      <"L259",58,3>: "l259d58c",
      <"L259",59,1>: "l259d59",
      <"U53",60,1>: "u53d60nf",
      <"2S411",60,1>: "sp411d60nf",
      <"L261",61,1>: "l261d61",
      <"L2121",61,1>: "l2121d61",
      <"U53",61,1>: "u53d61",
      <"S411",61,1>: "s411d61nf",
      <"L261",62,1>: "l261d62a",
      <"L261",62,2>: "l261d62b",
      <"L62",62,1>: "l62d62",
      <"2S65",62,1>: "sp65d62nf",
      <"S65",63,1>: "s65d63nf",
      <"J2",63,1>: "j2d63",
      <"L264",64,1>: "l264d64",
      <"2A10",64,1>: "2a10d64",
      <"2A14",64,1>: "2a14d64nf",
      <"2A15",64,1>: "2a15d64nf",
      <"U34",64,1>: "u34d64",
      <"2S62",64,1>: "2s62d64nf",
      <"G23",64,1>: "g23d64nf",
      <"2J2",64,1>: "2j2d64nf",
      <"L264",65,1>: "l264d65",
      <"A13",65,1>: "a13d65",
      <"L43",65,1>: "l43d65",
      <"S45",65,1>: "s45d65a",
      <"S45",65,2>: "s45d65b",
      <"U34",65,1>: "u34d65",
      <"G24",65,1>: "g24d65",
      <"A13",66,1>: "a13d66",
      <"M12",66,1>: "m12d66",
      <"U52",66,1>: "u52d66nf",
      <"6M22",66,1>: "6m22d66nf",
      <"3Suz",66,1>: "3suzd66nf",
      <"L267",67,1>: "l267d67",
      <"L267",68,1>: "l267d68",
      <"L271",70,1>: "l271d70a",
      <"L271",70,2>: "l271d70b",
      <"L271",70,3>: "l271d70c",
      <"2U43",70,1>: "2u43d70a",
      <"2U43",70,2>: "2u43d70bnf",
      <"2U43",70,3>: "2u43d70cnf",
      <"S62",70,1>: "s62d70",
      <"J2",70,1>: "j2d70nf",
      <"L271",71,1>: "l271d71",
      <"L38",72,1>: "l38d72",
      <"U39",73,1>: "u39d73a",
      <"U39",73,2>: "u39d73bnf",
      <"L38",73,1>: "l38d73nf",
      <"L273",73,1>: "l273d73",
      <"L273",74,1>: "l273d74a",
      <"L273",74,2>: "l273d74b",
      <"L273",74,3>: "l273d74c",
      <"A10",75,1>: "a10d75",
      <"U34",75,1>: "u34d75nf",
      <"J1",76,1>: "j1d76a",
      <"J1",76,2>: "j1d76b",
      <"A14",77,1>: "a14d77",
      <"J1",77,1>: "j1d77a",
      <"J1",77,2>: "j1d77bnf",
      <"HS",77,1>: "hsd77",
      <"A14",78,1>: "a14d78",
      <"S45",78,1>: "s45d78nf",
      <"S63",78,1>: "s63d78",
      <"O73",78,1>: "o73d78",
      <"G23",78,1>: "g23d78",
      <"G24",78,1>: "g24d78",
      <"TF42",78,1>: "t2f42d78",
      <"3Suz",78,1>: "3suzd78nf",
      <"Fi22",78,1>: "fi22d78",
      <"L279",78,1>: "l279d78",
      <"L279",79,1>: "l279d79",
      <"L279",80,1>: "l279d80",
      <"L281",81,1>: "l281d81",
      <"L281",82,1>: "l281d82",
      <"L283",82,1>: "l283d82a",
      <"L283",82,2>: "l283d82b",
      <"L283",83,1>: "l283d83",
      <"A9",84,1>: "a9d84",
      <"A10",84,1>: "a10d84",
      <"L44",84,1>: "l44d84",
      <"U35",84,1>: "u35d84",
      <"S62",84,1>: "s62d84",
      <"O8p2",84,1>: "o8+2d84",
      <"O8m2",84,1>: "o8-2d84",
      <"2J2",84,1>: "2j2d84nf",
      <"2S413",84,1>: "sp413d84nf",
      <"6aU43",84,1>: "6au43d84nf",
      <"12aU43",84,1>: "12au43d84nf",
      <"L2169",85,1>: "l2169d85",
      <"L44",85,1>: "l44d85nf",
      <"U82",85,1>: "u82d85nf",
      <"S44",85,1>: "s44d85",
      <"S413",85,1>: "s413d85nf",
      <"S82",85,1>: "s82d85",
      <"J3",85,1>: "j3d85nf",
      <"U82",86,1>: "u82d86",
      <"L289",88,1>: "l289d88",
      <"L289",89,1>: "l289d89",
      <"A10",90,1>: "a10d90",
      <"A15",90,1>: "a15d90",
      <"6bU43",90,1>: "6bu43d90nf",
      <"S45",90,1>: "s45d90",
      <"J2",90,1>: "j2d90",
      <"L289",90,1>: "l289d90",
      <"L39",90,1>: "l39d90",
      <"L43",90,1>: "l43d90",
      <"U43",90,1>: "u43d90",
      <"A15",91,1>: "a15d91",
      <"L39",91,1>: "l39d91a",
      <"L39",91,2>: "l39d91bnf",
      <"L39",91,3>: "l39d91cnf",
      <"G23",91,1>: "g23d91a",
      <"G23",91,2>: "g23d91b",
      <"S63",91,1>: "s63d91nf",
      <"O73",91,1>: "o73d91",
      <"L35",96,1>: "l35d96nf",
      <"3L37",96,1>: "3l37d96nf",
      <"L297",97,1>: "l297d97",
      <"L297",98,1>: "l297d98a",
      <"L297",98,2>: "l297d98b",
      <"L297",98,3>: "l297d98c",
      <"M12",99,1>: "m12d99",
      <"M22",99,1>: "m22d99",
      <"3M22",99,1>: "3m22d99nf",
      <"L2101",100,1>: "l2101d100",
      default: "" >;
  
    param := <name,d>;
    ngps := case < param |
        <"L28",7>: 2,
        <"L211",10>: 2,
        <"2L211",10>: 2,
        <"L213",14>: 2,
        <"2L213",14>: 2,
        <"L217",16>: 2,
        <"L217",18>: 2,
        <"2L217",16>: 2,
        <"2L213",16>: 2,
        <"A7",14>: 2,
        <"2A7",20>: 2,
        <"3A7",15>: 2,
        <"3A7",21>: 2,
        <"L219",18>: 2,
        <"L219",20>: 2,
        <"2L219",18>: 2,
        <"2L219",20>: 2,
        <"L216",17>: 3,
        <"L33",26>: 2,
        <"U33",7>: 2,
        <"U33",21>: 2,
        <"L223",22>: 4,
        <"2L223",22>: 2,
        <"L225",26>: 4,
        <"2L225",26>: 2,
        <"M11",10>: 2,
        <"L227",26>: 2,
        <"2L227",26>: 2,
        <"L229",28>: 3,
        <"L229",30>: 2,
        <"2L229",28>: 3,
        <"2L229",30>: 2,
        <"L231",30>: 3,
        <"L231",32>: 3,
        <"2L231",32>: 3,
        <"A8",21>: 2,
        <"U42",15>: 2,
        <"U42",30>: 2,
        <"U42",20>: 3,
        <"2U42",60>: 2,
        <"L232",31>: 3,
        <"3U35",21>: 2,
        <"S62",21>: 2,
        <"L35",31>: 2,
        <"S62",35>: 2,
        <"L237",38>: 4,
        <"2L237",38>: 3,
        <"L241",40>: 3,
        <"L241",42>: 3,
        <"U37",43>: 2,
        <"L247",46>: 5,
        <"L249",50>: 5,
        <"M12",55>: 2,
        <"U52",55>: 2,
        <"L259",58>: 3,
        <"L261",62>: 2,
        <"S45",65>: 2,
        <"L271",70>: 3,
        <"2U43",70>: 2,
        <"U39",73>: 2,
        <"L273",74>: 3,
        <"J1",76>: 2,
        <"J1",77>: 2,
        <"L283",82>: 2,
        <"L39",91>: 3,
        <"G23",91>: 2,
        <"L297",98>: 3,
        default: 1 >; //should have RepNo <= ngps

    if file eq "" then
      error
      "There is no quasisimple group with that name and dimension in database.
QuasisimpleMatrixGroups() returns a list of group names, with dimensions and
number of representations.";
    end if;
  
    if ngps gt 1 and RepNo eq -1 then
     "There are", ngps, "groups with this name and dimension.";
     "Use the optional RepNo parameter to specify groups other than the first.";
    end if;
  
    if RepNo gt ngps then
      error "There are only",ngps,
              "quasisimple groups with that name and dimension in database";
    end if;

    c9lib := GetLibraryRoot() cat "/c9lattices/";
  
    if OverZ and Substring(file,#file-1,#file) eq "nf" then
      nfile := Substring(file,1,#file-2);
      //check if representation over Z exists
      try _:=Open(c9lib cat nfile,"r"); file:=nfile; catch e; end try;
    end if;
    if Print gt 0 then "Reading from file:",file; end if;
  
    L := eval Read(c9lib cat file);
  end if; //if not setfile then

  G := L`G;
  K := BaseRing(G);
  assert (d eq Dimension(G)) or
                (K cmpeq Integers() and Dimension(G) mod d eq 0);
  M := GModule(G);

  if char ne 0 then
    p := char;
    assert IsPrime(p);
    if K cmpeq Integers() then
     G := sub< GL(Dimension(G), p) | G.1, G.2 >;
     M := GModule(G);
    else
      f := Factorisation(ideal<MaximalOrder(K)|p>);
      M := Evaluate(M, f[1][1]);
      G := ActionGroup(M);
    end if;
    K := BaseRing(G);
    if not IsIrreducible(M) then
      C := Constituents(M);
      M := Random([ c : c in C | Dimension(c) gt 1 ]);
      M := AbsolutelyIrreducibleModule(M);
      G := ActionGroup(M);
      if Dimension(M) ne d then
        d := Dimension(M);
        print "Warning: module reducible in this characteristic";
        print "Using constituent of dimension", d;
      end if;
    elif not IsAbsolutelyIrreducible(M) then
      M := AbsolutelyIrreducibleModule(M);
      G := ActionGroup(M);
      K := BaseRing(G);
      if Dimension(M) ne d then
        d := Dimension(M);
        print "Warning: module absolutely reducible in this characteristic";
        print "Rewriting in dimension", d;
      end if;
    end if;
    iss, GG := IsOverSmallerField(G);
    if iss then
      print "Writing over smaller field";
      G := GG;
      K := BaseRing(G);
      M := GModule(G);
    end if;
  elif defaultfield and d ne Dimension(M) then //char = 0
    print "Warning: representation over number field unavailable.";
    print "Using integral representation in dimension", Dimension(M);
  end if;

  if not Automorphisms then
    return G;
  end if;

  //The file should contain groups automorphisms generating the module
  //stabiliser
  AI := L`AI;
  F := L`F;
  if K cmpeq Integers() then
    d := Dimension(M);
    K := Rationals();
    G := sub< GL(d, K) | G.1, G.2 >;
    M := GModule(G);
  end if;
  phi := hom< F->G | G.1, G.2 >;
  gens := [ Generic(G) | G.1, G.2];
  for a in AI do
    M2 := GModule(G, [phi(a[1]),phi(a[2])]);
    isiso, mat := IsIsomorphic(M, M2);
    if Print gt 0 then "automorphism fixed module:", isiso; end if;
    if isiso then
      mat := Generic(G)!mat;
      if char ne 0 then //try and reduce order of mat
        f1 := Factorisation(Order(mat));
        f2 := Factorisation(ProjectiveOrder(mat));
        pow := 1;
        for f in f1 do if not f[1] in {x[1]:x in f2} then
          pow *:= f[1]^f[2];
        end if; end for;
        mat := mat^pow;
      end if;
      Append(~gens, mat);
    end if;
  end for;
  return sub< Generic(G) | gens >;
end function;

intrinsic QuasisimpleMatrixGroups() -> SeqEnum
{list of group names with dimensions and number of representations}
return
      [<"2A5",2,1>,
      <"3A6",3,1>,
      <"A5",3,1>,
      <"L27",3,1>,
      <"2A5",4,1>,
      <"2A6",4,1>,
      <"2A7",4,1>,
      <"2L27",4,1>,
      <"2U42",4,1>,
      <"A5",4,1>,
      <"A5",5,1>,
      <"A6",5,1>,
      <"L211",5,1>,
      <"U42",5,1>,
      <"2A5",6,1>,
      <"2J2",6,1>,
      <"2L211",6,1>,
      <"2L213",6,1>,
      <"2L27",6,1>,
      <"3A6",6,1>,
      <"3A7",6,1>,
      <"6A6",6,1>,
      <"6A7",6,1>,
      <"6aU43",6,1>,
      <"6L34",6,1>,
      <"A7",6,1>,
      <"L27",6,1>,
      <"U33",6,1>,
      <"U42",6,1>,
      <"A8",7,1>,
      <"L213",7,1>,
      <"L27",7,1>,
      <"S62",7,1>,
      <"L28",7,2>,
      <"U33",7,2>,
      <"2A6",8,1>,
      <"2A8",8,1>,
      <"2A9",8,1>,
      <"2L217",8,1>,
      <"2L27",8,1>,
      <"2O8p2",8,1>,
      <"2S62",8,1>,
      <"4aL34",8,1>,
      <"A6",8,1>,
      <"L27",8,1>,
      <"L28",8,1>,
      <"3A6",9,1>,
      <"A6",9,1>,
      <"L217",9,1>,
      <"L219",9,1>,
      <"L28",9,1>,
      <"2A6",10,1>,
      <"2L219",10,1>,
      <"2L34",10,1>,
      <"2M12",10,1>,
      <"2M22",10,1>,
      <"A6",10,1>,
      <"A7",10,1>,
      <"U42",10,1>,
      <"U52",10,1>,
      <"2L211",10,2>,
      <"L211",10,2>,
      <"M11",10,2>,
      <"L211",11,1>,
      <"L223",11,1>,
      <"M11",11,1>,
      <"M12",11,1>,
      <"U52",11,1>,
      <"2G24",12,1>,
      <"2L211",12,1>,
      <"2L213",12,1>,
      <"2L223",12,1>,
      <"2L225",12,1>,
      <"2M12",12,1>,
      <"2S45",12,1>,
      <"6A6",12,1>,
      <"6Suz",12,1>,
      <"L211",12,1>,
      <"L213",12,1>,
      <"L33",12,1>,
      <"U34",12,1>,
      <"L213",13,1>,
      <"L225",13,1>,
      <"L227",13,1>,
      <"L33",13,1>,
      <"S45",13,1>,
      <"S63",13,1>,
      <"U34",13,1>,
      <"2A7",14,1>,
      <"J2",14,1>,
      <"2J2",14,1>,
      <"2L227",14,1>,
      <"2L229",14,1>,
      <"2S63",14,1>,
      <"A8",14,1>,
      <"G23",14,1>,
      <"Sz8",14,1>,
      <"U33",14,1>,
      <"2L213",14,2>,
      <"A7",14,2>,
      <"L213",14,2>,
      <"3A6",15,1>,
      <"3aU43",15,1>,
      <"3L34",15,1>,
      <"A7",15,1>,
      <"L216",15,1>,
      <"L229",15,1>,
      <"L231",15,1>,
      <"S62",15,1>,
      <"3A7",15,2>,
      <"U42",15,2>,
      <"2A10",16,1>,
      <"2A11",16,1>,
      <"2L231",16,1>,
      <"L216",16,1>,
      <"L33",16,1>,
      <"M11",16,1>,
      <"M12",16,1>,
      <"2L217",16,2>,
      <"L217",16,2>,
      <"L217",17,1>,
      <"L216",17,3>,
      <"2L217",18,1>,
      <"2L237",18,1>,
      <"3J3",18,1>,
      <"S44",18,1>,
      <"2L219",18,2>,
      <"L217",18,2>,
      <"L219",18,2>,
      <"L219",19,1>,
      <"2L241",20,1>,
      <"2U43",20,1>,
      <"4bL34",20,1>,
      <"4U43",20,1>,
      <"A8",20,1>,
      <"L34",20,1>,
      <"U35",20,1>,
      <"U42",20,1>,
      <"2A7",20,2>,
      <"2L219",20,2>,
      <"L219",20,2>,
      <"2U42",20,3>,
      <"3aU43",21,1>,
      <"U43",21,1>,
      <"3L34",21,1>,
      <"3M22",21,1>,
      <"3U35",21,1>,
      <"3U62",21,1>,
      <"A7",21,1>,
      <"A9",21,1>,
      <"J2",21,1>,
      <"M22",21,1>,
      <"U35",21,1>,
      <"3A7",21,2>,
      <"3U35",21,2>,
      <"A8",21,2>,
      <"S62",21,2>,
      <"U33",21,2>,
      <"L241",21,1>,
      <"L243",21,1>,
      <"HS",22,1>,
      <"M23",22,1>,
      <"McL",22,1>,
      <"U62",22,1>,
      <"2L223",22,2>,
      <"L223",22,4>,
      <"2L243",22,1>,
      <"Co2",23,1>,
      <"Co3",23,1>,
      <"L223",23,1>,
      <"M24",23,1>,
      <"L247",23,1>,
      <"12aL34",24,1>,
      <"2A8",24,1>,
      <"2Co1",24,1>,
      <"2L223",24,1>,
      <"2L225",24,1>,
      <"2L247",24,1>,
      <"2L249",24,1>,
      <"2S47",24,1>,
      <"3A7",24,1>,
      <"6A7",24,1>,
      <"L223",24,1>,
      <"L225",24,1>,
      <"U42",24,1>,
      <"L225",25,1>,
      <"L249",25,1>,
      <"S47",25,1>,
      <"L43",26,1>,
      <"TD42",26,1>,
      <"TF42",26,1>,
      <"2L225",26,2>,
      <"2L227",26,2>,
      <"L227",26,2>,
      <"L33",26,2>,
      <"L225",26,4>,
      <"3G23",27,1>,
      <"3O73",27,1>,
      <"A9",27,1>,
      <"L227",27,1>,
      <"L33",27,1>,
      <"S62",27,1>,
      <"TF42",27,1>,
      <"U33",27,1>,
      <"L253",27,1>,
      <"2L227",28,1>,
      <"2L34",28,1>,
      <"2Ru",28,1>,
      <"4bL34",28,1>,
      <"A8",28,1>,
      <"A9",28,1>,
      <"L227",28,1>,
      <"O8p2",28,1>,
      <"U33",28,1>,
      <"U35",28,1>,
      <"2L229",28,3>,
      <"L229",28,3>,
      <"L229",29,1>,
      <"L259",29,1>,
      <"2L231",30,1>,
      <"2L261",30,1>,
      <"L35",30,1>,
      <"L52",30,1>,
      <"2L229",30,2>,
      <"L229",30,2>,
      <"U42",30,2>,
      <"L231",30,3>,
      <"L231",31,1>,
      <"L261",31,1>,
      <"L35",31,2>,
      <"L232",31,3>,
      <"2A12",32,1>,
      <"2A13",32,1>,
      <"2M12",32,1>,
      <"L232",32,1>,
      <"U33",32,1>,
      <"2L231",32,3>,
      <"L231",32,3>,
      <"L232",33,1>,
      <"L267",33,1>,
      <"2L267",34,1>,
      <"O8m2",34,1>,
      <"S44",34,1>,
      <"A10",35,1>,
      <"A7",35,1>,
      <"A8",35,1>,
      <"A9",35,1>,
      <"L271",35,1>,
      <"L34",35,1>,
      <"O8p2",35,1>,
      <"S82",35,1>,
      <"Sz8",35,1>,
      <"U43",35,1>,
      <"S62",35,2>,
      <"12bL34",36,1>,
      <"12bU43",36,1>,
      <"2A7",36,1>,
      <"2L237",36,1>,
      <"2L271",36,1>,
      <"2L34",36,1>,
      <"2U42",36,1>,
      <"3bU43",36,1>,
      <"4bL34",36,1>,
      <"6A7",36,1>,
      <"6L34",36,1>,
      <"A10",36,1>,
      <"J2",36,1>,
      <"L237",36,1>,
      <"L237",37,1>,
      <"2L237",38,3>,
      <"L237",38,4>,
      <"L279",39,1>,
      <"L33",39,1>,
      <"L43",39,1>,
      <"U34",39,1>,
      <"2L279",40,1>,
      <"2L281",40,1>,
      <"2L43",40,1>,
      <"2S49",40,1>,
      <"2S83",40,1>,
      <"2Sz8",40,1>,
      <"S45",40,1>,
      <"U42",40,1>,
      <"2L241",40,3>,
      <"L241",40,3>,
      <"L241",41,1>,
      <"L281",41,1>,
      <"L283",41,1>,
      <"S49",41,1>,
      <"S83",41,1>,
      <"6L34",42,1>,
      <"A10",42,1>,
      <"A9",42,1>,
      <"L241",42,3>,
      <"U37",42,1>,
      <"U72",42,1>,
      <"U72",43,1>,
      <"U37",43,2>,
      <"L243",43,1>,
      <"L243",44,1>,
      <"2M12",44,1>,
      <"A11",44,1>,
      <"M11",44,1>,
      <"M11",45,1>,
      <"U52",44,1>,
      <"3L34",45,1>,
      <"A11",45,1>,
      <"A8",45,1>,
      <"L34",45,1>,
      <"M11",45,1>,
      <"3bU43",45,1>,
      <"M12",45,1>,
      <"M22",45,1>,
      <"3M22",45,1>,
      <"M23",45,1>,
      <"M24",45,1>,
      <"U42",45,1>,
      <"L289",45,1>,
      <"L247",46,5>,
      <"L247",47,1>,
      <"L249",48,1>,
      <"12aL34",48,1>,
      <"12bL34",48,1>,
      <"2A10",48,1>,
      <"2A8",48,1>,
      <"2A8",48,1>,
      <"2A9",48,1>,
      <"2S62",48,1>,
      <"3U35",48,1>,
      <"A9",48,1>,
      <"L249",49,1>,
      <"L297",49,1>,
      <"L249",50,5>,
      <"2J2",50,1>,
      <"O8p2",50,1>,
      <"S44",50,1>,
      <"He",51,1>,
      <"O8m2",51,1>,
      <"S44",51,1>,
      <"S82",51,1>,
      <"U44",51,1>,
      <"2F42",52,1>,
      <"2S45",52,1>,
      <"L43",52,1>,
      <"TD42",52,1>,
      <"U34",52,1>,
      <"U44",52,1>,
      <"L253",52,1>,
      <"L253",53,1>,
      <"A12",54,1>,
      <"M12",54,1>,
      <"A12",55,1>,
      <"M11",55,1>,
      <"M11",55,1>,
      <"M22",55,1>,
      <"M12",55,2>,
      <"U52",55,2>,
      <"2A8",56,1>,
      <"2A9",56,1>,
      <"2HS",56,1>,
      <"2J2",56,1>,
      <"2M22",56,1>,
      <"2O8p2",56,1>,
      <"2Sz8",56,1>,
      <"2U43",56,1>,
      <"2U62",56,1>,
      <"4aL34",56,1>,
      <"4M22",56,1>,
      <"A8",56,1>,
      <"A9",56,1>,
      <"J1",56,1>,
      <"L37",56,1>,
      <"S62",56,1>,
      <"U38",56,1>,
      <"3L37",57,1>,
      <"3U38",57,1>,
      <"L37",57,1>,
      <"U38",57,1>,
      <"L259",58,3>,
      <"L259",59,1>,
      <"12bL34",60,1>,
      <"2S411",60,1>,
      <"6L34",60,1>,
      <"U42",60,1>,
      <"U53",60,1>,
      <"2U42",60,2>,
      <"L261",61,1>,
      <"L2121",61,1>,
      <"S411",61,1>,
      <"U53",61,1>,
      <"L261",62,2>,
      <"2S65",62,1>,
      <"L62",62,1>,
      <"3L34",63,1>,
      <"J2",63,1>,
      <"L34",63,1>,
      <"S65",63,1>,
      <"L264",64,1>,
      <"2A10",64,1>,
      <"2A14",64,1>,
      <"2A15",64,1>,
      <"2A8",64,1>,
      <"2L34",64,1>,
      <"2S62",64,1>,
      <"2Sz8",64,1>,
      <"2U42",64,1>,
      <"4aL34",64,1>,
      <"4bL34",64,1>,
      <"A8",64,1>,
      <"G23",64,1>,
      <"L34",64,1>,
      <"Sz8",64,1>,
      <"U34",64,1>,
      <"U42",64,1>,
      <"2J2",64,1>,
      <"L264",65,1>,
      <"A13",65,1>,
      <"G24",65,1>,
      <"L43",65,1>,
      <"Sz8",65,1>,
      <"U34",65,1>,
      <"S45",65,2>,
      <"3Suz",66,1>,
      <"6M22",66,1>,
      <"A13",66,1>,
      <"M12",66,1>,
      <"U52",66,1>,
      <"L267",67,1>,
      <"L267",68,1>,
      <"2L34",70,1>,
      <"A8",70,1>,
      <"J2",70,1>,
      <"L271",70,3>,
      <"S62",70,1>,
      <"2U43",70,3>,
      <"L271",71,1>,
      <"L38",72,1>,
      <"L273",73,1>,
      <"L38",73,1>,
      <"U39",73,2>,
      <"L273",74,3>,
      <"A10",75,1>,
      <"U34",75,1>,
      <"J1",76,2>,
      <"A14",77,1>,
      <"HS",77,1>,
      <"J1",77,2>,
      <"L279",78,1>,
      <"3Suz",78,1>,
      <"A14",78,1>,
      <"Fi22",78,1>,
      <"G23",78,1>,
      <"G24",78,1>,
      <"O73",78,1>,
      <"S45",78,1>,
      <"S63",78,1>,
      <"TF42",78,1>,
      <"L279",79,1>,
      <"L279",80,1>,
      <"2U42",80,1>,
      <"4bL34",80,1>,
      <"U42",81,1>,
      <"L281",81,1>,
      <"L281",82,1>,
      <"L283",82,2>,
      <"L283",83,1>,
      <"12aU43",84,1>,
      <"12bL34",84,1>,
      <"2J2",84,1>,
      <"2S413",84,1>,
      <"3L34",84,1>,
      <"6aU43",84,1>,
      <"A10",84,1>,
      <"A9",84,1>,
      <"L44",84,1>,
      <"O8m2",84,1>,
      <"O8p2",84,1>,
      <"S62",84,1>,
      <"U35",84,1>,
      <"L2169",85,1>,
      <"J3",85,1>,
      <"L44",85,1>,
      <"S413",85,1>,
      <"S44",85,1>,
      <"S82",85,1>,
      <"U82",85,1>,
      <"U82",86,1>,
      <"L289",88,1>,
      <"L289",89,1>,
      <"2L34",90,1>,
      <"6bU43",90,1>,
      <"6L34",90,1>,
      <"A10",90,1>,
      <"A15",90,1>,
      <"J2",90,1>,
      <"S45",90,1>,
      <"L289",90,1>,
      <"L39",90,1>,
      <"L43",90,1>,
      <"U43",90,1>,
      <"A15",91,1>,
      <"G23",91,2>,
      <"O73",91,1>,
      <"S63",91,1>,
      <"Sz8",91,1>,
      <"L39",91,3>,
      <"3L37",96,1>,
      <"L35",96,1>,
      <"L297",97,1>,
      <"L297",98,3>,
      <"3M22",99,1>,
      <"M12",99,1>,
      <"M22",99,1>,
      <"L2101",100,1>,
      <"2Sz8",104,1>,
      <"12aL34",120,1>];
end intrinsic;