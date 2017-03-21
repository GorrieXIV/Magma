freeze;

/*
Library access.
Code by JF Carlson; installed by AKS April 2016.
*/

contents := {@
"2A7_2_1", "2A7_2_2", "2A7_3_1", "2A7_3_2", "2A7_3_3", "2A7_5_1", "2A7_5_2", 
"2A7_7_1", "2A7_7_2", "2A8_2_1", "2A8_2_2", "2A8_3_1", "2A8_3_2", "2A8_3_3", 
"2A8_3_4", "2A8_5_1", "2A8_5_2", "2A8_5_3", "2A8_5_4", "2A8_7_1", "2A8_7_2", 
"2A9_2_1", "2A9_2_2", "2A9_3_1", "2A9_3_2", "2A9_3_3", "2A9_5_1", "2A9_5_2", 
"2A9_5_3", "2A9_5_4", "2A9_5_5", "2A9_7_1", "2A9_7_2", "2L34_2_1", "2L34_2_2", 
"2L34_3_1", "2L34_3_2", "2L34_5_1", "2L34_5_2", "2L34_7_1", "2L34_7_2", "2M12_11_1", 
"2M12_11_2", "2M12_2_1", "2M12_2_2", "2M12_3_1", "2M12_3_2", "2M12_3_3", "2M12_5_1", 
"2M12_5_2", "2M12_5_3", "2U42_2_1", "2U42_2_2", "2U42_3_1", "2U42_3_2", "2U42_5_1", 
"2U42_5_2", "3A7_2_1", "3A7_2_2", "3A7_2_3", "3A7_3_1", "3A7_3_2", "3A7_5_1", 
"3A7_5_2", "3A7_7_1", "3A7_7_2", "3A7_7_3", "3D42_3_1", "3D42_7_1", "3L34_2_1", 
"3L34_2_2", "3L34_3_1", "3L34_3_2", "3L34_3_3", "3L34_5_1", "3L34_5_2", "3L34_7_1", 
"3L34_7_2", "3L34_7_3", "6A7_2_1", "6A7_2_2", "6A7_2_3", "6A7_2_4", "6A7_2_5", 
"6A7_3_1", "6A7_3_2", "6A7_3_3", "6A7_3_4", "6A7_5_1", "6A7_5_2", "6A7_5_3", 
"6A7_5_4", "6A7_7_1", "6A7_7_2", "6A7_7_3", "6A7_7_4", "6A7_7_5", "6A7_7_6", 
"6L34_2_1", "6L34_2_2", "6L34_2_3", "6L34_3_1", "6L34_3_2", "6L34_3_3", "6L34_3_4", 
"6L34_3_5", "6L34_3_6", "6L34_5_1", "6L34_5_2", "6L34_5_3", "6L34_5_4", "6L34_7_1", 
"6L34_7_2", "6L34_7_3", "6L34_7_4", "6L34_7_5", "6L34_7_6", "A10_2_1", "A10_3_1", 
"A10_5_1", "A10_7_1", "A11_2_1", "A11_3_1", "A11_5_1", "A12_3_1", "A12_3_2", "A12_5_1",
"A8_2_1", "A8_3_1", "A8_3_2", "A8_5_1", "A8_5_2", "A8_7_1", "A9_2_1", "A9_2_2", 
"A9_3_1", "A9_3_2", "A9_5_1", "A9_5_2", "A9_5_3", "A9_7_1", "G23_2_1", "G23_3_1", 
"G23_5_1", "He_2_1", "He_2_2", "HS_3_1", "HS_3_2", "J1_11_1", "J1_19_1", "J1_2_1", "J1_2_2", 
"J1_3_1", "J1_3_2", "J1_3_3", "J1_5_1", "J1_5_2", "J1_5_3", "J1_7_1", "J2_2_1", 
"J2_2_2", "J2_3_1", "J2_3_2", "J2_3_3", "J2_5_1", "J2_5_2", "J2_7_1", "J3_2_1", 
"J3_3_1", "L216_17_1", "L216_2_1", "L216_3_1", "L216_3_2", "L216_5_1", "L216_5_2",
"L227_13_1", "L227_2_1", "L227_2_2", "L227_3_1", "L227_7_1", "L227_7_2","L232_11_1", 
"L232_11_2", "L232_2_1", "L232_31_1", "L232_3_1", "L232_3_2", "L34_2_1", "L34_3_1", 
"L34_5_1", "L34_7_1", "L35_2_1", "L35_2_2", "L35_3_1", "L35_3_2", "L35_3_3", 
"L35_3_4", "L52_2_1", "M12_11_1", "M12_2_1", "M12_2_2", "M12_3_1", "M12_3_2", 
"M12_5_1", "M12_5_2", "M22_11_1", "M22_2_1", "M22_3_1", "M22_3_2", "M22_5_1", 
"M22_7_1", "M23_11_1", "M23_2_1", "M23_23_1", "M23_3_1", "M23_5_1", "M23_5_2", 
"M23_7_1", "M23_7_2", "m24_3_1", "McL_2_1", "McL_3_1", "McL_5_1", "S44_5_1", "S45_3_1", 
"S45_5_1", "S62_2_1", "Sz8_13_1", "Sz8_2_1", "Sz8_5_1", "Sz8_7_1", "Tits_2_1", 
"Tits_3_1", "Tits_5_1", "U311_11_1", "U311_2_1", "U34_13_1", "U34_2_1", "U34_3_1", 
"U34_3_2", "U34_5_1", "U35_2_2", "U35_3_1", "U35_3_2", "U35_5_1", "U35_7_1", 
"U37_2_1", "U37_2_2", "U37_7_1", "U42_2_1", "U42_3_1", "U42_5_1"
@};

intrinsic BasicAlgebraFromGroup(
    name::MonStgElt, p::RngIntElt, b::RngIntElt
) -> AlgBas
{This function reconstructs from the library the basic algebra of the 
block number "b" of the group algebra KG where K is a field of characteristic
"p" and G is the finite group with Atlas name "name". Block number 1 is 
always the principal block.
}

    tag := name cat "_" cat IntegerToString(p) cat "_" cat IntegerToString(b);
    if tag in contents then

	fname := Sprintf(
	    "%o/data/AlgBas/allgpfiles/%o.dat", GetLibraryRoot(), tag
	);
	A := eval Read(fname);
    else
	require false: "The algebra requested is not in the database."; 
    end if;
    
     return A;

end intrinsic; 

intrinsic BasicAlgebraGroupNames() -> SetIndx
{The set of names of groups for which there are basic algebras in
the library (see BasicAlgebraFromGroup)}
    return contents;
end intrinsic;

schurcontents := 
{@
    [ 3, 5, 2 ], [ 3, 5, 3 ], [ 3, 5, 5 ], [ 3, 6, 2 ], [ 3, 6, 3 ], [ 3, 6, 5 ],
    [ 3, 7, 2 ], [ 3, 7, 3 ], [ 3, 7, 5 ], [ 3, 7, 7 ], 
    [ 3, 8, 2 ], [ 3, 8, 3 ], [ 3, 8, 5 ], [ 3, 8, 7 ],
    [ 3, 9, 2 ], [ 3, 9, 3 ], [ 3, 9, 5 ], [ 3, 9, 7 ], [ 3, 10, 2 ], [ 3, 10, 3 ],
    [ 4, 5, 2 ], [ 4, 5, 3 ], [ 4, 5, 5 ], [ 4, 6, 2 ], [ 4, 6, 3 ], [ 4, 6, 5 ],
    [ 4, 7, 2 ], [ 4, 7, 3 ], [ 4, 7, 5 ], [ 4, 7, 7 ], [ 4, 8, 2 ], [ 4, 8, 3 ], [ 4, 8, 5 ],
    [ 5, 5, 2 ], [ 5, 5, 3 ], [ 5, 5, 5 ], [ 5, 6, 2 ], [ 5, 6, 3 ], [ 5, 6, 5 ],
    [ 5, 7, 2 ], [ 5, 7, 3 ], [ 5, 7, 5 ], [ 5, 8, 2 ], [ 5, 8, 3 ],
    [ 6, 6, 2 ], [ 6, 6, 3 ], [ 6, 6, 5 ], [ 6, 7, 2 ], [ 6, 7, 3 ], [ 6, 7, 5 ], [ 6, 7, 7 ],
    [ 7, 7, 2 ]
@};

intrinsic BasicAlgebraFromSchur(
    r::RngIntElt, s::RngIntElt, p::RngIntElt
) -> AlgBas
{Create a basic algebra from Schur info [r, s] in characteristic p}

    tag := "Schur" cat IntegerToString(r) cat "_" cat IntegerToString(s)
	  cat "_" cat IntegerToString(p);

    if [r,s,p] in schurcontents then 
	fname := Sprintf(
	    "%o/data/AlgBas/schurfiles/%o.dat", GetLibraryRoot(), tag
	);
	A := eval Read(fname);
    else
         error "\nThe algebra requested is not in the database.\n\n";
    end if;

     return A;

end intrinsic;

