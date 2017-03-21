/************************************************************/
/*								                            */
/* Project name: Codes over Z4 in MAGMA	                    */
/* File name: testCodesOverZ4.m	        		            */
/*								                            */
/* Comment: Package developed within the CCSG group      	*/
/*								                            */
/* Authors: Jaume Pernas, Jaume Pujol and Merce Villanueva	*/
/*								                            */
/* Revision version and last date: v1.2   15-03-2010		*/
/*                                 v1.3   18-03-2011        */
/*                                 v1.4   29-02-2012        */
/*                                 v1.5   18-12-2015        */
/*                                                          */
/************************************************************/

/*****************************************************************************/
/*****************************************************************************/
/********************* TEST FILE FOR CodesOverZ4.m ***************************/
/*****************************************************************************/
/*****************************************************************************/
/*
	Put the file CodesOverZ4.m in the same directory than this test file.
	Execute the function TestCodesOverZ4()
*/
// Attach("CodesOverZ4.m");
Z  := Integers();
Z2 := Integers(2);
Z4 := Integers(4);


/*****************************************************************************/
GammaRM:=function(s,r,m)
	sum := r div 2;
	aux := 0;
	for i:=0 to sum do
		aux := aux + Binomial(m-2*s-1,r-2*i)*Binomial(s,i);
	end for;
	return aux;
end function;
/*****************************************************************************/
DeltaRM:=function(s,r,m)
	aux := 0;
	for i:=0 to r do
		aux := aux + Binomial(m,i);
	end for;
	aux := aux - GammaRM(s,r,m);
	aux := aux div 2;
	return aux;
end function;
/*****************************************************************************/
TestDualKronecker:=function()

	//equivalent to ExtendedPerfectCodeZ4(2,4)
	ExtendedPerfectCodeZ4 := LinearCode<Z4, 8 |
								[1,0,0,1,0,0,1,3],
								[0,1,0,1,0,0,2,2],
								[0,0,1,1,0,0,1,1],
								[0,0,0,2,0,0,0,2],
								[0,0,0,0,1,0,3,2],
								[0,0,0,0,0,1,2,3]>;
								
	//equivalent to HadamardCodeZ4(2,4)
	HadamardCodeZ4 := LinearCode<Z4, 8 |
						[1,0,3,2,1,0,3,2],
						[0,1,2,3,0,1,2,3],
						[0,0,0,0,2,2,2,2]>;
						
	return 			   DualKroneckerZ4(HadamardCodeZ4) eq ExtendedPerfectCodeZ4 
			and DualKroneckerZ4(ExtendedPerfectCodeZ4) eq HadamardCodeZ4;
			
end function;

/*****************************************************************************/
/******************************************************************************
** TestDimensionOfSpanZ2 function
******************************************************************************/
//RM(2,1,5)=(0,3,4,7)-RM(2,2,5)=(2,7,11,21)-RM(2,3,5)=(0,13,14,29)-RM(2,4,5)=(1,15,31,31)-
TestDimensionOfSpanZ2:=function()

	C := ReedMullerCodeRMZ4(2,2,5);
	D := ReedMullerCodeRMZ4(2,4,5);
	rC := DimensionOfSpanZ2(C);
	rD := DimensionOfSpanZ2(D);
	return rC eq 21 and rD eq 31;
	
end function;
/*****************************************************************************/
/******************************************************************************
** TestDimensionOfSpanZ2ForAllFamily function
******************************************************************************/
// TestDimensionOfSpanZ2ForAllFamily:=function(s,m)
// 
// 	SuposedKer := [];
// 	DKerList   := [DimensionOfKernelZ2(ReedMullerCodeRMZ4(0,r,m)) : r in {0..m}];
// 	GammaDelta := [GammaRM(s,r,m) + DeltaRM(s,r,m) : r in {0..m}];
// 	if s eq 0 then
// 		SuposedKer := [i + m : i in GammaDelta]; 
// 	end if;
// 	if s eq 1 then
// 		SuposedKer := [i + 2 : i in GammaDelta]; 
// 	end if;
// 	if s gt 1 then
// 		SuposedKer := [i + 1 : i in GammaDelta]; 
// 	end if;
// 	if s eq 2 and m eq 5 then
// 		SuposedKer[3] := SuposedKer[3] + 1;
// 	end if;
// 	
// 	SuposedKer[m+1] := SuposedKer[m+1]
// 	
// 	return DKerList eq SuposedKer; 
// 	
// end function;

/*****************************************************************************/
/******************************************************************************
** TestDimensionOfKernelZ2 function
******************************************************************************/
//RM(2,1,5)=(0,3,4,7)-RM(2,2,5)=(2,7,11,21)-RM(2,3,5)=(0,13,14,29)-RM(2,4,5)=(1,15,31,31)-
TestDimensionOfKernelZ2:=function()

	C := ReedMullerCodeRMZ4(2,2,5);
	D := ReedMullerCodeRMZ4(2,4,5);
	kC := DimensionOfKernelZ2(KernelZ2CodeZ4(C));
	kD := DimensionOfKernelZ2(KernelZ2CodeZ4(D));
	
	return kC eq 11 and kD eq 31;
end function;

/*****************************************************************************/
/******************************************************************************
** TestReedMullerCodesRMZ4 function
******************************************************************************/
//TODO: test more properties 
TestReedMullerCodesRMZ4:=function()
	F := ReedMullerCodesRMZ4(1,5);
	n := #F;
	
	itsok := true;
	for i:=1 to n-1 do
		itsok := itsok and F[i] subset F[i+1]; 
	end for;
	
	return itsok;
end function;

/*****************************************************************************/
/******************************************************************************
** TestHadamardCodeZ4 function
******************************************************************************/
TestHadamardCodeZ4:=function()
	C1, G1 := HadamardCodeZ4(4,10);
	C2, G2 := ReedMullerCodeRMZ4(4-1,1,10);
	
	return (C1 eq C2) and (G1 eq G2);
end function;

/*****************************************************************************/
/******************************************************************************
** TestPAutHadamardCodeZ4 function
******************************************************************************/
TestPAutHadamardCodeZ4:=function(delta,m)
       C, G := HadamardCodeZ4(delta,m);
       PAut := PAutHadamardCodeZ4(delta,m);
       PAutOrder := PAutHadamardCodeZ4Order(delta,m);
       itsok1 := #PAut eq PAutOrder;
       itsok2 := #[ Set(C^p) eq Set(C) : p in PAut] eq PAutOrder; 
       return itsok1 and itsok2;
end function;

/*****************************************************************************/
/******************************************************************************
** TestPAutExtendedPerfectCodeZ4 function
******************************************************************************/
TestPAutExtendedPerfectCodeZ4:=function(delta,m)
       C, G := ExtendedPerfectCodeZ4(delta,m);
       PAut := PAutExtendedPerfectCodeZ4(delta,m);
       PAutOrder := PAutExtendedPerfectCodeZ4Order(delta,m);
       itsok1 := #PAut eq PAutOrder;
       itsok2 := #[ Set(C^p) eq Set(C) : p in PAut] eq PAutOrder; 
       return itsok1 and itsok2;
end function;

/*****************************************************************************/
/******************************************************************************
** TestZeroCode function
******************************************************************************/
TestZeroCode:=function()
	   Z	:= ZeroCode(Z4,4);
	   U	:= UniverseCode(Z4,4);
	   GZ  := GeneratorMatrix(Z); 
	   itsok1 := MinRowsGeneratorMatrix(Z) eq GZ;
       itsok2 := LinearCode(PlotkinSum(GZ,GZ)) eq PlotkinSum(Z,Z);
       itsok3 := LinearCode(BQPlotkinSum(GZ,GZ,GZ)) eq BQPlotkinSum(Z,Z,Z);
	   itsok4 := LinearCode(QuaternaryPlotkinSum(GZ,GZ)) eq 
	                             QuaternaryPlotkinSum(Z,Z);
	   itsok5 := LinearCode(DoublePlotkinSum(GZ,GZ,GZ,GZ)) eq 
	                             DoublePlotkinSum(Z,Z,Z,Z);
	   itsok6 := DualKroneckerZ4(Z) eq U;
       itsok7 := DimensionOfSpanZ2(Z) eq 0;
	   itsok8 := RankZ2(Z) eq 0;
       itsok9 := DimensionOfKernelZ2(Z) eq 0;
       itsok10 := KernelZ2CodeZ4(Z) eq Z;
       itsok11 := SpanZ2CodeZ4(Z) eq Z;	   
       return itsok1 and itsok2 and itsok3 and itsok4 and itsok5 and itsok6 
	          and itsok7 and itsok8 and itsok9 and itsok10 and itsok11; 
end function;

/*****************************************************************************/
/******************************************************************************
** TestUniverseCode function
******************************************************************************/
TestUniverseCode:=function()
	   Z	:= ZeroCode(Z4,4);
	   U	:= UniverseCode(Z4,4);
	   GU  := GeneratorMatrix(U);
	   itsok1 := MinRowsGeneratorMatrix(U) eq GU;
       itsok2 := LinearCode(PlotkinSum(GU,GU)) eq PlotkinSum(U,U);
       itsok3 := LinearCode(BQPlotkinSum(GU,GU,GU)) eq BQPlotkinSum(U,U,U);
	   itsok4 := LinearCode(QuaternaryPlotkinSum(GU,GU)) eq 
	                        QuaternaryPlotkinSum(U,U);
	   itsok5 := LinearCode(DoublePlotkinSum(GU,GU,GU,GU)) eq 
	                        DoublePlotkinSum(U,U,U,U);
	   itsok6 := DualKroneckerZ4(U) eq Z;
       itsok7 := DimensionOfSpanZ2(U) eq 8;
	   itsok8 := RankZ2(U) eq 8;
       itsok9 := DimensionOfKernelZ2(U) eq 8;
       itsok10 := KernelZ2CodeZ4(U) eq U;
       itsok11 := SpanZ2CodeZ4(U) eq U;	  	
       return itsok1 and itsok2 and itsok3 and itsok4 and itsok5 and itsok6 
	          and itsok7 and itsok8 and itsok9 and itsok10 and itsok11; 
end function;

/*****************************************************************************/
/******************************************************************************
** TestCosetRepresentatives function
******************************************************************************/
TestCosetRepresentatives:=function()
	   Z	:= ZeroCode(Z4,4);
	   U	:= UniverseCode(Z4,4);
	   
	   itsok1 := CosetRepresentatives(Z) eq {@ c : c in U @};
       itsok2 := CosetRepresentatives(U) eq {@ c : c in Z @}; 
	   
	   L, Lb := KernelCosetRepresentatives(U);
       itsok3 := (L eq []) and (Lb eq []);
	   
	   L, Lb := KernelCosetRepresentatives(Z);
       itsok4 := (L eq []) and (Lb eq []);
	   
	   L, Lb := KernelCosetRepresentatives(ReedMullerCodeRMZ4(0,3,4));
	   itsok5 := (L eq []) and (Lb eq []);
	   
	   L, Lb := KernelCosetRepresentatives(ReedMullerCodeRMZ4(1,2,4));
	   V8 := RSpace(Z4,8);
	   Loutput := [ V8![0,0,1,1,0,0,1,1], V8![1,0,3,0,0,0,0,2],
	                V8![1,0,0,1,0,0,1,3], V8![0,1,0,1,0,0,2,2],
					V8![0,1,1,2,0,0,3,3], V8![1,1,3,1,0,0,2,0],
					V8![1,1,0,2,0,0,3,1] ];
	   V16 := VectorSpace(GF(2),16);
	   Lboutput := [V16![0,0,0,0,0,1,0,1,0,0,0,0,0,1,0,1],
                    V16![0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,1],
                    V16![0,1,0,0,0,0,0,1,0,0,0,0,0,1,1,0],
                    V16![0,0,0,1,0,0,0,1,0,0,0,0,1,1,1,1],
                    V16![0,0,0,1,0,1,1,1,0,0,0,0,1,0,1,0],
                    V16![0,1,0,1,1,0,0,1,0,0,0,0,1,1,0,0],
                    V16![0,1,0,1,0,0,1,1,0,0,0,0,1,0,0,1]];
	   itsok6 := (L eq Loutput) and (Lb eq Lboutput);
	    	
       return itsok1 and itsok2 and itsok3 and itsok4 and itsok5 and itsok6; 
end function;

/*****************************************************************************/
/******************************************************************************
** TestCodesOverZ4 function
******************************************************************************/

//TestCodesOverZ4:=function()
	allok := true;
	printf "\n";
	printf "Testing package CodesOverZ4.m\n\n";
	
	if(TestDualKronecker()) then
		printf "DualKronecker							[OK]\n";
	else
		allok = false;
		printf "DualKronecker							[FAIL]\n";
	end if;
	
	if(TestReedMullerCodesRMZ4()) then
		printf "ReedMullerCodesRMZ4						[OK]\n";
	else
		allok = false;
		printf "ReedMullerCodesRMZ4						[FAIL]\n";
	end if;
	
	if(TestDimensionOfSpanZ2()) then
		printf "DimensionOfSpanZ2		    				[OK]\n";
	else
		allok = false;
		printf "DimensionOfSpanZ2							[FAIL]\n";
	end if;
	
	if(TestDimensionOfKernelZ2()) then
		printf "DimensionOfKernelZ2			   			[OK]\n";
	else
		allok = false;
		printf "DimensionOfKernelZ2						[FAIL]\n";
	end if;
	
	if(TestHadamardCodeZ4()) then
		printf "HadamardCodeZ4  			   			[OK]\n";
	else
		allok = false;
		printf "HadamardCodeZ4   						[FAIL]\n";
	end if;
	
    if(TestPAutHadamardCodeZ4(2,4)) then
		printf "PAutHadamardCodeZ4  			   		[OK]\n";
	else
		allok = false;
		printf "PAutHadamardCodeZ4   					[FAIL]\n";
	end if;

    if(TestPAutExtendedPerfectCodeZ4(2,4)) then
		printf "PAutExtendedPerfectCodeZ4  			   	[OK]\n";
	else
		allok = false;
		printf "PAutExtendedPerfectCodeZ4   				[FAIL]\n";
	end if;
	
	if(TestZeroCode()) then
		printf "Test functions using zero code  			   	[OK]\n";
	else
		allok = false;
		printf "Test funcions using zero code   				[FAIL]\n";
	end if;
	
	if(TestUniverseCode()) then
		printf "Test functions using universe code  			[OK]\n";
	else
		allok = false;
		printf "Test funcions using universe code   			[FAIL]\n";
	end if;
	
	if(TestCosetRepresentatives()) then
		printf "CosetRepresentatives and KernelCosetRepresentatives  			[OK]\n";
	else
		allok = false;
		printf "CosetRepresentatives and KernelCosetRepresentatives   			[FAIL]\n";
	end if;

	// return allok;
    print allok;
//end function;

/*****************************************************************************/

