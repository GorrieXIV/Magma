SetLogFile("sl3_test_group.out" : Overwrite := true);
SetVerbose("sl3q", 8);

SetSeed(2);

load "../../../test/suites/testgroup.m";

procedure TestSL3(G, F)
    print "Testing group";
    try
	flag := RecogniseSL3(G, F);
	assert flag;
        print G`SL3Data`SL2Time / G`SL3Data`TotalTime;
    catch err
        ErrorOutput(err, "RecogniseSL3", G);
    end try;
end procedure;

/*
G := MatrixGroup<9, GF(2, 6) |
    Matrix(GF(2, 6), 9, 9, [ W^29, W^5, W^41, W^5, W^56, W^4, W^51, W^2, W^42, 
    W^21, W^51, W^13, W^54, W^8, W^53, W^10, W^32, W^8, W^19, W^36, W^39, W^52, 
    W^23, W^43, W^29, W^44, W^56, W^39, W^16, W^6, 0, W^28, W^3, W^13, W^50, 
    W^2, W^49, W^60, W^33, W^17, W^9, W^26, W^40, W^6, W^42, W^28, W^19, W^42, 
    W^15, W^24, W^42, W^22, W^12, W^16, W^48, W^15, W^59, W^32, W^60, W^34, 
    W^34, W^16, W^55, W^16, W^55, W^22, W^49, W^58, W^31, W^39, W^7, W^15, W^8, 
    W^46, 1, W^50, W^47, W^35, W^10, W^18, W^18 ] where W := GF(2, 6).1),
    Matrix(GF(2, 6), 9, 9, [ W^22, W^26, W^45, W^5, W^25, W^49, W^26, W^42, 
    W^49, W^62, W^62, W^41, W^12, W^15, W^45, W^60, W^20, W^31, W^32, W^48, 
    W^24, W^10, W^48, W^57, W^11, W^19, W^12, 0, W, W^32, W^58, W^23, W^6, 0, 
    W^35, W^16, W^60, W^12, W^48, W^60, W^48, W^39, W, W^45, W^40, W^38, W^13, 
    W^15, W^11, W^62, W^45, W^34, W^8, W^52, W^57, W^50, W^29, W^48, W^46, W^45,
    W^43, W^3, W^11, W^25, W^26, W^33, W^43, W^12, W^16, W^49, W^3, W^45, W^62, 
			       W^53, W^40, W^15, W^24, W^43, W^62, W^15, W^25 ] where W := GF(2, 6).1) >;
*/
G := MatrixGroup<9, GF(2, 4) |
    Matrix(GF(2, 4), 9, 9, [ W^7, W^7, W^11, W^12, W, W^9, 0, W^9, W^6, 1, W^7, 
    1, W^11, W, W^4, W^2, W^9, W^9, W^14, W, W^9, 1, 1, W^2, W^11, W^12, 1, 
    W^14, W^12, W^5, W^7, W^10, W^4, W, W, 0, W^12, W^3, W, W^3, 0, W^4, W^8, 
    W^2, W^10, W^3, W^10, W^8, W, W^2, W^8, W^13, W^14, W^6, 1, W^7, W^13, W, 
    W^13, W^4, W^6, W^11, W^11, W^2, W^9, 0, W^9, W^11, W^2, W^14, 1, W^8, W^9, 
    W^10, W^9, W^10, 1, W^7, W^8, 0, W^5 ] where W := GF(2, 4).1),
    Matrix(GF(2, 4), 9, 9, [ W^13, W^14, W^9, 0, W^3, W^8, W^13, W^6, W^3, 1, 
    W^4, W^7, W^9, W^3, W^4, W^9, W^7, W^11, W^9, W^5, W^3, W^8, W^12, W^6, W^2,
    W^12, W^10, W, W^4, W^5, W^6, W^8, 1, W^13, W^6, W^2, W^8, W^7, W^13, W^4, 
    W, W^12, W, W^6, W^8, 0, W^5, W^6, W^11, W^5, W^14, W^3, W^8, W^3, W, W^4, 
    1, W^2, W^3, W^13, W^13, W, W^8, W^12, W^10, W^10, 1, W^6, W, W^14, 0, W, 0,
			       W^2, W^3, 1, W^9, W^14, W^9, W^14, W^13 ] where W := GF(2, 4).1) >;

TestSL3(G, CoefficientRing(G));

