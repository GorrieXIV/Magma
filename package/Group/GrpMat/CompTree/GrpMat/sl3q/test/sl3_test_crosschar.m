SetLogFile("sl3_test_crosschar.out" : Overwrite := true);
SetVerbose("sl3q", 0);

SetSeed(1);

load "../../../test/suites/testgroup.m";

names := ["L311G1-f11r3aB0.m", "L311G1-f5r132B0.m", "L33G1-f3r3aB0.m",
	  "L311G1-f2r132B0.m",  "L33G1-f13r11B0.m", "L37G1-f3r55B0.m", 
	  "L311G1-f3r132B0.m", "L33G1-f2r12B0.m", "L37G1-f7r8B0.m"];

procedure TestSL3CT(H)
    G := RandomConjugate(H);
    TestGroup(G : Verify := true);
end procedure;

path := "../../../test/CrossChar/";

for name in names do
    G := eval(Read(path cat name) cat "return G;");
    printf "Testing group %o\n", name;
    TestSL3CT(G);
end for;
