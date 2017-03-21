freeze;
 
get_standard_gens_s82 := function(G)
/* 
   Find standard generators of S(8,2). 
   Assumes G is S(8,2).
   Algorithm and code by Bill Unger 4/12/2003. 
   Standard gens as defined in Birmingham Atlas at that date. 
*/
    P := RandomProcess(G);
    repeat x := Random(P); until Order(x) eq 24; // 1 in 24
    a := x^12; // a is in 2B
    repeat
	repeat 
	    x := Random(P); ord := Order(x); 
	until ord in {5, 10, 15};// 49 in 300
	x := x ^ (ord div 5);
	// x is in 5B with prob 36/49
	count := 0;
	repeat
	    count +:= 1;
	    b := x^Random(P);
	    found_5B := Order(a*b) in {14, 17, 18, 20, 21, 24, 30};
	    // x in 5B gives prob 152/357 we get found_5B true here
	until found_5B or count eq 10;
    until found_5B;
    // now we know that x is in 5B
    repeat
	b := x^Random(P);
	ab := a*b;
    until Order(ab) eq 17 and Order(ab*b) eq 21;
    return a,b;
end function;

S82Identify := function(group: max:= true, Print:=0)
    S := Sym(120);
a := S!
\[2, 1, 4, 3, 7, 9, 5, 12, 6, 14, 16, 8, 13, 10, 21, 11, 23, 25, 27, 29, 15, 32,
17, 34, 18, 36, 19, 38, 20, 30, 42, 22, 33, 24, 46, 26, 49, 28, 52, 53, 54, 31, 
56, 58, 60, 35, 63, 65, 37, 50, 69, 39, 40, 41, 55, 43, 57, 44, 74, 45, 76, 62, 
47, 80, 48, 66, 72, 68, 51, 78, 85, 67, 73, 59, 89, 61, 83, 70, 79, 64, 95, 97, 
77, 98, 71, 86, 87, 102, 75, 105, 91, 92, 93, 108, 81, 109, 82, 84, 111, 101, 
100, 88, 113, 112, 90, 106, 107, 94, 96, 110, 99, 104, 103, 119, 115, 116, 117, 
118, 114, 120 ];
b := S!
\[ 3, 1, 5, 6, 8, 10, 11, 2, 13, 15, 17, 18, 19, 20, 22, 7, 24, 26, 28, 30, 31, 
4, 33, 16, 35, 29, 37, 39, 40, 41, 43, 25, 44, 45, 47, 48, 50, 51, 9, 12, 55, 
36, 57, 59, 61, 62, 64, 66, 67, 68, 46, 23, 60, 70, 14, 71, 72, 73, 52, 75, 77, 
78, 79, 32, 81, 82, 65, 83, 56, 84, 86, 21, 87, 88, 90, 91, 92, 38, 93, 94, 96, 
42, 27, 99, 100, 101, 95, 103, 104, 106, 85, 34, 107, 89, 105, 49, 108, 110, 
112, 102, 69, 76, 114, 115, 58, 53, 116, 113, 98, 117, 109, 54, 118, 120, 80, 
63, 111, 119, 97, 74 ];

    s82 := sub<S|a,b>;
    s82`Order := 47377612800;

    /* presentation from B'ham Atlas */
    F := Group<x,y| x^2, y^5, (x*y)^17, (x, y)^3, (x, y^2)^4, (x, y*x*y)^3, 
    (x, y^2*x*y*x*y^2)^2, (x, y^2*x*y^2)^3, (x, (x*y^2)^4)^2, 
    (x, y*x*y*x*y)^3, (x*y*x*y*x*y^2*x*y^-1*x*y^-2)^4 >;

    phi := hom<F->s82|a, b>;

    if Print gt 1 then print "Setting up isomorphism"; end if;

    //Find standard generators of socle
    ag, bg := get_standard_gens_s82(group);
    group := sub< group | ag,bg >;
    group`Order := 47377612800;

    homom := hom< group -> s82 | [a,b] >;

    maximals:= [];
    if not max then
      return homom, s82, maximals, F, phi;
    end if;

    if Print gt 1 then print "getting maximals"; end if;

    // O-(8,2).2
    M := sub<s82| a ^ (b^2), b * a * b^2 * a * b * a * b * a * b^-2 * a >;
    M`Order := 394813440; /* Index 120 */
    Append(~maximals, M);

    // O+(8,2).2
    M := sub<s82|
	a, a^(b^2),
	b * a * b * a * b * a * b^-1 * a * b^-2 * a * b^-1 * a * b>;
    M`Order := 348364800; /* Index 136 */
    Append(~maximals, M);

    // 2^7.S(6,2) 2-local
    M := sub<s82| a^b, a^(b^2), a^(b^-2 * a),
	a ^ (b^-1 * a * b^-1), a ^ (b^-2 * a * b * a) >;
    M`Order := 185794560; /* Index 255 */
    Append(~maximals, M);

    // 2^(6+4).A8 2-local [ = 2^(6+4).L(4,2) ]
    M := sub<s82|
	a * b * a * b^-1 * a,
	b^-2 * a * b^2, 
	b * a * b^2 * a * b * a * b^-2 * a * b^-1 >;
    M`Order := 20643840; /* Index 2295 */
    Append(~maximals, M);

    // 2^(1+2+8).3.2.A6.2 (chief factors) 2-local 
    // 2^(3+8):(L(2,2)xS(4,2)) ???
    // M := Centralizer(s82,a);
    M := sub<s82| b * a * b^-1 * a * b,
	b * a * b * a * b^-1 * a * b^-1 * a * b * a * b >;
    M`Order := 8847360; /* Index 5355 */
    Append(~maximals, M);

    // S3.S(6,2) 
    M := sub<s82|
	b * a * b^2 * a * b^-1 * a * b^-2 * a * b^2 * a * b^-2 * a * b^-1, 
	a * b * a * b^-1 * a * b^-2 * a * b^-1 * a * b * a * b * a * b * 
	    a * b * a * b >;
    M`Order := 8709120; /* Index 5440 */
    Append(~maximals, M);

    // 2^(3+6).3.2^(3+1).L(3,2) 2-local [2^(3+6+3).(S3 x L(3,2)) ?]
    M := sub<s82|
	b^2 * a * b^-1 * a * b^-1 * a * b * a * b * a * b^-2, 
	a * b * a * b * a * b^2 * a * b^-1 * a * b^-1 * a * b^2 * a, 
	a * b^2 * a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 * a * 
	    b^2 * a * b^-2 * a * b>;
    M := Stabilizer(s82, { 2, 5, 9, 25, 35, 56, 75, 113 });
    M`Order := 4128768; /* Index 11475 */
    Append(~maximals, M);

    // S10
    M := sub<s82|
	a * b^-1 * a * b^-2 * a * b^2 * a * b * a * b^2 * a * b^-2, 
	b^-1 * a * b^2 * a * b * a * b^2 * a * b^-2 * a * b^-1 * a * b^-1, 
	a * b * a * b^-1 * a * b^-1 * a * b^-1 * a * b^-2 * a * b * a * b^2 * 
	    a * b^-1 >;
    M`Order := 3628800; /* Index 13056 */
    Append(~maximals, M);

    // S(4,4):2
    M := sub<s82|
	b^-1 * a * b^-1 * a * b^2 * a * b^-1 * a * b^2 * a * b * a * 
	    b^-1 * a, 
	b^-1 * a * b * a * b^2 * a * b^-1 * a * b^-2 * a * b^2 * a * b^-2 * a >;
    M`Order := 1958400; /* Index 24192 */
    Append(~maximals, M);

    // A6^2.D8 [S(4,2) wr 2 ???]
    M := sub<s82|
	b^-1 * a * b^-1 * a * b^2 * a * b^-2 * a * b * a * b,
	b * a * b^2 * a * b * a * b * a * b * a * b * a * b * a * b^-2,
	a * b^2 * a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 * a * b * 
	    a * b * a * b * a * b^-1>;
    M`Order := 1036800; /* Index 45696 */
    Append(~maximals, M);

    // L(2,17) - unchecked for maximality 
    //         - checked not in any conjugate of any above
    M := sub<s82|
	a * b * a * b^2 * a * b * a * b^2 * a * b * a * b^-1 * 
	    a * b^-2 * a * b * a * b^-2 * a * b^2 * a * b^-2,
	a * b^2 * a * b^-2 * a * b^-1 * a * b^-1 * a * b^-1 * 
	    a * b^-2 * a * b * a * b^-2 * a * b * a * b^2 * a * b^-2 >;
    M`Order := 2448; /* index 19353600 */
    Append(~maximals, M);

    return homom, s82, maximals, F, phi;

end function;
