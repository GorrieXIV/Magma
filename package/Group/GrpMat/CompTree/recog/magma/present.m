/******************************************************************************
 *
 *    present.m Composition Tree sporadic group presentations
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Eamonn O'Brien and Henrik B‰‰rnhielm
 *    Dev start : 2008-04-26
 *
 *    Version   : $Revision:: 2628                                           $:
 *    Date      : $Date:: 2014-05-08 19:38:25 +1000 (Thu, 08 May 2014)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: present.m 2628 2014-05-08 09:38:25Z eobr007                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

 /* known presentations for sporadic groups and their covers 
   on standard generators */


SporadicGroupPresentations := AssociativeArray ();

/*
Mathieu group M11 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^4,
(x*y)^11,
(x*y^2)^6,
x*y*x*y*x*y^-1*x*y*x*y^2*x*y^-1*x*y*x*y^-1*x*y^-1
>;
SporadicGroupPresentations["M11"] := G;

/*
M12 presented on its standard generators.
SGens (x,y) are (2B, 3B, 11[AB]).
*/

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^11,
(x,y)^6,
(x*y*x*y*x*y^-1)^6,
(x,y*x*y)^5 // Redundant relation that aids coset enumeration.
>;

SporadicGroupPresentations["M12"] := G;

/*
2"M12 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^6,
(y^3,x),
(x*y)^11,
(x,y)^6,
(x*y*x*y*x*y^-1)^6*y^-3,
(x,y*x*y)^5 // Redundant relation that aids coset enumeration.
>;

SporadicGroupPresentations["2M12"] := G;

/*
M22 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^4,
(x*y)^11,
(x*y^2)^5,
(x,y)^6, // Redundant but very useful.
(x,y*x*y)^3,
(x*y*x*y*x*y^-1)^5
>;

SporadicGroupPresentations["M22"] := G;


/*
M23 presented on its standard generators.

Length: 190 [or 238].
NoRels: 8   [or 9].
[Depends on whether (x*y*x*y^2*x*y^2)^6=1 is included.]
Enumerates quite well with (x*y*x*y^2*x*y^2)^6=1.
It enumerates quite appallingly without it.
*/


G<x,y>:=Group<x,y|
x^2,
y^4,
(x*y)^23,
(x*y^2)^6,
(x,y)^6,
(x*y*x*y^-1*x*y^2)^4,
(x*y)^3*x*y^-1*x*y^2*(x*y*x*y^-1)^2*(x*y)^3*(x*y^-1)^3,
(x*y*x*y^2*x*y^2)^6, // Is redundant, but very useful.
(x*y*x*y^2)^3*(x*y^2*x*y^-1)^2*x*y*x*y^2*x*y*x*y^-1*x*y^2
>;

SporadicGroupPresentations["M23"] := G;

/*
M24 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^23,
(x,y)^12,
(x,y*x*y)^5,
(x*y*x*y*x*y^-1)^3*(x*y*x*y^-1*x*y^-1)^3,
// (x,y^-1*x*y*x*y)^5, // redundant, but quite useful.
(x*y*(x*y*x*y^-1)^3)^4
>;

SporadicGroupPresentations["M24"] := G;

/*
HS presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^5,
(x*y)^11,
(x*y^2)^10,
(x,y)^5,
(x,y*x*y)^3,
(x,y^2)^6,
x*y*x*y*x*y^2*x*y^-1*x*y^-2*x*y^-1*x*y^2*x*y*x*y*(x*y^-2)^4,
x*y*(x*y^2*(x*y^-2)^2)^2*x*y^2*x*y*x*y^2*(x*y^-1*x*y^2)^2,
x*y*x*y*(x*y^2)^2*x*y*(x*y^-1)^2*x*y*(x*y^2)^2*x*y*x*y*x*y^-2*x*y^-1*x*y^-2,
(x*y*x*y*x*y^2*x*y^-1*x*y^-2*x*y*x*y*x*y^-1)^2, // R1.
(x*y*x*y*x*y^2)^2*x*y*x*y*x*y^-1*x*y*x*y*(x*y^2)^3*x*y*x*y*x*y^-1, // R2.
x*y*(x*y*x*y^2)^3*x*y*x*y*x*y^2*x*y^-1*x*y*x*y^-2*x*y*x*y^-1*x*y^2 // R3.
>;

SporadicGroupPresentations["HS"] := G;

/*
J2 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^7,
(x,y)^12,
// (x*y*x*y*x*y^-1*x*y*x*y^-1)^6, // Is redundant.
(x*y*x*y*x*y^-1*x*y*x*y^-1*x*y^-1*x*y*x*y*x*y^-1*x*y^-1*x*y*x*y^-1)^3
>;

SporadicGroupPresentations["J2"] := G;

/*
2"J2 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^4,
(x^2,y),
y^3,
(x*y)^7,
(x,y)^12,
// (x*y*x*y*x*y^-1*x*y*x*y^-1)^6, // Is redundant.
x^-2*(x*y*x*y*x*y^-1*x*y*x*y^-1*x*y^-1*x*y*x*y*x*y^-1*x*y^-1*x*y*x*y^-1)^3
>;
SporadicGroupPresentations["2J2"] := G;



/*
Co2 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^5,
(x*y^2)^9,
(x,y)^4,
(x,y^2)^4,
(x,y*x*y)^3,
(x,y*x*y^2*x*y)^2,
(x,y*x*y^-2)^3,
(x,y^-2*x*y*x*y^-2)^2,
// (x,y^2*x*y^2)^3, // Redundant, but useful.
(x*y*x*y^2*x*y^-1*x*y^-2)^7
>;

SporadicGroupPresentations["Co2"] := G;


/*
McL presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^5,
(x,y)^5,
(x*y)^11,
(x*y^2)^12,
(x,y^2)^6,
(x*y*x*y^-2)^7,
(x,y^-2*x*y*x*y*x*y^2)^2, // R0 - redundant.
(x,y^-2*x*y^2*x*y^-1*x*y*(x*y^2)^2*x*y*x*y^-1),
(x,y*(x*y^2)^3)^2, // R1 - redundant.
(x,y^2*x*y*(x*y^2)^2)^2,
x*y*x*y^2*x*y^-2*x*y*x*y^-1*x*y^2*(x*y^-2*x*y)^2*(x*y^2*x*y^-2*x*y^2)^2,
(x,y^2*x*y^2*x*y^-1*x*y^2)^2,
(x,y^2*x*y)^4,
(x,y^2*x*y^2)^4 // R2 - redundant.
>;

SporadicGroupPresentations["McL"] := G;

/*
He presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^7,
(x*y)^17,
// (x*y^3)^8, // redundant.
// (x*y^2*x*y^2*x*y^-3)^3, // redundant, maybe useful.
(x,y*x*y*x*y^-1*x*y*x*y),
(x,y^3)^5,
(x,y)^6,
// x*y*(x*y*x*y^-2)^2*x*y^2*x*y^-1*x*y^2*x*y^-2*(x*y*x*y^-1)^2, // redundant, maybe useful.
(x*y)^4*x*y^2*x*y^-3*x*y*x*y*x*y^-1*x*y^3*x*y^-2*x*y^2
>;

SporadicGroupPresentations["He"] := G;

/*
Fi22 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^13,
(x*y)^11,
// (x*y^2)^21, // [R1]
(x*y*x*y*x*y^-3)^5, // [R2]
(x,y)^3,
(x,y^2)^3,
(x,y^3)^3,
(x,y^4)^2,
(x,y^5)^3,
(x,y*x*y^2)^3,
(x,y^-1*x*y^-2)^2,
(x,y*x*y^5)^2,
(x,y^2*x*y^5)^2
>;

SporadicGroupPresentations["Fi22"] := G;
SporadicGroupPresentations["F22"] := G;

/*
2"Fi22 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^13,
(x*y)^11,
(x,y)^3,
(x,y^2)^3,
(x,y^3)^3,
(x,y^4)^2,
(x,y^5)^3,
(x,y*x*y^2)^3,
(x,y^-1*x*y^-2)^2,
(x,y*x*y^5)^2,
// (x,y^-1*x*y^-5)^3, // Redundant.
(x,y^2*x*y^5)^2
>;
SporadicGroupPresentations["2Fi22"] := G;
SporadicGroupPresentations["2F22"] := G;

/*
J1 presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^7,
(x*y*(x*y*x*y^-1)^3)^5,
(x*y*(x*y*x*y^-1)^6*x*y*x*y*(x*y^-1)^2)^2
>;

SporadicGroupPresentations["J1"] := G;

/*
J3 presented in terms of its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^3,
(x,y)^9,
(x*y)^19,
((x*y)^6*(x*y^-1)^5)^2,
((x*y*x*y*x*y^-1)^2*x*y*x*y^-1*x*y^-1*x*y*x*y^-1)^2,
x*y*x*y*(x*y*x*y^-1)^3*x*y*x*y*(x*y*x*y^-1)^4*x*y^-1*(x*y*x*y^-1)^3,
((x*y)^3*(x*y*x*y^-1)^2)^4
>;

SporadicGroupPresentations["J3"] := G;

/*
J4 presented on its G2-`standard' generators.
*/

G<x,y,t>:=Group<x,y,t|
x^2,
y^3,
(x*y)^23,
(x,y)^12,
(x,y*x*y)^5,
(x*y*x*y*x*y^-1)^3*(x*y*x*y^-1*x*y^-1)^3,
(x*y*(x*y*x*y^-1)^3)^4,
t^2,
(t,x),
(t,y*x*y*(x*y^-1)^2*(x*y)^3),
(y*t^(y*x*y^-1*x*y*x*y^-1*x))^3,
((y*x*y*x*y*x*y)^3*t*t^((x*y)^3*y*(x*y)^6*y))^2
>;
SporadicGroupPresentations["J4"] := G;

/* Havas, Soicher, Wilson presentation for Thompson */
G := Group <a, b, c, d, e, s, t, u | 
   a^2, b^2, c^2, d^2, e^2, (a*b)^3, (a * e)^2, (b * c)^3,
   (b * d)^2, (b * e)^2, a = (c * d)^4, (c * e)^2, (d * e)^3,
   (b * c * d * e)^8,
   s^7, (s, a), (s, b), (s, c), (s * d)^2, (e, s) = e^(s^3),
   t^3, (t, a), (t, b), (t, c), (t, d), (t, e), s^t = s^2,
   u^2 = a * c, (u, a), (u, c), (u, e), (d * e * d^u)^2,
   (u, (a * c)^b) = e, (u^d, (a * c)^b) = u * e * (a * c)^b * u^d * e * c,
   t^u = t^-1,
   (e, u^(s^2)), a * c = (u * s)^3 = (u, s)^4, 
   (d * u^(s^2))^4 = a * c * c^d * c ^(d * e * s^-1) * c^(d * e * s^2) >;
SporadicGroupPresentations["Th"] := G;

/* presentation extracted from 
Generators and relations for the Lyons sporadic simple group
By Christopher Parker, Arch. Math. 78 (2002) 97-103
*/
   
ParkerPresentationForLy := function ()

f<b1,b2,b3,b4, b5,b6,b7,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10>:=FreeGroup (17);

// Coxeter type relations for 3 McL 2
//
cox :=    [ b1^2,b2^2,b3^2,b4^2,b5^2,b6^2,b7^2, (b1,b7),
                    (b7,b2), (b7,b3), (b7,b4), (b7,b6),
                    (b1,b3), (b1,b6), (b1,b4), (b1*b2)^3, (b1*b5)^4,
                    (b2,b6), (b2,b4), (b2*b3)^5, (b2,b5), (b3*b4)^3,
            (b3*b6)^4, (b3*b5)^3, (b4,b5), (b4*b6)^3,  (b5*b7)^8];

// relations that identify a1..a8 and a10 with elements of 3McL2
//
Ident :=  [a2 = (b3*b6*b7),a3 = (b3*b6*(b3*b6)^b4*b7),
                a1 = (a3^((b1*b5)^2)),a4 = ((b4*a1*a3)^(a2*a2^b4)*a1),
                    a5 = a2^((b1*b5)^2*b4*b3), a6 = (a1^b6), 
                    a7 = ((b1*b2)^(b5*b2*b3*b1*b5*b1*b3*b5),a1),
                    a8 = (b3*b5*b6)^7, a10 = a2^((b5*b1*b2*b3)^4)];
       
// additional relations of 3 McL2
//
r0 := [ b1 * (b3*b6)^-2, b2 * (b5*b6)^-3, (b5*b1*b2)^3,
       (b2*b3*b5)^5, (b1*b5*b3*b4)^4, (b3*b5*b6)^21 ];
r1 := [ b5^b7*b5^(b3*b1*b2*b3*b6*b4*b2*b5*b3*b5*b2*b4*b1*b5*b2)];

r12 := [ a6^4, a1^2 * a6^-2, a8*a8^a6, (a2*a6)^3*a1^2, (a1,a6)*a1^2,
        (a3*a6)^3, (a4,a6)*a1^2, (a5,a6)*a1^2, 
        (a7^a6*a7^2*(a7^a1)^2*(a7^a2)^2)*a8^2 ];
// not needed for isomorphism check but needed for coset enumeration 
r12 := [];

r13 := [a10^4, a8^a10*a8, (a1^a10*a1)^5*a8^2, (a5^a10*a5)^5*a8^2,
        (a10^2*a1^2)^2, (a3^a10*a3)^5*a8^2, (a1^a10*a5)^3, (a1*a3*a5,a10)*a8^2,
        (a1,a10)^3, (a3,a10)^5*a8, (a5,a10)^3, 
        (a10^2*a3)^2, a10^2*((a1^2)^(a10*a5))^(a10^2*((a1^2)^(a10*a5))),
        (a10,a7)^4*a8, (a10,a2)^3,(a1*a10)^5*a8^2,
        (a3*a10)^8*a8^2, (a5*a10)^4*a8,(a2*a10)^4*a8^2,(a4*a10)^4*a8^2,
        (a10,a4)^3,a1^-1*a10^(a1^3*a5*a10*a5^2*a10)*a8, 
        ((a4*a5)^2)^a10*(a4*a5)^4*((a1*a2)^a7)*((a1*a2)^(a7*a3))*a8,
        (a7*a10)^8,
       (a1*a2)^a10*(a4*a5)^4*(a1*a2)*((a1*a2)^a7)^2*((a1*a2)^(a7*a3))*a8^2,
        (a7^(a1^-1*a10^-1*a1^-1*a3^-1)*(a1,a10)^-1*(a1*a2)*
        ((a1*a2)^a7)^2*(a1*a2)^(a7*a3))*a8^2];
// not needed for isomorphism check but needed for coset enumeration 
r13 := [];

r2 := [ a9^a6*a9^5];

r3 := [(a9^(a10^2*a9))^-1 * ((a10*a3)^(a7*a4*a10)*(a1*a2)*((a1*a2)^(a7*a3))^2)];

r123 := [ a1^4, a2^4, a3^4, a4^4, a5^4, a1^2 * a2^-2, a1^2 * a3^-2, 
         a1^2 * a4^-2, a1^2 * a5^-2, a7^3, a8^3, 
         a8*a8^a1, a8 * a8^a2, a8*a8^a3, (a8,a8^a4), a8*a8^a5, (a8, a7),
         (a1*a2)^3, (a1, a3)* a1^2, (a1, a4)*a1^2, (a1, a5)*a1^2, 
         (a2, a3)*a1^2, (a2, a4)*a1^2, 
         (a2, a5)  * a1^2, (a3, a4)*a1^2, (a3, a5)*a1^2, (a4*a5)^3*a1^2, 
         (a4*a5)^2*(a7, a7^a1), 
         (a7, a7^a2), (a7 ^ (a2*a1), a7)*a8^2 * ((a7 ^ (a2*a1), a7^a2))^-1,
         (a7 ^ (a2*a1), a7)*a8^2 * (a7, a7^a1)^-1,
         (a7 ^ (a2*a1), a7)*a8^2 *  ((a7^a1, a7^a2)*a8)^-1, 
         ((a7, a7^a1)^3, a7), (a7 ^ (a2*a1), a7^a1), 
         (a7^a3*a7*(a7^a2) ^ 2 * (a7, a7^a1)), a7^a4*a7^2*(a7^a2)^2, 
         a7^a5*a7^2*(a7^a2)^2, 
         a7^(a1*a2)*a7 * (a7 ^ (a2*a1))*(a7, a7^a1)^2*a8^2
         ];
// not needed for isomorphism check but needed for coset enumeration 
r123 := [];

r23 := [a9^a1*a9^5,a9^a2*a9^5,a9^a3*a9^5,a9^2*a4^3,
        a7^a9*((a7^a2)^2)*(a4*a5)^2*a8,a8^a9*(a4*a5)^4 ];

G := quo < f | cox, Ident, r0, r1, r12, r13, r2, r23, r123, r3>;

// H is 3.MCl.2 
// H := sub<G | b1,b2,b3,b4,b5,b6,b7>;
// successful enumeration using 105GB of RAM 
// ToddCoxeter (G, sub<G|H>: Hard, CosetLimit:=10^9, Print:=10^6);

return G;
end function;

G := ParkerPresentationForLy ();
SporadicGroupPresentations["Ly"] := G;
assert IsDefined(SporadicGroupPresentations, "Ly"); 

/*
 * Presentation for 2F4(2)' on its standard generators.
 * Length 143, 6 relations.
 * */

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^13,
(x,y)^5,
(x,y*x*y)^4,
(x*y*x*y*x*y*x*y*x*y^-1)^6
>;
SporadicGroupPresentations["TF42"] := G;

G<a,b>:=Group<a,b|
a^2,
b^3,
(a*b)^13,
(a,b)^13,
a*b*a*b*(a,b)^4*(a*b)^3*(a,b*a*b)^3,
(((a*b)^3*a*b^(-1))^2*(a*b)^2*(a*b^(-1))^2)^2
>;
SporadicGroupPresentations["G23"] := G;

G<a,b>:=Group<a,b|
a^3,
b^5,
(a*b)^7,
(a * a^b)^2,
(a * b^(-2) * a * b^2)^2
>;
SporadicGroupPresentations["A7"] := G;

/*
S10(2) presented on its standard generators.
*/

G<x,y>:=Group<x,y|
x^2,
y^11,
(x*y)^15,
(x*y^5)^18,
(x,y)^3,
(x,y^2)^2,
(x,y^3)^2,
(x,y^4)^2,
(x,y^5)^3,
(x,(x*y)^5)^2
>;
SporadicGroupPresentations["S102"] := G;

G<x,y>:=Group<x,y|
x^2,
y^3,
(x*y)^43,
(x,y)^4,
(x,y*x*y*x*y*x*y)^3,
x*y*(x*y*x*y*x*y^-1)^2*((x*y)^3*(x*y^-1)^3)^3
>;
SporadicGroupPresentations["U37"] := G;

G<x,y>:=Group<x,y|
x^2,
y^15,
(x*y)^91, // Get 4 o SU6(3) without this.
(x*y^2)^14,
(x,y)^2,
(x,y^2)^3,
(x,y^4)^3,
(x,y^-2*x*y^5*x*y^2),
(x,y^3)^4
>;

SporadicGroupPresentations["U63"] := G;

G<x,y>:=Group<x,y|
x^2,
y^16,
// (x*y)^45, // R1: Redundant.
(x,y)^3, // R2: Redundant but useful.
(x,y^2)^2,
(x,y^3)^3,
(x,y^4)^2,
(x,y^5)^2,
(x,y^6)^2,
(x,y^7)^2,
(x*y^8)^4,
(x*y*x*y^-4)^10, // R3: Redundant but useful.
(x*y^2*x*y^2*x*y^-1)^9
>;

SporadicGroupPresentations["O10p2"] := G;

   G := Group< a, b |
    a^2 , 
    b^4 , 
    (b * a * b^-1 * a)^4 , 
    b^-1 * a * b^-2 * a * b^-2 * a * b^-2 * a * b^2 * a *
    b^2 * a * b^2 * a * b^2 * a * b^-1 , 
    (a * b^-1)^13 , 
    a * b^-1 * a * b * a * b * a * b^-1 * a * b * a *
    b^-2 * a * b * a * b^-1 * a * b^2 * a * b^-1 * a * b *
    a * b^2 * a * b , 
    (b * a * b * a * b^-1 * a * b^-1 * a)^4 , 
    b^-1 * a * b^-2 * a * b^-2 * a * b^-2 * a * b^-1 * a *
    b^-2 * a * b^-2 * a * b^-2 * a * b * a * b^2 * a * b^2
    * a * b^2 * a * b^-1 * a * b^2 * a * b^2 * a * b^2 * a ,
    a * b^-2 * a * b^-1 * a * b^-2 * a * b^-2 * a * b^-2 *
    a * b^-1 * a * b^-2 * a * b^-1 * a * b^-2 * a * b^2 *
    a * b^2 * a * b^-1 * a * b^2 * a * b * a * b^2 * a *
    b^2 * a * b^2 * a * b , 
    b * a * b^-2 * a * b^-2 * a * b * a * b^-2 * a * b *
    a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 * a * b^-1 *
    a * b * a * b^2 * a * b * a * b^2 * a * b^2 * a * b
    * a * b * a * b^2 * a * b * a  > ;
SporadicGroupPresentations["L43"] := G;


/* construct sporadic group as subgroup of its automorphism group by 
   evaluating the stored SLPs in standard generators of the aut gp */

SporadicMaximalWords := AssociativeArray ();
SporadicMaximalWords["M12"] :=
function (S)
a := S[1]; b := S[2];
return [(a*b*a*b*a*b*b*a*b)^3, (a*b*b)^-3*(a*b)^4*(a*b*b)^3];
end function;

SporadicMaximalWords["M22"] := 
function (S)
w1 := S[1];
w2 := S[2];
w3:=w1*w2;
w4:=w3*w2;
w1:=w3*w4;
w4:=w3*w3;
w3:=w1*w4;
w1:=w2*w2;
w2:=w3*w3;
return [w1,w2];
end function;

SporadicMaximalWords["HS"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/HS/words/HS[2]G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w4^10;
  w7 := w3^-1;
  w8 := w7 * w6;
  w1 := w8 * w3;
  w6 := w4^4;
  w7 := w5^4;
  w3 := w7^-1;
  w4 := w3 * w6;
  w2 := w4 * w7;
  return [w1,w2];
end function;

SporadicMaximalWords["J2"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/J2/words/J2d2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w1 := w6^18;
  w2 := w6^16;
  w5 := w4^3;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  return [w1,w2];
end function;

SporadicMaximalWords["McL"] := 

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/McL/words/McLd2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w1 := w8^12;
  w2 := w5^3;
  w5 := w4^3;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  w4 := w3^-1;
  w5 := w4 * w1;
  w1 := w5 * w3;
  return [w1,w2];
end function;

SporadicMaximalWords["Suz"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/Suz/words/Suzd2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w1 := w3^14;
  w5 := w4 * w4;
  w4 := w5^-1;
  w3 := w4 * w1;
  w1 := w3 * w5;
  return [w1,w2];
end function;

SporadicMaximalWords["He"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/He/words/Hed2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w6;
  w2 := w6 * w7;
  w7 := w4 * w4;
  w8 := w7^-1;
  w9 := w8 * w2;
  w2 := w9 * w7;
  w7 := w6 * w5;
  w8 := w7 * w3;
  w1 := w8^14;
  return [w1,w2];
end function;

SporadicMaximalWords["HN"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/HN/words/HNd2G1-max1W1
function(S)
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w5 * w5;
  w7 := w5 * w6;
  w2 := w6 * w7;
  w6 := w4 * w4;
  w7 := w6 * w6;
  w8 := w7 * w7;
  w9 := w6 * w8;
  w10 := w8 * w2;
  w2 := w10 * w9;
  w6 := w3 * w5;
  w8 := w6 * w5;
  w9 := w3 * w8;
  w10 := w9 * w4;
  w9 := w10 * w10;
  w8 := w10 * w9;
  w7 := w9 * w8;
  w1 := w7 * w7;
  w4 := w3 * w3;
  w5 := w3 * w4;
  w6 := w5^-1;
  w7 := w6 * w1;
  w1 := w7 * w5;
  return [w1,w2];
end function;

SporadicMaximalWords["F22"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/F22/words/F22d2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w5 := w2 * w8;
  w6 := w4 * w4;
  w7 := w6^-1;
  w8 := w7 * w5;
  w2 := w8 * w6;
  w4 := w3 * w3;
  w5 := w3 * w4;
  w6 := w5 * w5;
  w7 := w6^-1;
  w8 := w7 * w1;
  w1 := w8 * w6;
  return [w1,w2];
end function;

SporadicMaximalWords["Fi22"] := SporadicMaximalWords["F22"];

SporadicMaximalWords["Fi24"] := 
function (S)
w1 := S[1]; w2 := S[2];
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w1:=w4^10;
w2:=w7^8;
w6:=w5^10;
w7:=w6^-1;
w3:=w7*w2;
w2:=w3*w6;
return [w1, w2];
end function;
SporadicMaximalWords["F24"] := SporadicMaximalWords["Fi24"];

SporadicMaximalWords["ON"] :=
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/ON/words/ONd2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w2 * w2;
  w4 := w1 * w3;
  w5 := w4 * w4;
  w6 := w5^-1;
  w7 := w3 * w5;
  w1 := w6 * w7;
  return [w1,w2];
end function;

SporadicMaximalWords["J3"] :=
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/spor/J3/words/J3d2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w1 := w3^12;
  w4 := w5^-1;
  w3 := w4 * w2;
  w2 := w3 * w5;
  return [w1,w2];
end function;

SporadicMaximalWords["TF42"] := 
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/words/TF42d2G1-max1W1
function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w3;
  w5 := w4 * w4;
  w3 := w4 * w2;
  w4 := w3 * w3;
  w3 := w4 * w2;
  w4 := w1 * w3;
  w3 := w5 * w4;
  w5 := w4^-1;
  w2 := w5 * w3;
  return [w1,w2];
end function;

/* return presentation for A_n on standard generators */

PresentationForAlternatingGroup := function (n)
   if IsOdd (n) then
       /* n odd: a=(1,2,3), b=(1,2,...,n), */
      return Group <a, b | a^3, b^n, (a*b^2)^((n-1) div 2), 
                           [((b*a)^j*b^-j)^2 : j in [2..n - 2]]>;
   else
      /* n even: a=(1,2,3), b=(2,...,n) */
      return Group < a, b | a^3, b^(n-1), (b^2*a^-1)^(n div 2), (b*a^-1)^(n-1),
        [((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2 : j in [1..n div 2 - 1]],
        [((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2 : j in [1.. n div 2 - 2]]>;
   end if;
end function;

/* return presentation for S_n on standard generators
  a=(1,2), b=(1,2,...,n) */

PresentationForSymmetricGroup := function (n)
  return Group <a, b | a^2, b^n, (a*b)^(n-1), (a*b^(-1)*a*b)^3,
                       [(a*b^-j*a*b^j)^2 : j in [2 .. n - 2]]>;
end function; 

// presentation on standard generators returned by Conder and Jambor code 
CarmichaelPresentationForAlt := function (n)
   assert n gt 4;
   if IsOdd (n) then
      return Group<s, t | t^3, s^(n - 2), (s * t)^n, (t * t^s)^2, (t * t^(s^2))^2,
                          (t * s^-((n - 3) div 2) * t * s^((n - 3) div 2))^2>;
   else 
      return Group<s, t | t^3, s^(n - 2), (s * t)^(n - 1), (t^-1 * t^s)^2, (t * t^(s^2))^2,
            (t^((-1)^((n -2) div 2)) * s^-((n - 2) div 2) * t * s^((n - 2) div 2))^2>;
   end if;
end function;




