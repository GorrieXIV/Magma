// SubgroupNames(Sym(8));        // to do
// Subgroup(Sym(5),"A5");        // to do

">>> Various group types <<<";
Cputime();

GroupName(AbelianGroup([2,4,7,8]));            // GrpAb
GroupName(Sym(3));                             // GrpPerm 
GroupName(GL(4,5));                            // GrpMat
GroupName(PCGroup(Sym(3)));                    // GrpPC
GroupName(GPCGroup(Sym(3)));                   // GrpGPC
GroupName(FPGroup(Sym(3)));                    // GrpFP
GroupName(CoxeterGroup(GrpFPCox,"B3"));        // GrpFPCox
GroupName(CoxeterGroup(GrpPermCox,"A2B2"));    // GrpPermCox
GroupName(AutomorphismGroup(Alt(5)));          // GrpAuto

">>> Extra special groups <<<";
Cputime();

GroupName(ExtraSpecialGroup(GrpPC,2,2));
GroupName(ExtraSpecialGroup(GrpPC,2,3));
GroupName(ExtraSpecialGroup(GrpPC,2,4));

">>> All possible atoms <<<";
Cputime();

G0:=Group("C10^2*C3");     // cyclic and abelian
G1:=Group("D5");           // dihedral Dn of order 2n
G2:=Group("A5");           // alternating
G3:=Group("S5");           // symmetric

G4:=Group("SL(2,3)");      // linear: GL, SL, AGL, ASL, AGammaL, ASigmaL, 
G5:=Group("SL(2,F3)");     //   PGL, PSL, PGammaL, PSigmaL, SU, PSU, 
G6:=Group("SL_2(3)");      //   PGammaU, PSigmaU, SO, PSO, PGO, PGO+, PGO-, 
G7:=Group("SL2(3)");       //   POmega, POmega+, POmega-, Sp, PSp, PSigmaSp

G8:=Group("S3*GL(4,2)");   // Products 
G9:=Group("C41:C40");      // Split extensions that are not direct products,
                           // [usually with largest action of the quotient group]
G10:=Group("A5wrC2");      // Wreath products

G11:=Group("C2^3.C4");             // unique names returned by GroupName 
                                   // when |G|<512, not multiple of 128
G12:=Group("A5*A_5*A_{5}*Alt(5)"); // name variations
G13:=Group("D10:C8.C2*C3");        // operator order ^ > wr > : > . > *
                                   // (so read left to right in this example)
                                 
G14:=Group("<12,1>");        // Small group database (C3:C4)
G14:=Group("g12n1");         //   same group
G15:=Group("T<12,48>");      // Transitive group database (C2^2*S4)
G15:=Group("t12n48");        //   same group
G16:=Group("C(4,2)");        // Simple groups: Lie Type A,B,C,D,E,F,G, returned
                             //   as matrix groups via standard representation
G17:=Group("Sz(32)");        // Simple groups: Suzuki
G18:=Group("J1*J2*M11");     // Simple groups: sporadic
G19:=Group("PGL(4,3)`2");    // Almost simple group database names

G20:=Group("He11");          // Heisenberg
G21:=Group("Q16");           // Quasi-cyclic groups C_2^n . C2  :
G22:=Group("SD16");          //   Dihedral, generalized quaternion,
G23:=Group("OD16");          //   semi-dihedral, `other-dihedral' one.
G24:=Group("F13");           // Frobenius group Fn of order n(n-1)
                                   
[GroupName(eval "G"*Sprint(n)): n in [1..24]];

assert [#(eval "G"*Sprint(n)): n in [1..24]] eq 
  [ 10, 60, 120, 24, 24, 24, 24, 120960, 1640, 7200, 32, 12960000, 960, 12, 96, 
    47377612800, 32537600, 840935208960000, 24261120, 1331, 16, 16, 16, 13*12 ];

">>> Random small and transitive groups <<<";
Cputime();

[GroupName(G): G in SmallGroups(24)];
[GroupName(G): G in TransitiveGroups(9)];
[GroupName(G): G in TransitiveGroups(8)];
[GroupName(G): G in TransitiveGroups(13)];
[GroupName(G): G in TransitiveGroups(21)];

">>> Maximal subgroups of large simple groups <<<";
Cputime();

for s in ["HS","MCL","Co3","PSL(4,3)","Sz","Rubik"] do
  "G =",s;
  G:=Group(s);
  [GroupName(D`subgroup): D in MaximalSubgroups(G)];
end for;

">>> Maximal subgroups of almost simple groups <<<";
Cputime();

function AlmostSimpleGroup(db,n)
  D:=GroupData(db,n);
  try O<x,y,t,u,v,w>:=D`permrep; ok:=true; catch e ok:=false; end try;
  if not ok then 
    w:=1; try O<x,y,t,u,v>:=D`permrep; ok:=true; catch e ok:=false; end try; 
  end if;
  if not ok then 
    v:=1; try O<x,y,t,u>:=D`permrep; ok:=true; catch e ok:=false; end try; 
  end if;
  if not ok then 
    u:=1; try O<x,y,t>:=D`permrep; ok:=true; catch e ok:=false; end try; 
  end if;
  if not ok then 
    t:=1; try O<x,y>:=D`permrep; ok:=true; catch e ok:=false; end try; 
  end if;
  error if not ok, "Failed to decode AlmostSimpleGroup #"*Sprint(n);
  t:=O!t;
  u:=O!u;
  v:=O!v;
  w:=O!w;
  G:=sub<O|[x,y] cat [eval Sprint(X): X in D`subgens]>;
  return G;
end function;

function MSGPS(G)
  return [D`subgroup: D in MaximalSubgroups(G)];
end function;

D:=AlmostSimpleGroupDatabase();
for n:=1 to 100 do
  G:=AlmostSimpleGroup(D,n);
  n,GroupName(G);
  S:=[GroupName(H): H in MSGPS(G)];
end for;

">>> Small groups of size 1800..1850 <<<";
Cputime();

for n:=1800 to 1850 do
  if n eq 1024 then continue; end if;
  N:=NumberOfSmallGroups(n);
  if N gt 3000 then continue; end if;
  n,N;
  S:=[GroupName(H): H in SmallGroups(n: Warning:=false)];
end for;

">>> TESTING DONE <<<";
Cputime();
