freeze;

/*
  $Id: RootDtm.m 48758 2014-10-27 06:17:25Z don $

  Arjeh Cohen, Scott H Murray and D E Taylor

  30 November 2000

  twisted root data 
  
  January-February 2006
  
  Sergei Haller, Scott H Murray

  Root data for real reflection groups and Lie theory.

  Together with Cartan.m and GrpPermCox.m, this file grew out of the
  old Coxeter.m
*/

import "Cartan.m": nameToType, typeToName, cartanToType, removeTorusFromType, addTorusToType,
  selectTorusFromType, numPosRootsOfType, typeToCartan, isIsogenousTypes,
  isCrystType, isFiniteType, typeToDiagram, tnToType, typeAutos, typeToCoxeterGraph, dualOfType, 
  typeToBasicDegrees, stdRealInj,cmpRealInj;
import "Const.m": maxMultiplicity;
import "MapRootDtm.m" : check_matrices;
import "../../Algebra/AlgLie/rootsystem.m" : fund_rts_from_pos_rts, CartInt;
import "RootDtmExt.m" : computeGA, GA_RF;
import "RootDtmSprs.m" : createRawSprsDtm;

forward nonredSimpleRoots;

declare verbose VerboseRootDtm,        1; // verbosity level; not yet used

/*
**  Verbosity level RootDtmStat is defined on C level. 
**
**      SetVerbose("RootDtmStat", 1);
**
**  to see statistics on hash table usage.
*/


/* 
Basis parameter overwrites intrinsic in some functions
Get alternative
*/
basis_intrinsic := Basis;

// ====================================================
//
// Attributes
//
// ====================================================

// 
// Common to RootSys and RootDtm
// 

declare attributes RootStr:

  // Required fields
  RootSpace,                // The lattice/space which contains the roots
  CorootSpace,              // The lattice/space which contains the coroots
  SimpleRoots,              // The matrix of simple roots in RootSpace
  SimpleCoroots,            // The matrix of simple coroots in CorootSpace

  // Basic fields
  CartanMatrix,             // The Cartan matrix = SimpleRoots*Transpose(SimpleCoroots)
  CoxeterMatrix,            // The Coxeter matrix
  CoxeterGraph,             // The Coxeter graph
  RootSystem,               // The roots written wrt the SimpleRoots
  RootSystemStandard,       // wrt the standard basis
  RootSystemWeight,         // wrt the weight basis
  CorootSystem,             // The coroots written wrt the SimpleCoroots
  CorootSystemStandard,     // wrt the standard basis
  CorootSystemWeight,       // wrt the weight basis
  NumPosRoots,              // The number of positive (co)roots
  Rank,                     // Rank = Nrows(SimpleRoots/SimpleCoroots) = Dim(CartanMatrix)
  Dimension,                // Dim(RootSpace/CorootSpace) = Ncols(SimpleRoots/SimpleCoroots)
  Type,                     // The Cartan type of the root datum
  Name,                     // The name of the Cartan Type

  // Root orbit Schreier structure
  SimpleRep,                // The simple representative of the orbit
  SchreierVect,             // Schreier vector
  BackPointers,             // Back pointer:
                            // r eq R`SchreierVect[r]^R`SimpleReflectionPerms[R`BackPointers[r]]

  // Action of the roots
  ReflectionPerms,          // the action of the (co)roots on themselves
  ReflectionWords,          // the words of the reflections
  ReflectionMatrices,       // the reflections (standard basis only)
  CoreflectionMatrices,     // the coreflections (standard basis only)

  // Properties
  IsIrreducible,            // is there only one component?
  IsSemisimple,             // is rank = dimension?

  // Constants
  MaximumMultiplicity,      // the maximum multiplicity of edges in the Dynkin diagram
  RootNorms,                // the norms of the roots
  CorootNorms,              // the norms of the coroots
  CoxeterForm,              // the inner product matrix for the root space
  DualCoxeterForm,          // the inner product matrix for the coroot space
  RightStrings,             // r+s, 2r+s, r+2s, 3r+s, r+3s, 3r+2s, 2r+3s
  LeftStrings,              // s-r, s-2r, r-2s, s-3r, r-3s
  NontrivialPairs,          // indexed set of pairs <r,s> of positive roots whose sum or difference is a root

  // Derived structures
  CoxeterGroupPerm,         // The Perm Coxeter group, see GrpPermCox.m
  CoxeterGroupFP,           // The FP Coxeter group, see GrpPermCox.m
  CoxeterGroupMat,          // The reflection group, see GrpPermCox.m

  // various constants
  multiplicationData,
  LieConstant_eta,
  cartanIntegers,

  // DEBUG
  SHcount,

  // Basis change
  Vstd,Vrts,Vwgt,           // The vector space spanned by simple roots. w.r.t. standard, root, weight bases
  std2rtsV, rts2stdV,       //
  std2wgtV, wgt2stdV,       //   bijections between them
  rts2wgtV, wgt2rtsV,       //

  Ustd,Urts,Uwgt,           //
  std2rtsU, rts2stdU,       //
  std2wgtU, wgt2stdU,       //  same for coroots
  rts2wgtU, wgt2rtsU;       //

// 
// RootSys only attributes
// 

declare attributes RootSys:

  // Required fields
  BaseField,                // The base ring for the root and coroot spaces
  RealInjection,            // The real injection for the base field

  // Properties
  IsCrystallographic;       // is the Cartan matrix integral?


  // Derived structures
//  StructureConstants,     // The structure constants for the integral Lie algebra
//  NatRepnMxs,             // The matrices corresponding to the root elements of the Lie algebra

  

// 
// RootDtm only attributes
// 
declare attributes RootDtm:


  // Derived structures
  NatRepnMxs,               // The matrices corresponding to the root elements of the Lie algebra
  LieAlgebra,               // The Lie algebra over the integers
  DynkinDigraph,            // The Dynkin digraph
  FundamentalGroup,         // The fundamental group
  FundamentalHom,           // The map from the weight lattice to the fundamental group
  IsogenyGroup,             // The isogeny group
  IsogenyInjToFund,         // The injection of the isogeny group into the fundamental group
  IsogenyProj,              // The projection of the isogeny group onto the root space
  CoisogenyGroup,           // The isogeny group of the dual
  CoisogenyProjFromFund,    // The projection of the coisogeny group onto the fundamental group
  CoisogenyProj,            // The projection of the coisogeny group onto the root space

  // Properties
  IsAdjoint,                // is the isogeny group trivial, and R semisimple?
  IsSimplyConnected,        // is the coisogeny group trivial, and R semisimple?
  IsWeaklyAdjoint,          // is the isogeny group trivial?
  IsWeaklySimplyConnected,  // is the coisogeny group trivial?

  // Constants
  ExtraspecialPairs,        // the extraspecial pairs
  ExtraspecialSigns,        // the extraspecial signs. // frome these other signs are computed.
  Epsilons,                 // epsilon_{rs}

  // Various Hall Polynomials are defined in GrpLie.m

  // automorphism groups
  AutoDD,                   // The DynkinDiagramSymmetryGruop as permutation group on simple roots
  AutoDR,                   // same as DD, but as a permutation group on the whole set of roots
  AutoDW,                   // The direct product of DR and W, the Weyl Group of R
  dd2dr,                    // isomorphism from AutoDD to AutoDR

  // Twisted Root Data:
  // Gamma,                 // the Permutation group acting on the root datum
                            // don't store Gamma, get it by Domain(GammaAction`pa)
  GammaAction;              // this is a record of record format RF_GA


  

baseField := func< R | FieldOfFractions( BaseRing( R ) ) >;




// ====================================================
//
// Construction
//
// The internal functions construct the root data/systems.
// The intrinsics interpret and check inputs, then
// call the appropriate function.
//
// ====================================================

assignSpaces := procedure( ~R );
  // since this function is called when the RootDatum is not
  // yet completely created, we access attributes directly
  K := baseField(R); 
  C := Matrix(ChangeRing(R`CartanMatrix,  K));
  A := Matrix(ChangeRing(R`SimpleRoots,   K));
  B := Matrix(ChangeRing(R`SimpleCoroots, K));
  n := R`Rank; d := R`Dimension;

  // find T1, s.t. A*T1 eq 1
   _,T := EchelonForm(Transpose(A));
  T1   := Transpose(Submatrix(T,1,1,n,d));
  C1   := C^-1;
  C1A  := C1*A;
  T1C  := T1*C;

  // this two are just for intermediate coercion
  Vn := VectorSpace(K,n);
  Vd := VectorSpace(K,d);

  // the space spanned by simple roots:
  R`Vrts     := Vn;
  R`Vstd     := Vd; // VectorSpaceWithBasis(A);
  R`Vwgt     := Vn; // VectorSpaceWithBasis(C);

  R`std2rtsV := hom< R`Vstd->R`Vrts | x :-> x*T1   >;
  R`rts2stdV := hom< R`Vrts->R`Vstd | x :-> x*A    >;
  R`std2wgtV := hom< R`Vstd->R`Vwgt | x :-> x*T1C  >;
  R`wgt2stdV := hom< R`Vwgt->R`Vstd | x :-> x*C1A  >;
  R`rts2wgtV := hom< R`Vrts->R`Vwgt | x :-> x*C    >;
  R`wgt2rtsV := hom< R`Vwgt->R`Vrts | x :-> x*C1   >;

  // find T2, s.t. B*T2 eq 1
  _,T  := EchelonForm(Transpose(B));
  T2   := Transpose(Submatrix(T,1,1,n,d));
  Ct   := Transpose(C);
  Ct1  := Transpose(C1);
  Ct1B := Ct1*B;
  T2Ct := T2*Ct;

  // the space spanned by simple coroots:
  R`Urts     := Vn;
  R`Ustd     := Vd; // VectorSpaceWithBasis(B);
  R`Uwgt     := Vn; // VectorSpaceWithBasis(Ct);

  R`std2rtsU := hom< R`Ustd->R`Urts | x :-> x*T2   >;
  R`rts2stdU := hom< R`Urts->R`Ustd | x :-> x*B    >;
  R`std2wgtU := hom< R`Ustd->R`Uwgt | x :-> x*T2Ct >;
  R`wgt2stdU := hom< R`Uwgt->R`Ustd | x :-> x*Ct1B >;
  R`rts2wgtU := hom< R`Urts->R`Uwgt | x :-> x*Ct   >;
  R`wgt2rtsU := hom< R`Uwgt->R`Urts | x :-> x*Ct1  >;

end procedure;

createRawSys := function(A,B)
  R := HackobjCreateRaw( RootSys );
  R`Rank              := Nrows(A);
  R`Dimension         := Ncols(A);
  R`SimpleRoots       := A;
  R`SimpleCoroots     := B;
  return R;  
end function;

/*
**    if signs or ga can't be computed before calling
**    createRawDtm (and thus InternalCreateRootDatum(R))
**
**    then we use 100 for signs and 100 for ga
**    (both nonsense-values, ensuring that there is no 
**    such root datum available already)
**    and then drop and reinsert the root datum
**
**    for example :
**      S := createRawDtm(A,B, 100, ga);
**      ... compute signs ...
**      InternalDropRootDatum(S);
**      S`ExtraspecialSigns := signs;
**      S := InternalCreateRootDatum(S);
**    
**
**    same for ga.
**
*/
createRawDtm := function( A, B, type, signs, ga )
  R := HackobjCreateRaw( RootDtm );
  R`Rank                    := Nrows(A);
  R`Dimension               := Ncols(A);
  R`SimpleRoots             := A;
  R`SimpleCoroots           := B;
  R`Type                    := type;
  R`ExtraspecialSigns       := signs;
  R`GammaAction             := ga;
  /*  
   *  at this stage
   *     a) R must be comparable to other Data
   *     b) Hash(R) must be computable
   */
  RD, is_new := InternalCreateRootDatum(R); 
  if is_new then vprint ROOTS,1 : "*"; end if;
  return RD, is_new;
  // returns  a root datum  and  a boolean if it is new (in which case it was inserted)
end function;


rootSystem := function( A, B, C, type, realinj )
  R := HackobjCreateRaw( RootSys );
  n := Nrows(A);   R`Rank      := n;
  d := Ncols(A);   R`Dimension := d;
  k := BaseRing(A);
  if Category( k ) eq RngInt then
    k := Rationals();  
  end if;
  A := ChangeRing( A, k );  B := ChangeRing( B, k );
  C := ChangeRing( C, k );
  V := VectorSpace( k, d );
  R`BaseField := k;    R`CartanMatrix := C;
  R`RealInjection := realinj;
  R`RootSpace := V;    R`CorootSpace := V;
  R`SimpleRoots := A;  R`SimpleCoroots := B;
  R`Type := type;      R`Name := typeToName( type );
  assignSpaces(~R);
  return R;
end function;

normalisedRootDatumMxs := function( A, B )
  T := func< x | Transpose(x) >;
  A := ChangeRing( A, Integers() );
  Ap, P := HermiteForm( T(A) );
  Ap := T( ChangeRing( Ap, Rationals() ) );
  Bp := B * P^-1; //T( T(P)^-1 * T(B) );  // Huh?
  //Bp := T( Ap^-1 * A * T(B) );
  return ChangeRing( Ap, Integers() ), ChangeRing( Bp, Integers() );
end function;

checkSigns := function( R )
    signs := R`ExtraspecialSigns;
    case ExtendedCategory(signs):
    when ExtendedCategory(1): 
        if not signs in [1,-1] then
            return "Signs must be +1 or -1";
        end if;
        R`ExtraspecialSigns := [Integers()| signs : i in [1..NumExtraspecialPairs( R )]];
    when SeqEnum[RngIntElt]:
        if not {s:s in signs} subset [1,-1] then
            return "Signs must be +1 or -1";
        end if;
        if #signs ne NumExtraspecialPairs( R ) then
            return Sprintf("The number of signs must be %o", NumExtraspecialPairs( R ));
        end if;
    when SeqEnum[Any]: // IsNull(signs) eq true
        if NumExtraspecialPairs( R ) ne 0 then
            return Sprintf("The number of signs must be 0");
        end if;
    else:
        return "signs have wrong category: " * Sprintf("%o",ExtendedCategory(signs));
    end case;

    return "";
end function;


rootDatum := function( A, B, C, type, signs : twist:=1, NoSignCheck:=true )
  F := CoveringStructure(BaseRing(A), Rationals());
  F := CoveringStructure(BaseRing(B), F);
  A := Matrix(F,A);     // make sure we are consistent for Hashes
  B := Matrix(F,B);     // 
  
  N := numPosRootsOfType( type );

  if Category(twist) eq Rec then
    // assume ga is correct
    ga := twist;
  else 
    // fake invalid ga. 
    // the real ga is computed below
    ga := rec<GA_RF|gamma := Sym(1), perm_ac := hom<Sym(1)->Sym(1)|[]>,
                    mats_rt := [Matrix(1,[1])], mats_co := []>;
  end if;

  R,is_new := createRawDtm(A,B,type,signs,ga);

  // if the required root datum already exists ...
  if not is_new then return R; end if;


  R`multiplicationData := [ [Parent([Parent(<1,1,1,1>)|])|] : i in [1..N] ];
  R`LieConstant_eta    := [ [Integers()|] : i in [1..2*N] ];
  R`cartanIntegers     := [ [Integers()|] : i in [1..2*N] ];

  R`CartanMatrix := C;
  R`NumPosRoots  := N;
  R`Name := typeToName( type );

  /*
   *  dimension and field could be deduced from R (in principle)
   *  inside CreateRootVectorSpace.
   *  it is harder to get this info on C level, so we just pass it along.
   */
  d := R`Dimension;
  V := CreateRootVectorSpace( Rationals(), d, R );
  U := CreateRootVectorSpace( Rationals(), d, R : Coroots );

  R`RootSpace   := V; 
  R`CorootSpace := U;

  assignSpaces(~R);
  if not NoSignCheck then
    err := checkSigns(R);
    if err ne "" then
      InternalDropRootDatum(R);
      error err;
    end if;
  end if;
  
  if Category(twist) ne Rec then
    ga := computeGA(R,twist);
    // drop from hash table
    InternalDropRootDatum(R);
    // return if myga is an error string
    if Category(ga) eq MonStgElt then
        error ga;
    end if;
    // assign correct gamma action
    R`GammaAction := ga;
    // reinsert into hash table
    S, is_new := InternalCreateRootDatum(R);
    if is_new then vprint ROOTS,1 :"*"; end if;
    if not is_new then return S; end if;
  end if;
  
  return R;
end function;


// the functions up to and including myB are modified from
// functions in Lattice/cons.m
ZZ := IntegerRing();
QQ := RationalField();

function MatrixR(X)
    if BaseRing(Parent(X)) cmpeq ZZ then
	return ChangeRing(Parent(X), QQ) ! X;
    else
	return X;
    end if;
end function;

function MatrixZ(X)
    return ChangeRing(Parent(X), ZZ) ! X;
end function;

function PrimitiveMatrix(X)
    g := GCD(Eltseq(X));
    if g ne 1 then
	X := Parent(X) ! [x div g: x in Eltseq(X)];
    end if;
    return X, g;
end function;

function IntegralMatrix(X)
    d := LCM([Denominator(x): x in Eltseq(X)]);
    return MatrixZ(d * X), d;
end function;

myB := function( C )
  B := MatrixR(C)^-1;
  B := PrimitiveMatrix(IntegralMatrix(B));
  B := MatrixR(B);
  F := B * C * Transpose(B);
  B := B*LCM([Denominator(x): x in Eltseq(F)])/GCD(Eltseq(MatrixZ(F)));
  return B;
end function;

insertTorusIntoAB := procedure( ~A, ~B, type )
  torus_start := 1;
  for tt in type do
    if (tt[1] eq "T") then
      torus_dim := tt[3];
      blk := ZeroMatrix(CoefficientRing(A), NumberOfRows(A), torus_dim);
      A := HorizontalJoin(A, blk);
      B := HorizontalJoin(B, blk);
      nc := NumberOfColumns(A);
      for i in [0..(torus_dim-1)] do
        for j in [nc..(torus_start+i+1) by -1] do
          SwapColumns(~A, j, j-1);
  	  SwapColumns(~B, j, j-1);
        end for;
      end for;
      torus_start +:= torus_dim;
    else
      torus_start +:= #(tt[2]);
    end if;
  end for;
end procedure;

ABByInjection := function( C, type, inj )
  n := Ncols( C );
  L := StandardLattice( n );
  M := LatticeWithBasis( myB(C) );
  G, h := M / L;
  a, ident := IsIsomorphic( Codomain(inj), G );
  if not a then
    error "Injection has invalid codomain";
  end if;
  gens := [ ident(inj(g)) : g in Generators( Domain(inj) ) ];
  K := sub< M | L, [ g@@h : g in gens ] >;
  A := Matrix( [ CoordinateVector(K,L.i) : i in [1..n] ] );
  B := Transpose( Matrix( [ CoordinateVector(M,K.i) : i in [1..n] ] ) );
  return normalisedRootDatumMxs( A, B );
end function;
  
rootDatumByInjection := function( C, type, inj, signs )
  sstype := removeTorusFromType( type );
  A, B := ABByInjection( C, sstype, inj );
  insertTorusIntoAB( ~A, ~B, type );
  return rootDatum( A, B, C, sstype, signs );
end function;

ABByIsogeny := function( C, type, isogeny )
  case Category(isogeny) :
  when MonStgElt :
    I := Parent(C)!1;
    if isogeny eq "Ad" then
      return I, Transpose(C);
    elif isogeny eq "SC" then
      return C, Transpose(I);
    else
      error "Invalid isogeny";
    end if;
  when RngIntElt :
    G := FundamentalGroup( C );  order := #G;
    if NumberOfGenerators( G ) ne 1 then
      error "Integer isogeny only for cyclic isogeny groups";
    elif order mod isogeny ne 0 then
      error "Isogeny must divide", order;
    end if;
    _,inj := sub< G | (order div isogeny)*G.1 >;
    return ABByInjection( C, type, inj );
  when Map :
     return ABByInjection( C, type, isogeny );
  else
    error "Isogeny parameter must be a string, an integer or a map";
  end case;
end function;
  
rootDatumByIsogeny := function( C, type, isogeny, signs : twist := 1 )
  sstype := removeTorusFromType( type );
  A, B := ABByIsogeny( C, sstype, isogeny );
  insertTorusIntoAB(~A, ~B, type);
  R := rootDatum( A, B, C, sstype, signs : twist := twist );
  if Category( isogeny ) eq MonStgElt then
    if isogeny eq "Ad" then
      R`IsAdjoint := Rank(R) eq Dimension(R);
      R`IsWeaklyAdjoint := true;
    elif isogeny eq "SC" then
	  R`IsSimplyConnected := Rank(R) eq Dimension(R);
      R`IsWeaklySimplyConnected := true;
    end if;
  end if;
  return R;
end function;

rootDatumByList := function( type, isogeny, signs : twist := 1  )
  sstype, isogeny := removeTorusFromType( type : Isogenies := isogeny);
  C := typeToCartan( sstype );
  i := 1;  pos := 1;
  C1 := Submatrix( C, pos, pos, #sstype[i][2], #sstype[i][2] );
  A, B := ABByIsogeny( C1, [* sstype[i] *], isogeny[i] ); 
  for i in [2..#sstype] do
    pos := pos + #(sstype[i-1][2]);
    C1 := Submatrix( C, pos, pos, #sstype[i][2], #sstype[i][2] );
    A1, B1 := ABByIsogeny( C1, [* sstype[i] *], isogeny[i] ); 
    A := DiagonalJoin( A, A1 );  B := DiagonalJoin( B, B1 );
  end for;
  insertTorusIntoAB(~A, ~B, type);
  return rootDatum( A, B, C, sstype, signs : twist := twist );
end function;

intrinsic RootSystem( A::Mtrx, B::Mtrx : RealInjection:=false, Nonreduced := {} ) -> RootSys
{The root system whose simple (co)roots are the rows of the matrix A (B)}
local t;
  require Nrows(A) eq Nrows(B) : "Matrices must have the same number of rows";
  require Ncols(A) eq Ncols(B) : "Matrices must have the same number of columns";
  rank := Nrows(A);  dim := Ncols(A);
  F := FieldOfFractions( BaseRing(A) );
  require F eq FieldOfFractions( BaseRing(B) ) : "Matrices must be defined over the same field";
  A := ChangeRing( A, F );  B := ChangeRing( B, F );
  C := Matrix( A*Transpose(B) );
  ok, realinj := IsCartanMatrix( C : RealInjection:=RealInjection );
  require ok : "A*Transpose(B) must be a Cartan matrix";
  type := cartanToType( C : RealInjection:=realinj, nonred:=Nonreduced );
  require forall(t){ t : t in type | #t[1] eq 1 and t[1] ne "X" or t[1] eq "BC" } : 
  "Not a finite root system in rows ", t[2];
  return rootSystem( A, B, C, type, realinj );
end intrinsic;

intrinsic RootDatum( A::Mtrx, B::Mtrx : Signs := 1, Twist := 1, 
Nonreduced := {}, NoSignCheck:=false ) -> RootDtm
{The root datum whose simple (co)roots are the rows of the matrix A (B)}
/*
 *  the parameter Twist is processed by the function computeGA
 *  see there for description of possible values
 *  
 */
local t;
  require Nrows(A) eq Nrows(B) : "Matrices must have the same number of rows";
  require Ncols(A) eq Ncols(B) : "Matrices must have the same number of columns";
  rank := Nrows(A);  dim := Ncols(A);
  F := CoveringStructure(BaseRing(A), Rationals());
  F := CoveringStructure(BaseRing(B), F);
  A := Matrix(F,A);
  B := Matrix(F,B);
  C := Matrix( A*Transpose(B) );
  is_c,newC := IsCoercible( MatrixAlgebra(Integers(),rank), C);
  if is_c then C := newC; end if;
  
  require IsCartanMatrix( C ) : "A*Transpose(B) must be a Cartan matrix";
  type := cartanToType( C : nonred:=Nonreduced );
  is_fin,t := isFiniteType(type);
  require is_fin :  "Not a finite root datum in rows ", t[2];
  R := rootDatum( A, B, C, type, Signs : twist := Twist, 
    NoSignCheck:=NoSignCheck );
  return R;
end intrinsic;


intrinsic RootSystem( C::AlgMatElt : RealInjection:=false, Nonreduced := {},
  Symmetric:=false, BaseField:="NumberField" ) -> RootSys
{The root system with Cartan (Coxeter) matrix C}
// RealInjection only applies to Cartan matrices
// Symmetric and BaseField only apply to Coxeter matrices
local t;
  F := FieldOfFractions( BaseRing(C) );
  A := ChangeRing( C, F );
  if IsCoxeterMatrix( C ) then
    M := C;  
    C, realinj := CartanMatrix( C : Symmetric:=Symmetric,BaseField:=BaseField );
  else
    ok, realinj := IsCartanMatrix( C : RealInjection:=RealInjection );
    if ok then
      M := CoxeterMatrix( C : RealInjection:=realinj );
      require Category( M ) ne MonStgElt : M;
    else
      error "Not a Coxeter matrix or Cartan matrix";
    end if;
  end if;
  type := cartanToType( C : RealInjection:=realinj, nonred:=Nonreduced );
  is_fin,t := isFiniteType(type);
  require is_fin :  "Not a finite root system in rows ", t[2];
  return rootSystem( Parent(C)!1, Transpose(C), C, type, realinj );
end intrinsic;
  
intrinsic RootDatum( C::AlgMatElt : Isogeny := "Ad", Signs := 1, Twist := 1, 
  Nonreduced := {} ) -> RootDtm
{The root datum with Cartan (Coxeter) matrix C}
local t;
  if IsCoxeterMatrix( C ) then
    C := CartanMatrix( C );
  else
    require IsCartanMatrix( C ) : "Argument not a Coxeter or Cartan matrix";
  end if;
  require IsCrystallographic( C ) : "Root data must be crystallographic";
  type := cartanToType( C : nonred:=Nonreduced );
  is_fin,t := isFiniteType(type);
  require is_fin :  "Not a finite root datum in rows ", t[2];
  R := rootDatumByIsogeny( C, type, Isogeny, Signs : twist:=Twist );
  return R;
end intrinsic;


intrinsic RootSystem( G::GrphUnd : Nonreduced := {},
  Symmetric:=false, BaseField:="NumberField" ) -> RootSys
{The root system with Coxeter graph G}
  R := RootSystem( CoxeterMatrix( G ) : Nonreduced:=Nonreduced,
    Symmetric:=Symmetric, BaseField:=BaseField );
  R`CoxeterGraph := G;
  return R;
end intrinsic;


intrinsic RootSystem( D::GrphDir : Nonreduced := {} ) -> RootSys
{The root system with Dynkin digraph D}
  R := RootSystem( CartanMatrix( D ) : Nonreduced:=Nonreduced );
  R`DynkinDigraph := D;
  return R;
end intrinsic;

intrinsic RootDatum( D::GrphDir : Isogeny := "Ad", Signs := 1, Twist := 1, 
  Nonreduced := {}  ) -> RootDtm
{The root datum with Dynkin digraph D}
  R := RootDatum( CartanMatrix( D ) : Isogeny:=Isogeny, Signs := Signs, 
    Twist := Twist, Nonreduced := Nonreduced );
  R`DynkinDigraph := D;
  return R;
end intrinsic;


intrinsic IrreducibleRootSystem( X::MonStgElt, n::RngIntElt : Symmetric:=false, 
BaseField:="NumberField" ) -> RootSys
{The irreducible root system with Cartan name X_n}
  type := tnToType( X, n );
  require isFiniteType( type ) : "Not the Cartan name of a finite group";
  C, realinj := typeToCartan( type : Symmetric:=Symmetric, BaseField:=BaseField );
  if Category(BaseRing(C)) eq RngInt then
    C := ChangeRing( C, Rationals() );
  end if;
  return rootSystem( Parent(C)!1, Transpose(C), C, type, realinj );
end intrinsic;

intrinsic IrreducibleRootDatum( X::MonStgElt, n::RngIntElt : Isogeny := "Ad",
  Signs := 1 ) -> RootDtm
{The irreducible root datum with Cartan name X_n}
  type := tnToType( X, n );
  require isFiniteType( type ) : "Not the Cartan name of a finite group";
  require isCrystType( type ) : "Not a crystallographic Cartan name";
  require type[1][1] notin "HI" : "Cartan type must be crystallographic";
  C := typeToCartan( type );
  return rootDatumByIsogeny( C, type, Isogeny, Signs );
end intrinsic;

typeToRootSystem := function( type : Symmetric:=false, BaseField:="NumberField" )
  sstype := removeTorusFromType( type );
  C, realinj := typeToCartan( sstype : Symmetric:=Symmetric, BaseField:=BaseField );
  A := Parent(C)!1;
  B := Transpose(C);
  insertTorusIntoAB(~A, ~B, type);
  return rootSystem( A, B, C, sstype, realinj );
end function;

intrinsic RootSystem( N::MonStgElt : Symmetric:=false, BaseField:="NumberField" ) -> RootSys
{The root system with Cartan name N}
  type := nameToType(N : allowtorus );
  require Category( type ) ne BoolElt : "Invalid Cartan name";
  require isFiniteType( type ) : "Not a finite root system";
  return typeToRootSystem( type : Symmetric:=Symmetric, BaseField:=BaseField );
end intrinsic;

intrinsic RootDatum( N::MonStgElt : Isogeny := "Ad", Signs := 1, Twist := 1 ) -> RootDtm
{The root datum with Cartan name N}
//   this function was defined but not used:
//   simpleToRootDatum := function( t : Isogeny := "Ad", Signs := 1  )
//     return rootDatumByIsogeny( typeToCartan( [*t*]), [*t*], Isogeny, Signs );
//   end function;
  type := nameToType(N : allowtorus ); 
  require Category( type ) ne BoolElt : "Invalid Cartan name";
  require isFiniteType( type ) : "Not a finite root datum";
  require isCrystType( removeTorusFromType( type ) ) : "Not a crystallographic Cartan name";
  case Category( Isogeny ) :
  when List :
    R := rootDatumByList( type, Isogeny, Signs : twist := Twist );
  when Map, MonStgElt, RngIntElt :
    R := rootDatumByIsogeny( typeToCartan( removeTorusFromType( type) ), type, Isogeny, Signs : twist := Twist  );
  else
    error "Invalid isogeny parameter";
  end case;
  return R;
end intrinsic;

standardMatrices := function( t, n )
  type := tnToType( t, n );
  t := type[1][1];
  case t :
  when "A":
    A := Matrix( Integers(), n, n+1, [0:i in [1..n*(n+1)]] );
    for i in [1..n] do
      A[i,i] := 1;  A[i,i+1] := -1;
    end for;
    B := A;
  when "B", "C", "BC":
    A := Matrix( Integers(), n, n, [0:i in [1..n^2]] );
    for i in [1..n-1] do
      A[i,i] := 1;  A[i,i+1] := -1;
    end for;
    A[n,n] := 1;
    B := Matrix( Integers(), n, n, [0:i in [1..n^2]] );
    for i in [1..n-1] do
      B[i,i] := 1;  B[i,i+1] := -1;
    end for;
    B[n,n] := 2;
    if t eq "C" then  tmp := A;  A := B;  B := tmp;  end if;
  when "D":
    A := Matrix( Integers(), n, n, [0:i in [1..n^2]] );
    for i in [1..n-1] do
      A[i,i] := 1;  A[i,i+1] := -1;
    end for;
    if n gt 1 then  A[n,n-1] := 1;  end if;
    A[n,n] := 1;
    B := A;
  when "E":
    A := Matrix( Rationals(), 8,8, [0:i in [1..64]] );
    for i in [1..8] do
      A[1,i] := -1/2;
    end for;
    A[2,6] := 1;  A[2,7] := -1;
    A[3,6] := 1;  A[3,7] := 1;
    for i in [4..8] do
      A[i,8-i+1] := 1;  A[i,8-i+2] := -1;
    end for;
    A := ExtractBlock( A, 1,1, n,8 );  B := A;
  when "F":
    A := Matrix( Rationals(), 4, 4,
         [ 1,-1,0,0, 0,1,-1,0, 0,0,1,0, -1/2,-1/2,-1/2,1/2 ] );
    C := ChangeRing( typeToCartan( type ), Rationals() );
    B := Transpose( A^-1 * C );
  when "G":
    F := CyclotomicField( 12 ); xi := F.1;
    realinj := stdRealInj( F );
    xi := RootOfUnity( 3, F );  i := RootOfUnity( 4, F );
    cos := (xi+xi^-1)/2;  
    print cos, realinj(cos);
    cos := (Real(realinj(cos)) ge 0) select cos else -cos;
    A := Matrix( F, 2, 2, [ 1, 0, -3/2, -i*cos/2 ] ); 
    C := ChangeRing( typeToCartan( type ), F );
    B := Transpose( A^-1 * C );
  when "I":
    F := CyclotomicField( Lcm(4,(n mod 2 eq 0) select 2*n else n) );
    realinj := stdRealInj( F );
    z := RootOfUnity( 2*n, F );  i := RootOfUnity( 4, F );
    cos := (z+z^-1)/2;  sin := -i*(z-z^-1)/2;
    if Real(realinj(cos)) ge 0 then  cos:=-cos;  sin:=-sin;  end if;
    M := MatrixAlgebra( F, 2 );
    A := M![ 1, 0, -cos, sin ];  B := 2*A;
    C := A * Transpose( B );
  when "H":
    F := CyclotomicField( 20 );
    realinj := stdRealInj( F );
    z := RootOfUnity( 10, F );  i := RootOfUnity( 4, F );
    cos := (z+z^-1)/2;  sin := -i*(z-z^-1)/2;
    if Real(realinj(cos)) ge 0 then  cos:=-cos;  sin:=-sin;  end if;
    P := PolynomialRing( F ); X := P.1;
    c := Roots( X^2 - (1-1/(4*sin^2)) )[1][1];
    c := (Real(realinj(c)) ge 0) select c else -c;
    if n eq 3 then
      A := Matrix(3,3, [ sin,-cos,0, 0,1,0, -cos/(2*sin),-1/2,c ] );
      C := SymmetricMatrix( [ 2, -2*cos,2, 0,-1,2 ] );
    else
      d := Roots( X^2 - (1-1/(4*c^2)) )[1][1];
      A := Matrix(4,4, [ sin,-cos,0,0, 0,1,0,0, -cos/(2*sin),-1/2,c,0, 0,0,-1/(2*c),d ] );
      C := SymmetricMatrix( [ 2, -2*cos,2, 0,-1,2, 0,0,-1,2 ] );
    end if;
    B := 2*A;  C := A * Transpose( B );
  when "X" :
    error "Not a valid Cartan name";
  else
    error "Not the Cartan name of a finite group";
  end case;
  if not assigned realinj then  realinj := stdRealInj(BaseRing(A));  end if;
  C := Matrix( A * Transpose( B ) );
  return A, B, C, type, realinj;
end function;

intrinsic StandardRootSystem( X::MonStgElt, n::RngIntElt ) -> RootDtm
{The standard root system with Cartan name X_n}
  A, B, C, type, realinj := standardMatrices( X, n );
  R := rootSystem( A, B, C, type, realinj );
  if type[1][1] eq "A" then
    I := MatrixAlgebra(Rationals(),n+1)!1;
    R`CoxeterForm := I;  R`DualCoxeterForm := I;
  elif type[1][1] eq "E" then
    I := MatrixAlgebra(Rationals(),8)!(1/2);
    R`CoxeterForm := I;  R`DualCoxeterForm := I;
  end if;
  return R;
end intrinsic;

intrinsic StandardRootDatum( X::MonStgElt, n::RngIntElt : Signs := 1 ) -> RootDtm
{The standard root datum with Cartan name X_n}
 require X in "AaBbCcDd" : "Classical types (A,B,C,D) only";
//   if X notin "AaBbCcDd" then
//     print "WARNING! exceptional types do not work yet";
//   end if;
  A, B, C, type := standardMatrices( X, n );
  R := rootDatum( A, B, C, type, Signs );
  return R;
end intrinsic;


intrinsic RootSystem( R::RootDtm ) -> RootSys
{The root system of the root datum R}
  S := RootSystem( SimpleRoots( R ), SimpleCoroots( R ) );
  for field in [ "CoxeterMatrix", "CoxeterGraph",
  "CorootSystem", "NumPosRoots", "Rank", "Dimension", "Type", "Name", 
  "SimpleRep", "SchreierVect", "BackPointers", "IsIrreducible", "IsSemisimple",
  "MaximumMultiplicity", "RootNorms", "CorootNorms", "CoxeterForm",
  "DualCoxeterForm", "RightStrings", 
  "LeftStrings", "CoxeterGroupPerm", "CoxeterGroupFP", "CoxeterGroupMat" ] do
    if assigned R``field then
      S``field := R``field;
    end if;
  end for;
  return S;
end intrinsic;

intrinsic RootDatum( R::RootSys : Signs := 1 ) -> RootDtm
{The root datum of the root system R}
  require IsCrystallographic( R ) : "R must be crystallographic";
  n := Rank( R );  d := Dimension( R );
  A := SimpleRoots( R );  B := SimpleCoroots( R );

  require (Category(BaseRing(A)) eq RngInt 
       and Category(BaseRing(B)) eq RngInt)
    or forall{ <i,j> : i in [1..n], j in [1..d] 
                     | A[i,j] in Integers() and 
                       B[i,j] in Integers() } 
    : "The simple roots and coroots must have integral coordinates";

  S := RootDatum( A, B : Signs := Signs );

  for field in [ "CartanMatrix", "CoxeterMatrix", "CoxeterGraph", "RootSystem",
  "CorootSystem", "NumPosRoots", "Rank", "Dimension", "Type", "Name", 
  "SimpleRep", "SchreierVect", "BackPointers",  
  "IsIrreducible", "IsSemisimple", "MaximumMultiplicity",
  "RootNorms", "CorootNorms", "CoxeterForm", "DualCoxeterForm", "RightStrings",
  "LeftStrings", "CoxeterGroupPerm", "CoxeterGroupFP", "CoxeterGroupMat" ] do
    if assigned R``field then
      S``field := R``field;
    end if;
  end for;

  return S;
end intrinsic;
  
intrinsic ToralRootSystem( d::RngIntElt ) -> RootSys
{The toral root system of dimension d}
  A := Matrix( 0, d, [ Integers() | ] );
  return RootSystem( A, A );
end intrinsic;
  
intrinsic ToralRootDatum( d::RngIntElt : Twist := 1 ) -> RootDtm
{The toral root datum of dimension d}
  A := Matrix( 0, d, [ Integers() | ] );
  return RootDatum( A, A : Twist:=Twist );
end intrinsic;
  
intrinsic TrivialRootSystem() -> RootSys
{The trivial root system}
  return ToralRootSystem(0);
end intrinsic;
  
intrinsic TrivialRootDatum() -> RootDtm
{The trivial root datum}
  return ToralRootDatum(0);
end intrinsic;
  


// ====================================================
//
// Operations
//
// ====================================================

// ----------------------------------------------------
//
// (Co)root spaces
//
intrinsic IsRootSpace( V::ModTupFld ) -> BoolElt
{True iff V is a root space}
  return assigned V`RootDatum and not V`Coroots;
end intrinsic;

intrinsic IsCorootSpace( V::ModTupFld ) -> BoolElt
{True iff V is a coroot space}
  return assigned V`RootDatum and V`Coroots;
end intrinsic;

intrinsic IsInRootSpace( v::ModTupFldElt ) -> BoolElt
{True iff v is in a root space}
  return IsRootSpace( Parent(v) );
end intrinsic;

intrinsic IsInCorootSpace( v::ModTupFldElt ) -> BoolElt
{True iff v is in a coroot space}
  return IsCorootSpace( Parent(v) );
end intrinsic;

intrinsic RootDatum( V::ModTupFld ) -> BoolElt
{True iff V is a root space}
  require assigned V`RootDatum :
    "Not a (co)root space";
  return V`RootDatum;
end intrinsic;




// ----------------------------------------------------
//
// Required fields
//
// These fields must be set in any valid root datum or root system
//

intrinsic BaseRing( R::RootSys ) -> Fld
{Base ring for the root and coroot spaces of the root system R}
  return R`BaseField;
end intrinsic;

intrinsic BaseField( R::RootSys ) -> Fld
{Base ring for the root and coroot spaces of the root system R}
  return R`BaseField;
end intrinsic;

intrinsic BaseRing( R::RootDtm ) -> Rng
{Base ring for the root and coroot spaces of the root datum R}
  F := CoveringStructure(BaseRing(R`SimpleRoots), Rationals());
  F := CoveringStructure(BaseRing(R`SimpleCoroots), F);
  return F;
end intrinsic;



intrinsic RealInjection( R::RootSys ) -> Map
{The real injection for the base ring of the root system R}
  return R`RealInjection;
end intrinsic;



intrinsic RootSpace( R::RootStr ) -> ModTupFld
{The space containing the roots of R}
  return R`RootSpace;
end intrinsic
intrinsic CorootSpace( R::RootStr ) -> ModTupFld
{The space containing the coroots of R}
  return R`CorootSpace;
end intrinsic



intrinsic FullRootLattice( R::RootDtm ) -> Lat, Map
{The lattice X containing the roots of R. A map into the root space is also returned.}
  d := Dimension(R);
  L := StandardLattice(d);
  return L,Coercion(L,RootSpace(R));
end intrinsic

intrinsic FullCorootLattice( R::RootDtm ) -> Lat, Map
{The lattice Y containing the coroots of R. A map into the coroot space is also returned.}
  d := Dimension(R);
  L := StandardLattice(d);
  return L,Coercion(L,CorootSpace(R));
end intrinsic





intrinsic RootLattice( R::RootDtm ) -> Lat, Map
{The lattice spanned by the roots of R. A map into the root space is also returned.}
  L := Lattice( SimpleRoots(R) );
  return L,Coercion(L,RootSpace(R));
end intrinsic

intrinsic CorootLattice( R::RootDtm ) -> Lat, Map
{The lattice spanned by the coroots of R. A map into the coroot space is also returned.}
  L := Lattice( SimpleCoroots(R) );
  return L,Coercion(L,CorootSpace(R));
end intrinsic






intrinsic SimpleRoots( R::RootStr : Basis := "Standard") -> Mtrx
{The simple roots of R as the rows of a matrix}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  
  if Basis cmpeq "Standard" then
  	return R`SimpleRoots;
  else
	return Matrix([ BasisChange(R, (R`SimpleRoots)[i] : OutBasis := Basis) : i in [1..Rank(R)] ]);
  end if;
end intrinsic

intrinsic SimpleCoroots( R::RootStr : Basis := "Standard") -> Mtrx
{The simple coroots of R as the rows of a matrix}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";

  if Basis cmpeq "Standard" then
  	return R`SimpleCoroots;
  else
  	return Matrix([ BasisChange(R, (R`SimpleCoroots)[i] : OutBasis := Basis, Coroots := true) : i in [1..Rank(R)] ]);
  end if;
end intrinsic




// ----------------------------------------------------
//
// Derived fields
//

intrinsic CartanMatrix( R::RootStr ) -> AlgMatElt
{The Cartan matrix of R}
  if not assigned R`CartanMatrix then
    R`CartanMatrix := Matrix( R`SimpleRoots * Transpose(R`SimpleCoroots) );
  end if;
  return R`CartanMatrix;
end intrinsic

intrinsic CoxeterMatrix( R::RootSys ) -> AlgMatElt
{The Coxeter matrix of R}
  if not assigned R`CoxeterMatrix then
    R`CoxeterMatrix := CoxeterMatrix( CartanMatrix( R ) : 
      RealInjection := RealInjection(R) );
  end if;
  return R`CoxeterMatrix;
end intrinsic;

intrinsic CoxeterMatrix( R::RootDtm ) -> AlgMatElt
{The Coxeter matrix of R}
  if not assigned R`CoxeterMatrix then
    R`CoxeterMatrix := CoxeterMatrix( CartanMatrix( R ) );
  end if;
  return R`CoxeterMatrix;
end intrinsic;

intrinsic CoxeterGraph( R::RootStr ) -> GrphUnd
{The Coxeter graph of R}
  if not assigned R`CoxeterGraph then
    R`CoxeterGraph := CoxeterGraph( CoxeterMatrix( R ) );
  end if;
  return R`CoxeterGraph;
end intrinsic;

intrinsic DynkinDigraph( R::RootStr ) -> GrphDir
{The Coxeter graph of R}
  require IsCrystallographic(R) :
  "R must be crystallographic";
  if not assigned R`DynkinDigraph then
    R`DynkinDigraph := (Rank(R) ne 0) select DynkinDigraph( CartanMatrix( R ) )
      else DynkinDigraph( "" );
  end if;
  return R`DynkinDigraph;
end intrinsic;

intrinsic Rank( R::RootStr ) -> RngIntElt
{The rank of R}
  if not assigned R`Rank then
    R`Rank := Nrows( R`SimpleRoots );
  end if;
  return R`Rank;
end intrinsic;

intrinsic Dimension( R::RootStr ) -> RngIntElt
{The dimension of R}
  if not assigned R`Dimension then
    R`Dimension := Dimension( RootSpace(R) );
  end if;
  return R`Dimension;
end intrinsic;


toType := function( R )
// SH, May 2006
//          Type must be assigned upon creation! 
//          (otherwise we can't recognise non-reduced types correctly)
//          see where it fails!
//
    if not assigned R`Type then
        print "WARNING: toType called, but R`Type not assigned.";
        print "         Please mail your magma run to sergei@maths.usyd.edu.au";
        R`Type := cartanToType( CartanMatrix( R ) );
    end if;
    return R`Type;
end function;

intrinsic CartanName( R::RootStr ) -> MonStgElt
{The Cartan name of R}
  if not assigned R`Name then
    R`Name := typeToName( toType( R ) );
  end if;
  return R`Name;
end intrinsic;



intrinsic FundamentalGroup( R::RootDtm ) -> GrpAb, Map
{The fundamental group of R}
  if not assigned R`FundamentalGroup then
    RPhi := Lattice( R`SimpleRoots );
    R`FundamentalGroup, R`FundamentalHom := WeightLattice( R ) / RPhi;
  end if;
  return R`FundamentalGroup, R`FundamentalHom;
end intrinsic;



intrinsic IsogenyGroup( R::RootDtm ) -> GrpAb, Map
{The isogeny group of R}
  if not assigned R`IsogenyGroup then
    X := StandardLattice( Dimension( R ) );
    RPhi := Lattice( R`SimpleRoots );
    G, g := X / RPhi;
    R`IsogenyGroup := G;
    R`IsogenyProj := g;
    if IsSemisimple( R ) then
      F, f := FundamentalGroup( R );
      R`IsogenyInjToFund := hom< G -> F | x :-> f( x@@g ) >;
    end if;
  end if;
  if IsSemisimple( R ) then 
    return R`IsogenyGroup, R`IsogenyProj, R`IsogenyInjToFund;
  else
    return R`IsogenyGroup, R`IsogenyProj, _;
  end if;
end intrinsic;



intrinsic CoisogenyGroup( R::RootDtm ) -> GrpAb, Map
{The coisogeny group of the root datum R}
  if not assigned R`CoisogenyGroup then
    Y := StandardLattice( Dimension( R ) );
    RPhis := Lattice( R`SimpleCoroots );
    G, g := Y / RPhis;
    R`CoisogenyGroup := G;
    R`CoisogenyProj := g;
    if IsSemisimple( R ) then
      F, f := FundamentalGroup( R );
      R`CoisogenyProjFromFund := hom< F -> G | 
        la :-> g( Y!Coordinates( la@@f ) ) >;
    end if;
  end if;
  if IsSemisimple( R ) then 
    return R`CoisogenyGroup, R`CoisogenyProj, R`CoisogenyProjFromFund;
  else
    return R`CoisogenyGroup, R`CoisogenyProj, _;
  end if;
end intrinsic;

intrinsic BasicDegrees( R::RootDtm ) -> [],[]
{The degrees of the basic polynomial invariants of R}
  return typeToBasicDegrees( toType( R ) : orbits := OrbitsOnSimples(R) );
end intrinsic;

intrinsic BasicDegrees( R::RootSys ) -> [],[]
{The degrees of the basic polynomial invariants of R}
  return typeToBasicDegrees( toType( R ) );
end intrinsic;



// ----------------------------------------------------
//
// Group orders
//

intrinsic CoxeterGroupOrder( R::RootStr ) -> RngIntElt
{The order of the Coxeter group of R}
  return CoxeterGroupOrder( CoxeterGraph( R ) );
end intrinsic;


intrinsic GroupOfLieTypeOrder( R::RootDtm, q::RngElt ) -> RngElt
{The order of the group of Lie type of R over the field with q elements}
  require IsReduced(R) : "Root datum is not reduced";
  require Ngens( GammaAction(R)`gamma ) le 1 : "The Gamma group must be cyclic";
  d := Dimension( R );  n := Rank( R );  N := NumPosRoots( R );
  deg, eps := BasicDegrees( R );  F := Universe(eps);
  int := Category(q) eq RngIntElt and Category(F) eq FldRat;
  if int then
    Q := q;  ChangeUniverse( ~eps, Integers() );
  else  
    F := PolynomialRing(F); Q := F.1;
  end if;
  mats := GammaAction(Radical(R))`mats_rt;
  if IsNull(mats) then
    F0 := One(MatrixAlgebra(Integers(),d));
  else
    F0 := (#mats eq 1) select mats[1] else Universe(mats)!1;
  end if;
  XQ := RootSpace( Radical(R) );
  if XQ ne Generic(XQ) then  // root subdatum
    d := Dimension(XQ);
    coords := [ Coordinates(XQ,u*F0) : u in Basis(XQ)];
//    ChangeUniverse(~coords,PowerSequence(BaseRing(XQ))); // in case coords is null
    F0 := Matrix( BaseRing(XQ), d,d, coords );
  end if ;
  F0 := ChangeRing( F0, Parent(Q) );
  order := Determinant(Q-F0)*Q^N * &*[F| (Q^deg[i] - eps[i]) : i in [1..#deg]];
  if not int then
    order := Evaluate( PolynomialRing(Integers())!order, q );
  end if;
  return (Type(order) eq FldRatElt) select Floor(order) else order;
end intrinsic;

fact_seq_power := func<S, n | [ <t[1], n*t[2]> : t in S ]>;

function fact_seq_canonicalise(S)
    // Given a sequence of tuples representing a factorisation, collate them
    // together and return the appropriate new factorisation sequence
    if #S le 1 then return S; end if;
    M := {* t[1]^^t[2] : t in S *};
    sorted_roots := Sort([ x : x in UnderlyingSet(M) ]);
    fseq := [ <x, Multiplicity(M, x)> : x in sorted_roots ];
    if Universe(fseq)[1] cmpeq Integers() then
	fseq := SequenceToFactorization(fseq);
    end if;
    return fseq;
end function;

intrinsic GroupOfLieTypeFactoredOrder( R::RootDtm, q::RngElt ) -> RngIntEltFact
{The factored order of the group of Lie type of R over the field with q elements}
  require IsReduced(R) : "Root datum is not reduced";
  require Ngens( GammaAction(R)`gamma ) le 1 : "The Gamma group must be cyclic";
  deg, eps := BasicDegrees( R );  F := Universe(eps);
  if Category(F) ne FldRat then
    // this only happens for 3D4 and absolutely reducible types
    return Factorisation( GroupOfLieTypeOrder( R, q ) );
  else
    ChangeUniverse( ~eps, Integers() );
  end if;
  d    := Dimension( R );  n := Rank( R );  N := NumPosRoots( R );
  fq   := Factorisation(  q  );
  fqm1 := Factorisation( q-1 );  // should call TwistedTorusOrder(R,1)
  fpow := [Factorisation( q^deg[i] - eps[i] ) : i in [1..#deg] ];
  // ret  := fqm1^(d-n) * fq^N * fpow;
  fq := fact_seq_power(fq, N);
  fqm1 := fact_seq_power(fqm1, d - n);
  ret := fact_seq_canonicalise(&cat ([fq, fqm1] cat fpow));
  return ret;
end intrinsic;

// ----------------------------------------------------
//
// Exceptional type (co)roots
//
// The positive (co)roots, organised by height.
//
E8roots :=
[
    [
        [ 1, 0, 0, 0, 0, 0, 0, 0 ],
        [ 0, 1, 0, 0, 0, 0, 0, 0 ],
        [ 0, 0, 1, 0, 0, 0, 0, 0 ],
        [ 0, 0, 0, 1, 0, 0, 0, 0 ],
        [ 0, 0, 0, 0, 1, 0, 0, 0 ],
        [ 0, 0, 0, 0, 0, 1, 0, 0 ],
        [ 0, 0, 0, 0, 0, 0, 1, 0 ],
        [ 0, 0, 0, 0, 0, 0, 0, 1 ]
    ],
    [
        [ 1, 0, 1, 0, 0, 0, 0, 0 ],
        [ 0, 1, 0, 1, 0, 0, 0, 0 ],
        [ 0, 0, 1, 1, 0, 0, 0, 0 ],
        [ 0, 0, 0, 1, 1, 0, 0, 0 ],
        [ 0, 0, 0, 0, 1, 1, 0, 0 ],
        [ 0, 0, 0, 0, 0, 1, 1, 0 ],
        [ 0, 0, 0, 0, 0, 0, 1, 1 ]
    ],
    [
        [ 1, 0, 1, 1, 0, 0, 0, 0 ],
        [ 0, 1, 1, 1, 0, 0, 0, 0 ],
        [ 0, 1, 0, 1, 1, 0, 0, 0 ],
        [ 0, 0, 1, 1, 1, 0, 0, 0 ],
        [ 0, 0, 0, 1, 1, 1, 0, 0 ],
        [ 0, 0, 0, 0, 1, 1, 1, 0 ],
        [ 0, 0, 0, 0, 0, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 1, 1, 0, 0, 0, 0 ],
        [ 1, 0, 1, 1, 1, 0, 0, 0 ],
        [ 0, 1, 1, 1, 1, 0, 0, 0 ],
        [ 0, 1, 0, 1, 1, 1, 0, 0 ],
        [ 0, 0, 1, 1, 1, 1, 0, 0 ],
        [ 0, 0, 0, 1, 1, 1, 1, 0 ],
        [ 0, 0, 0, 0, 1, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 1, 1, 1, 0, 0, 0 ],
        [ 1, 0, 1, 1, 1, 1, 0, 0 ],
        [ 0, 1, 1, 2, 1, 0, 0, 0 ],
        [ 0, 1, 1, 1, 1, 1, 0, 0 ],
        [ 0, 1, 0, 1, 1, 1, 1, 0 ],
        [ 0, 0, 1, 1, 1, 1, 1, 0 ],
        [ 0, 0, 0, 1, 1, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 1, 2, 1, 0, 0, 0 ],
        [ 1, 1, 1, 1, 1, 1, 0, 0 ],
        [ 1, 0, 1, 1, 1, 1, 1, 0 ],
        [ 0, 1, 1, 2, 1, 1, 0, 0 ],
        [ 0, 1, 1, 1, 1, 1, 1, 0 ],
        [ 0, 1, 0, 1, 1, 1, 1, 1 ],
        [ 0, 0, 1, 1, 1, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 2, 2, 1, 0, 0, 0 ],
        [ 1, 1, 1, 2, 1, 1, 0, 0 ],
        [ 1, 1, 1, 1, 1, 1, 1, 0 ],
        [ 1, 0, 1, 1, 1, 1, 1, 1 ],
        [ 0, 1, 1, 2, 2, 1, 0, 0 ],
        [ 0, 1, 1, 2, 1, 1, 1, 0 ],
        [ 0, 1, 1, 1, 1, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 2, 2, 1, 1, 0, 0 ],
        [ 1, 1, 1, 2, 2, 1, 0, 0 ],
        [ 1, 1, 1, 2, 1, 1, 1, 0 ],
        [ 1, 1, 1, 1, 1, 1, 1, 1 ],
        [ 0, 1, 1, 2, 2, 1, 1, 0 ],
        [ 0, 1, 1, 2, 1, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 2, 2, 2, 1, 0, 0 ],
        [ 1, 1, 2, 2, 1, 1, 1, 0 ],
        [ 1, 1, 1, 2, 2, 1, 1, 0 ],
        [ 1, 1, 1, 2, 1, 1, 1, 1 ],
        [ 0, 1, 1, 2, 2, 2, 1, 0 ],
        [ 0, 1, 1, 2, 2, 1, 1, 1 ]
    ],
    [
        [ 1, 1, 2, 3, 2, 1, 0, 0 ],
        [ 1, 1, 2, 2, 2, 1, 1, 0 ],
        [ 1, 1, 2, 2, 1, 1, 1, 1 ],
        [ 1, 1, 1, 2, 2, 2, 1, 0 ],
        [ 1, 1, 1, 2, 2, 1, 1, 1 ],
        [ 0, 1, 1, 2, 2, 2, 1, 1 ]
    ],
    [
        [ 1, 2, 2, 3, 2, 1, 0, 0 ],
        [ 1, 1, 2, 3, 2, 1, 1, 0 ],
        [ 1, 1, 2, 2, 2, 2, 1, 0 ],
        [ 1, 1, 2, 2, 2, 1, 1, 1 ],
        [ 1, 1, 1, 2, 2, 2, 1, 1 ],
        [ 0, 1, 1, 2, 2, 2, 2, 1 ]
    ],
    [
        [ 1, 2, 2, 3, 2, 1, 1, 0 ],
        [ 1, 1, 2, 3, 2, 2, 1, 0 ],
        [ 1, 1, 2, 3, 2, 1, 1, 1 ],
        [ 1, 1, 2, 2, 2, 2, 1, 1 ],
        [ 1, 1, 1, 2, 2, 2, 2, 1 ]
    ],
    [
        [ 1, 2, 2, 3, 2, 2, 1, 0 ],
        [ 1, 2, 2, 3, 2, 1, 1, 1 ],
        [ 1, 1, 2, 3, 3, 2, 1, 0 ],
        [ 1, 1, 2, 3, 2, 2, 1, 1 ],
        [ 1, 1, 2, 2, 2, 2, 2, 1 ]
    ],
    [
        [ 1, 2, 2, 3, 3, 2, 1, 0 ],
        [ 1, 2, 2, 3, 2, 2, 1, 1 ],
        [ 1, 1, 2, 3, 3, 2, 1, 1 ],
        [ 1, 1, 2, 3, 2, 2, 2, 1 ]
    ],
    [
        [ 1, 2, 2, 4, 3, 2, 1, 0 ],
        [ 1, 2, 2, 3, 3, 2, 1, 1 ],
        [ 1, 2, 2, 3, 2, 2, 2, 1 ],
        [ 1, 1, 2, 3, 3, 2, 2, 1 ]
    ],
    [
        [ 1, 2, 3, 4, 3, 2, 1, 0 ],
        [ 1, 2, 2, 4, 3, 2, 1, 1 ],
        [ 1, 2, 2, 3, 3, 2, 2, 1 ],
        [ 1, 1, 2, 3, 3, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 4, 3, 2, 1, 0 ],
        [ 1, 2, 3, 4, 3, 2, 1, 1 ],
        [ 1, 2, 2, 4, 3, 2, 2, 1 ],
        [ 1, 2, 2, 3, 3, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 4, 3, 2, 1, 1 ],
        [ 1, 2, 3, 4, 3, 2, 2, 1 ],
        [ 1, 2, 2, 4, 3, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 4, 3, 2, 2, 1 ],
        [ 1, 2, 3, 4, 3, 3, 2, 1 ],
        [ 1, 2, 2, 4, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 4, 3, 3, 2, 1 ],
        [ 1, 2, 3, 4, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 4, 4, 3, 2, 1 ],
        [ 1, 2, 3, 5, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 2, 3, 5, 4, 3, 2, 1 ],
        [ 1, 3, 3, 5, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 3, 3, 5, 4, 3, 2, 1 ],
        [ 2, 2, 4, 5, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 3, 4, 5, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 3, 4, 6, 4, 3, 2, 1 ]
    ],
    [
        [ 2, 3, 4, 6, 5, 3, 2, 1 ]
    ],
    [
        [ 2, 3, 4, 6, 5, 4, 2, 1 ]
    ],
    [
        [ 2, 3, 4, 6, 5, 4, 3, 1 ]
    ],
    [
        [ 2, 3, 4, 6, 5, 4, 3, 2 ]
    ]
];

F4roots :=
[
    [   [ 1, 0, 0, 0 ],  [ 0, 1, 0, 0 ],  [ 0, 0, 1, 0 ],  [ 0, 0, 0, 1 ]   ],
    [   [ 1, 1, 0, 0 ],  [ 0, 1, 1, 0 ],  [ 0, 0, 1, 1 ]   ],
    [   [ 1, 1, 1, 0 ],  [ 0, 1, 2, 0 ],  [ 0, 1, 1, 1 ]   ],
    [   [ 1, 1, 2, 0 ],  [ 1, 1, 1, 1 ],  [ 0, 1, 2, 1 ]   ],
    [   [ 1, 2, 2, 0 ],  [ 1, 1, 2, 1 ],  [ 0, 1, 2, 2 ]   ],
    [   [ 1, 2, 2, 1 ],  [ 1, 1, 2, 2 ]   ],
    [   [ 1, 2, 3, 1 ],  [ 1, 2, 2, 2 ]   ],
    [   [ 1, 2, 3, 2 ]   ],
    [   [ 1, 2, 4, 2 ]   ],
    [   [ 1, 3, 4, 2 ]   ],
    [   [ 2, 3, 4, 2 ]   ]
];
F4coroots :=
[
    [   [ 1, 0, 0, 0 ],  [ 0, 1, 0, 0 ],  [ 0, 0, 1, 0 ],  [ 0, 0, 0, 1 ]   ],
    [   [ 1, 1, 0, 0 ],  [ 0, 2, 1, 0 ],  [ 0, 0, 1, 1 ]   ],
    [   [ 2, 2, 1, 0 ],  [ 0, 1, 1, 0 ],  [ 0, 2, 1, 1 ]   ],
    [   [ 1, 1, 1, 0 ],  [ 2, 2, 1, 1 ],  [ 0, 2, 2, 1 ]   ],
    [   [ 1, 2, 1, 0 ],  [ 2, 2, 2, 1 ],  [ 0, 1, 1, 1 ]   ],
    [   [ 2, 4, 2, 1 ],  [ 1, 1, 1, 1 ]   ],
    [   [ 2, 4, 3, 1 ],  [ 1, 2, 1, 1 ]   ],
    [   [ 2, 4, 3, 2 ]   ],
    [   [ 1, 2, 2, 1 ]   ],
    [   [ 1, 3, 2, 1 ]   ],
    [   [ 2, 3, 2, 1 ]   ]
];

G2roots   := [ [[1,0], [0,1]], [[1,1]], [[2,1]], [[3,1]], [[3,2]] ];
G2coroots := [ [[1,0], [0,1]], [[1,3]], [[2,3]], [[1,1]], [[1,2]] ];


// ----------------------------------------------------
//
// Roots
//
// Note on basis changes:  We always compute wrt the simple root basis.
// To change to the standard basis, multiply by R`SimpleRoots
// To change to the weight basis, multiply by CartanMatrix( R )
//

// The following helper function is used by  Roots,
// SimpleReflectionMatrices and SimpleCoreflectionMatrices.
simpleReflection := function( transpC, id, i )
  id[i] := id[i] - transpC[i];
  return Transpose(id);
end function;

space := function( R, Basis, Coroots )
  if Coroots then
    case Basis:
    when "Standard": return R`CorootSpace;
    when "Root":     return R`Urts;
    when "Weight":   return R`Uwgt;
    end case;
  else
    case Basis:
    when "Standard": return R`RootSpace;
    when "Root":     return R`Vrts;
    when "Weight":   return R`Vwgt;
    end case;
  end if;
end function;

basisChange := function(R,v,InBasis,OutBasis,Coroots)
      if not (Category(InBasis)  eq MonStgElt and InBasis  in {"Standard","Root","Weight"}) then
        return "Invalid InBasis flag";
    elif not (Category(OutBasis) eq MonStgElt and OutBasis in {"Standard","Root","Weight"}) then
        return "Invalid OutBasis flag";
    elif not (Category(Coroots) eq BoolElt) then 
        return "Optional flag Coroots must be a boolean value";
    end if;

    mesg := "Argument 2 is not a " *
            (Coroots select "coroot" else "root") *
            " vector w.r.t. " * InBasis * " basis";

    if not Coroots then
        case InBasis:
        when "Standard":
            if not IsCoercible(R`Vstd,v) then return mesg; end if;
            v := R`Vstd!v;
            case OutBasis:
            when "Standard":    return RootSpace(R)!v;
            when "Root":        return Vector(R`std2rtsV(v));
            when "Weight":      return Vector(R`std2wgtV(v));
            end case;
        when "Root":
            if not IsCoercible(R`Vrts,v) then return mesg; end if;
            v := R`Vrts!v;
            case OutBasis:
            when "Standard":    return RootSpace(R)!(R`rts2stdV(v));
            when "Root":        return Vector(v);
            when "Weight":      return Vector(R`rts2wgtV(v));
            end case;
        when "Weight":
            if not IsCoercible(R`Vwgt,v) then return mesg; end if;
            v := R`Vwgt!v;
            case OutBasis:
            when "Standard":    return RootSpace(R)!(R`wgt2stdV(v));
            when "Root":        return Vector(R`wgt2rtsV(v));
            when "Weight":      return Vector(v);
            end case;
        end case;
    else
        case InBasis:
        when "Standard":
            if not IsCoercible(R`Ustd,v) then return mesg; end if;
            v := R`Ustd!v;
            case OutBasis:
            when "Standard":    return CorootSpace(R)!v;
            when "Root":        return Vector(R`std2rtsU(v));
            when "Weight":      return Vector(R`std2wgtU(v));
            end case;
        when "Root":
            if not IsCoercible(R`Urts,v) then return mesg; end if;
            v := R`Urts!v;
            case OutBasis:
            when "Standard":    return CorootSpace(R)!(R`rts2stdU(v));
            when "Root":        return Vector(v);
            when "Weight":      return Vector(R`rts2wgtU(v));
            end case;
        when "Weight":
            if not IsCoercible(R`Uwgt,v) then return mesg; end if;
            v := R`Uwgt!v;
            case OutBasis:
            when "Standard":    return CorootSpace(R)!(R`wgt2stdU(v));
            when "Root":        return Vector(R`wgt2rtsU(v));
            when "Weight":      return Vector(v);
            end case;
        end case;
    end if;
end function;

intrinsic BasisChange( R::RootStr, v::. : InBasis := "Standard", OutBasis := "Standard", Coroots := false ) -> SeqEnum
{Changes the Basis of the vector v contained in the space spanned by the roots of R}
    ret := basisChange(R,v,InBasis,OutBasis,Coroots);
    require not Category(ret) eq MonStgElt : ret;
    return ret;
end intrinsic;

intrinsic IsInRootSpace( R::RootDtm, v::ModTupFldElt ) -> BoolElt
{True iff v is in root space of R}
    return assigned Parent(v)`RootDatum      
           and      Parent(v)`RootDatum eq R
           and      Parent(v)`Roots;
end intrinsic;

intrinsic IsInCorootSpace( R::RootDtm, v::ModTupFldElt ) -> BoolElt
{True iff v is in coroot space of R}
    return assigned Parent(v)`RootDatum      
           and      Parent(v)`RootDatum eq R
           and      Parent(v)`Coroots;
end intrinsic;

rootsCorootsWRTSimple := function( t, n, B )
  setseq := func< s | [ s[i] : i in [1..#s] ] >;
  lincomb := func< v | &+[ v[i]*B[i] : i in [1..#B] ] >;
  roots := [ [ B[i] : i in [1..#B] ] ];
  case t:
  when "A":
    for h in [2..n] do
      Append( ~roots, [ B[i] + roots[h-1][i+1] : i in [1..n-h+1] ] );
    end for;
    coroots := roots;
  when "B","BC":
    coroots := roots;
    for h in [2..2*n-1] do
      lvl := roots[h-1];
      if (h mod 2) eq 0 then  Prune( ~lvl );  end if;
      for i in [1..#lvl] do
        idx := i+h-1;  idx := Integers()!(n+1/2 - Abs(n+1/2-idx));
        lvl[i] +:= B[idx];
      end for;
      Include( ~roots, lvl );
      pos := n-h+1;
      if pos gt 0 then
        lvl[pos] := coroots[h-1][n-h+2] + 2*B[pos];
      end if;
      for i in [Max(1,pos+1)..#lvl] do
        lvl[i] -:= B[n];
      end for;
      Include( ~coroots, lvl );
    end for;
    if t eq "BC" then
      Append(  ~roots,[]);
      Append(~coroots,[]);
      for i in [1..n] do 
        Append(  ~roots[2*i],   2*  roots[i][n-i+1]);
        Append(~coroots[2*i], 1/2*coroots[i][n-i+1]);
      end for;
    end if;
  when "C":
    coroots := roots;
    for h in [2..2*n-1] do
      lvl := roots[h-1];
      if (h mod 2) eq 0 then  Prune( ~lvl );  end if;
      for i in [1..#lvl] do
        idx := i+h-1;  idx := Integers()!(n - Abs(n-idx));
        lvl[i] +:= B[idx];
      end for;
      Append( ~roots, lvl );
      for i in [Max(1,n-h+1)..#lvl] do
        lvl[i] +:= B[n];
      end for;
      if h mod 2 eq 1 then
        lvl[#lvl] := roots[(h+1) div 2][n-((h+1) div 2)+1];
      end if;
      Include( ~coroots, lvl );
    end for;
  when "D":
    for h in [2..2*n-3] do
      lvl := [];
      if h le 2*n-4 then
        lvl cat:= roots[h-1];  Remove( ~lvl, 1 );
        if h eq n then  Remove( ~lvl, 1 );  end if;
        for i in [1..#lvl] do
          idx := i;
          if (idx gt n-h and h lt n) then  idx -:= 1;  end if;
          lvl[i] +:= B[idx];
        end for;
      end if;
      if h eq 3 then
        Append( ~lvl, roots[2][n-2] + B[n] );
      end if;
      if h ge 5 and h mod 2 eq 1 then
        last := roots[h-1];
        Append( ~lvl, last[#last] + B[n-1-((h-3) div 2)] );
      end if;
      Append( ~roots, lvl );
    end for;
    coroots := roots;
  when "E":
    m := case< n | 6:11, 7:17, default:29 >;
    for h in [2..m] do
      Append( ~roots, [ lincomb(v) : v in E8roots[h] |
                        forall{ i : i in [n+1..8] | v[i] eq 0 } ] );
    end for;
    coroots := roots;
  when "F":
    coroots := roots;
    for h in [2..11] do
      Append( ~roots,   [ lincomb(v) : v in F4roots[h]   ] );
      Append( ~coroots, [ lincomb(v) : v in F4coroots[h] ] );
    end for;
  when "G":
    coroots := roots;
    for h in [2..5] do
      Append( ~roots,   [ lincomb(v) : v in G2roots[h]   ] );
      Append( ~coroots, [ lincomb(v) : v in G2coroots[h] ] );
    end for;
  else
    error "This should not happen";
  end case;
  return roots, coroots;
end function;

computeRootsCoroots := procedure( ~R )
  if not (assigned R`RootSystem and assigned R`CorootSystem) then
    C := CartanMatrix( R );
    if Nrows(C) eq 0 then
      R`NumPosRoots := 0;
      R`RootSystem := {@ R`Vrts | @};
      R`CorootSystem := {@ R`Urts | @};
      return;
    end if;
    K := ISA(Category(R),RootDtm) select BaseRing(R) else BaseField(R);
    B := Basis( ChangeRing(Parent( C[1] ),K) );
    type := toType( R );
    isCryst := IsCrystallographic( C );

    // function for computing roots of noncrystallographic components
    noncrystalCompRoots := function( C, comp, N )
      n := #comp;
      // compute the reflection matrices
      transpC := Transpose(C);  id := Identity(Parent(C));
      refs := [ simpleReflection(transpC, id, i) : i in comp ];

      compRoots := [ [ B[i] : i in comp ] ];
      layer := compRoots[1];  done := { v : v in layer } join { -v : v in layer };
      height := 1;
      while not IsEmpty( layer ) do
        compRoots[height] := layer;  
        layer := [];
        for beta in compRoots[height] do
          for i in [1..n] do
            if not (height eq 1 and beta eq B[comp[i]]) then // never create -ve root
              gamma := beta*refs[i];
              if gamma notin done then
                Append( ~layer, gamma );  Include( ~done, gamma ); Include( ~done, -gamma );
                if &+[ #l : l in compRoots ] + #layer eq N then
                  compRoots[height+1] := layer;
                  return compRoots;
                end if;
              end if;
            end if;
          end for;
        end for;
        height +:= 1;
      end while;
      return compRoots;
    end function;

/*    // function for computing roots of noncrystallographic components
    noncrystalCompRoots := function( C, comp, N )
      n := #comp;
      // compute the reflection matrices
      transpC := Transpose(C);  id := Identity(Parent(C));
      refs := [ simpleReflection(transpC, id, i) : i in comp ];

      compRoots := [ [ B[i] : i in comp ] ];
      layer := compRoots[1];  done := { v : v in layer } join { -v : v in layer };
      height := 1;
      while not IsEmpty( layer ) do
        compRoots[height] := layer;  
        done := done join { v : v in layer } join { -v : v in layer };
        layer := [];
        for beta in compRoots[height] do
          for i in [1..n] do
            if not (height eq 1 and beta eq B[comp[i]]) then // never create -ve root
              gamma := beta*refs[i];
              if gamma notin layer and forall{ j : j in [1..height] | gamma notin compRoots[j] } then
                Append( ~layer, gamma );
                if &+[ #l : l in compRoots ] + #layer eq N then
                  compRoots[height+1] := layer;
                  return compRoots;
                end if;
              end if;
            end if;
          end for;
        end for;
        height +:= 1;
      end while;
      return compRoots;
    end function;*/

    // The main loop
    roots := [ [ b : b in B ] ];  coroots := roots;
    for t in type do
      comp := t[2];

      if isCryst or forall{ <i,j> : i,j in comp | C[i,j] in Integers() } then
        if not isCrystType( [* t *] ) then
          subC := Matrix( #comp,#comp,[ C[i,j] : i,j in comp ] );
          t2 := cartanToType( subC )[1];  X := t2[1]; comp := t2[2];
        else
          X := t[1];  
        end if;
        compRoots, compCoroots := rootsCorootsWRTSimple( X, #comp, B[comp] );
      else
        N := numPosRootsOfType( [* t *] );
        compRoots := noncrystalCompRoots( C, comp, N );
        compCoroots := noncrystalCompRoots( Transpose(C), comp, N );
      end if;

      // add comp(Co)roots to (co)roots
      for h := 2 to #compRoots do
        if not IsDefined( roots, h ) then
          roots[h] := [];  coroots[h] := [];
        end if;
        roots[h] cat:= compRoots[h];
        coroots[h] cat:= compCoroots[h];
      end for;

    end for;

    // put the layers together in an indexed set
    roots   := {@ R`Vrts | v : v in &cat(  roots) @};
    coroots := {@ R`Urts | v : v in &cat(coroots) @};

    R`NumPosRoots := #roots;
    
    // add the negative (co)roots
    R`RootSystem := roots join {@ -v : v in roots @};
    R`CorootSystem := coroots join {@ -v : v in coroots @};
  end if;
end procedure;


intrinsic Roots( R::RootStr : Basis := "Standard" ) -> SetIndx
{The roots of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  computeRootsCoroots( ~R );
  if Basis eq "Root" then
    return R`RootSystem;
  else
    if not assigned R``("RootSystem" * Basis) then
      R``("RootSystem" * Basis) := {@ space( R, Basis, false ) |
      BasisChange( R, v : InBasis := "Root", OutBasis := Basis ) : v in R`RootSystem @};
    end if;
    return R``("RootSystem" * Basis);
  end if;
end intrinsic;


intrinsic NumPosRoots( R::RootStr ) -> RngIntElt
{The number of positive (co)roots of R}
  if not assigned R`NumPosRoots then
    R`NumPosRoots := numPosRootsOfType( toType(R) );
  end if;
  return R`NumPosRoots;
end intrinsic;

intrinsic NumberOfPositiveRoots( R::RootStr ) -> RngIntElt
{The number of positive (co)roots of R}
  return NumPosRoots( R );
end intrinsic;


intrinsic PositiveRoots( R::RootStr : Basis := "Standard" ) -> SetIndx
{The positive roots of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  N := NumPosRoots( R );
  // since the roots are stored now, we call
  // Roots and take the appropriate subset
  return Roots( R : Basis:=Basis )[1..N];
end intrinsic;



intrinsic Root( R::RootStr, r::RngIntElt : Basis := "Standard" ) -> .
{The rth root of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  requirerange r, 1, 2*NumPosRoots(R);
  if assigned R`RootSystem or r gt Rank(R) then
    roots := Roots( R : Basis:=Basis );
    return roots[r];
  else // r le Rank(R) and roots not yet computed. 
    roots := basis_intrinsic( Parent( CartanMatrix(R)[1] ) );
    return BasisChange( R, roots[r] : InBasis := "Root", OutBasis := Basis );
  end if;
end intrinsic;


intrinsic RootPosition( R::RootStr, v : Basis := "Standard" ) -> RngIntElt
{The position of the vector v as a root of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  roots := Roots( R : Basis := Basis );
  return Position( roots, v );
end intrinsic;



neg := func< r, N | (r le N) select r+N else r-N >;

intrinsic IsPositive( R::RootStr, r::RngIntElt ) -> BoolElt
{True iff the rth root of R is positive}
  return r in [1 .. NumPosRoots( R )];
end intrinsic;

intrinsic IsNegative( R::RootStr, r::RngIntElt ) -> BoolElt
{True iff the rth root of R is negative}
  return r in [N+1 .. 2*N] where N is NumPosRoots( R ) ;
end intrinsic;

intrinsic Negative( R::RootStr, r::RngIntElt ) -> BoolElt
{The index of the negative of the rth root of R}
  return neg(r,NumPosRoots( R ));
end intrinsic;





// ----------------------------------------------------
//
// Coroots
//
// Note on basis changes:  We always compute wrt the simple coroot basis.
// To change to the standard basis, multiply by R`SimpleCoroots
// To change to the coweight basis, multiply by Transpose( CartanMatrix( R ) )
//
// cobasisChange() moved into BasisChange()


intrinsic Coroots( R::RootStr : Basis := "Standard" ) -> SetIndx
{The coroots of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  computeRootsCoroots( ~R );
  if Basis eq "Root" then
    return R`CorootSystem;
  else
    if not assigned R``("CorootSystem" * Basis) then
    R``("CorootSystem" * Basis) := {@ space( R, Basis, true ) |
      BasisChange( R, v : InBasis := "Root", OutBasis := Basis, Coroots ) : 
      v in R`CorootSystem @};
    end if;
    return R``("CorootSystem" * Basis);
  end if;
end intrinsic;


intrinsic PositiveCoroots( R::RootStr : Basis := "Standard" ) -> SetIndx
{The positive coroots of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  N := NumPosRoots( R );
  return Coroots(R : Basis:=Basis )[1..N];
end intrinsic;


intrinsic Coroot( R::RootStr, r::RngIntElt : Basis := "Standard" ) -> .
{The rth coroot of R}
  require Basis in {"Standard","Root","Weight"}: "Invalid Basis flag";
  require ISA(Category(R),RootDtm) or Basis ne "Weight" : "Weight basis only defined for root data";
  requirerange r, 1, 2*NumPosRoots( R );
  if assigned R`RootSystem or r gt Rank(R) then
    roots := Coroots( R : Basis:=Basis );
    return roots[r];
  else // r le Rank(R) and roots not yet computed. 
    roots := basis_intrinsic( Parent( CartanMatrix(R)[1] ) );
    return BasisChange( R, roots[r] : InBasis := "Root", OutBasis := Basis, Coroots := true );
  end if;
end intrinsic;


intrinsic CorootPosition( R::RootStr, v : Basis := "Standard" ) -> RngIntElt
{The position of v as a coroot of R}
  roots := Coroots( R : Basis := Basis );
  return Position( roots, v );
end intrinsic;



// ----------------------------------------------------
//
// Heights of (co)roots
//

intrinsic RootHeight( R::RootStr, r::RngIntElt ) -> RngIntElt
{The height of the rth root of R}
  return &+Eltseq( Root( R, r : Basis := "Root" ) );
end intrinsic

intrinsic CorootHeight( R::RootStr, r::RngIntElt ) -> RngIntElt
{The height of the rth coroot of R}
  return &+Eltseq( Coroot( R, r : Basis := "Root" ) );
end intrinsic

intrinsic HighestRoot( R::RootStr : Basis:="Standard" ) -> .
{The unique root of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  return Root( R, NumPosRoots(R) : Basis:=Basis );
end intrinsic;

intrinsic HighestCoroot( R::RootStr : Basis:="Standard" ) -> .
{The unique coroot of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  return Coroot( R, NumPosRoots(R) : Basis:=Basis );
end intrinsic;


highestShortPos := function( R )
  len := RootNorms( R );  N := NumPosRoots( R );
  for r in [N..1 by -1] do
    if len[r] eq 1 then  return r;  end if;
  end for;
end function;  
highestLongPos := function( R )
  N := NumPosRoots( R );
  if IsReduced(R) then return N; end if;
  len := RootNorms( R );  
  for r in [N..1 by -1] do
    if len[r] in {2,3} then  return r;  end if;
  end for;
end function;  


intrinsic HighestLongRoot( R::RootStr : Basis:="Standard" ) -> .
{The unique long root of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  require IsCrystallographic( R ) : "For crystallographic root systems only";
  return Root( R, highestLongPos(R) : Basis:=Basis );
end intrinsic;
intrinsic HighestLongCoroot( R::RootStr : Basis:="Standard" ) -> .
{The unique long root of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  require IsCrystallographic( R ) : "For crystallographic root systems only";
  return Coroot( R, highestShortPos(R) : Basis:=Basis );
end intrinsic;


intrinsic HighestShortRoot( R::RootStr : Basis:="Standard" ) -> .
{The unique short root of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  require IsCrystallographic( R ) : "For crystallographic root systems only";
  return Root( R, highestShortPos(R) : Basis:=Basis );
end intrinsic;
intrinsic HighestShortCoroot( R::RootStr : Basis:="Standard" ) -> .
{The unique short root of greatest height of R}
  require IsIrreducible( R ) : "For irreducible root systems/data only";
  require IsCrystallographic( R ) : "For crystallographic root systems only";
  return Coroot( R, highestLongPos(R) : Basis:=Basis );
end intrinsic;


// ----------------------------------------------------
//
// Additive order
//


intrinsic AdditiveOrder( R::RootStr ) -> SeqEnum
{An additive order on the positive roots of R}
  require IsReduced(R) : "R must be reduced";
  return AdditiveOrder( CoxeterGroup( R ) );
end intrinsic;


// This is the brute force method -- is there a better way?
intrinsic IsAdditiveOrder( R::RootStr, order::[RngIntElt] ) -> BoolElt
{True iff order is an additive order on positive roots of R}
  require IsReduced(R) : "Only for reduced root systems/data";
  N := NumPosRoots( R );
  require Seqset(order) subset {1..N} and #order eq #Seqset(order) : 
    "The order must consist of the integers from 1 to ", N;
  for i in [1..N] do
    for j in [i+1..N] do
      sum := Sum( R, order[i], order[j] );
      if sum ne 0 then
        pos := Position( order, sum );
	if pos lt i or pos gt j then  return false;  end if;
      end if;
    end for;
  end for;
  return true;
end intrinsic;
	

// ----------------------------------------------------
//
// Weights
//
// Note on basis changes:  We always compute wrt the simple
// (co)weight basis.  To change to the (co)root basis,
// multiply by the fundamental weights, C^-1.  To change
// to the standard basis, go via the (co)root basis.
//

intrinsic FundamentalWeights( R::RootDtm : Basis := "Standard" ) -> AlgMatElt
{The fundamental weights of the root datum R as the rows of a matrix}
  C := CartanMatrix( R );  k := FieldOfFractions(BaseRing(C));
  C := ChangeRing( C, k );
  case Basis:
  when "Weight":
    return Parent(C)!1;
  when "Root":
    return C^(-1);
  when "Standard":
    return C^(-1) * ChangeRing( R`SimpleRoots, k );
  else
    error "Invalid Basis flag";
  end case;
end intrinsic;

intrinsic WeightLattice( R::RootDtm ) -> Lat
{The lattice of weights of the root datum R}
  return LatticeWithBasis( FundamentalWeights(R) );
end intrinsic;

intrinsic FundamentalCoweights( R::RootDtm : Basis := "Standard" ) -> SeqEnum
{The fundamental coweights of the root datum R as the rows of a matrix}
  C := Transpose( CartanMatrix( R ) );  k := FieldOfFractions(BaseRing(C));
  C := ChangeRing( C, k );
  case Basis:
  when "Weight":
    return Parent(C)!1;
  when "Root":
    return C^(-1);
  when "Standard":
    return C^(-1) * ChangeRing( R`SimpleCoroots, k );
  else
    error "Invalid Basis flag";
  end case;
end intrinsic;

intrinsic CoweightLattice( R::RootDtm ) -> Lat
{The lattice of coweights of the root datum R}
  return LatticeWithBasis( FundamentalCoweights(R) );
end intrinsic;

intrinsic DominantWeight( R::RootDtm, v : Basis := "Standard" ) -> 
  ModTupFldElt, GrpFPCoxElt
{The unique element in the W-orbit of the weight v which lies in the
fundamental Weyl chamber}
  C := ChangeRing( CartanMatrix(R), Rationals() );
  w := [];
  rank := Rank(R);
  
  case Basis:
  when "Weight":  lambda := RSpace( Rationals(), rank )!v;
  when "Root":    lambda := RSpace( Rationals(), rank )!v*C;
  when "Standard":
    V := WeightLattice(R);
    require IsCoercible( V, v ) : "v is not a weight";
    lambda := Coordinates( V, V!v );
    lambda := RSpace( Rationals(), rank )!lambda;
  else
    error "Invalid Basis flag";
  end case;
  
  while exists(i){ i : i in [1..rank] | lambda[i] lt 0 } do
    Append(~w,i);
    lambda -:= lambda[i]*C[i];
  end while;
  W := CoxeterGroup(R);
  return lambda * FundamentalWeights(R:Basis:=Basis), CoxeterGroup(GrpFPCox,W)!w;
end intrinsic;

intrinsic WeightOrbit( R::RootDtm, v : Basis := "Standard", J := [1..Rank(R)], dom := true ) -> {@ @}, SeqEnum
{The orbit of the weight v under the action of W}
  // Reductive datum:  This could be more efficient
  if not IsSemisimple(R) and Basis eq "Standard" then
    n := Rank( R );  d := Dimension(R);
//   RSPint := RSpace(Integers(),d);
    RSPrat := RSpace(Rationals(),d);
    v := RSPrat!v;
    B := [ SimpleRoots(R)[r] : r in [1..n] ] cat basis_intrinsic(RootSpace(Radical(R)));
    ChangeUniverse( ~B, RSPrat );
    V := VectorSpaceWithBasis(B);
    vim := Coordinates( V, V!v )[[1..n]];
    _, acts := $$( R, vim : Basis:="Root", J:=J, dom:=dom );
    refls := ReflectionMatrices(R);
    return {@ RSPrat | v*&*refls[Eltseq(wd)] : wd in acts @}, acts;
  end if; 

  v := BasisChange( R, v : InBasis:=Basis, OutBasis:="Weight" );

  C := ChangeRing( CartanMatrix(R), Rationals() );
  rank := Rank( R );
  V := RSpace( Rationals(), rank );
  if v eq V!0 then  return {@ v @}, [[Integers()|]];  end if;
  if dom then
    lambda, _ := DominantWeight( R, v : Basis:="Weight" );
  else
    lambda := v;
  end if;
  T := {@ V | @};  Action := [];
  current := {@ lambda @}; cAction := [ [] ];
  repeat
    previous := current;  pAction := cAction;
    T join:= current;     Action cat:= cAction;
    current := {@ V | @}; cAction := [];
    for nupos in [1..#previous] do
      nu := previous[nupos];
      for i in J do
        if nu[i] gt 0 then
          xi := nu - nu[i]*C[i];
          if forall{ j : j in [i+1..rank] | xi[j] ge 0 } then
            Include( ~current, xi );
            Append( ~cAction, pAction[nupos] cat [i] );
          end if;
        end if;
      end for;
    end for;
  until IsEmpty( current );
  return {@ BasisChange( R, t : InBasis:="Weight", OutBasis:=Basis ) : t in T @},
    ChangeUniverse( Action, CoxeterGroup(GrpFPCox,R) );
end intrinsic;

intrinsic IsDominant( R::RootDtm, v : Basis:="Standard" ) -> BoolElt
{Is v a dominant weight for R?}
  v :=  Eltseq( BasisChange( R, v : InBasis:=Basis,OutBasis:="Weight") );
  require forall{ a : a in v | IsCoercible(Integers(),a) } :
    "Not a weight";
  return forall{ a : a in Eltseq(v) | Integers()!a ge 0 };
end intrinsic;


// ----------------------------------------------------
//
// HASH
//

intrinsic HackobjHashRootDtm( R::RootDtm ) -> RngIntElt
{Return a hash value for a root datum}
    hashes := [
                Hash(R`Rank),           // take rank and dim into account
                Hash(R`Dimension),      // since empty matrices have same hashes 
                Hash(R`SimpleRoots),    // even if they have different sizes.
                Hash(R`SimpleCoroots) ];

    for t in R`Type do                  // Need Type here to distinguish between B and BC.
        Append( ~hashes, Hash(t) );     // NumPosRoots is not enough! counterexample is B2xBC2 vs. BC2xB2
    end for;                            //

    signs := R`ExtraspecialSigns;
    // make shure that the same hash is returned for signs 1 and [1,...,1]
    if Category(signs) eq SeqEnum and #Seqset(signs) eq 1 then
        Append(~hashes, Hash(Rep(signs)));
    else
        Append(~hashes, Hash(signs));
    end if;

    hashes cat:= [ Hash( R`GammaAction`gamma   ), 
                   Hash( R`GammaAction`mats_rt ),
                   Hash( R`GammaAction`mats_co ) ];

    return Hash(hashes);
end intrinsic;

intrinsic HackobjHashRootSys( R::RootSys ) -> RngIntElt
{Return a hash value for a root system}
    hashes := [
    
                Hash(R`Rank),           // take rank and dim into account
                Hash(R`Dimension),      // since empty matrices have same hashes 
                Hash(R`SimpleRoots),    // even if they have different sizes.
                Hash(R`SimpleCoroots) ];

    for t in R`Type do                  // Need Type here to distinguish between B and BC.
        Append( ~hashes, Hash(t) );     // NumPosRoots is not enough! counterexample is B2xBC2 vs. BC2xB2
    end for;                            //

    return Hash(hashes);
end intrinsic;


// ----------------------------------------------------
//
// Equality and isogeny
//

intrinsic 'eq'( R1::RootDtm, R2::RootDtm ) -> BoolElt
{True iff R1 and R2 are identical}
    check := Rank( R1 )         eq Rank( R2 )
         and Dimension( R1 )    eq Dimension( R2 )
         and R1`SimpleRoots     eq R2`SimpleRoots   
         and R1`SimpleCoroots   eq R2`SimpleCoroots;

    if not check then return false; end if;
    
    // Need Type here to distinguish between B and BC.
    // NumPosRoots is not enough! counterexample is B2xBC2 vs. BC2xB2
    type1 := toType(R1); type2 := toType(R2);
    check := #type1 eq #type2 and forall{i:i in [1..#type1]|type1[i] eq type2[i]};
    
    if not check then return false; end if;
    
    // signs must be either an integer or a sequence of integers
    if Category(R1`ExtraspecialSigns) eq Category(R2`ExtraspecialSigns) then
        check := R1`ExtraspecialSigns eq R2`ExtraspecialSigns;
    elif Category(R1`ExtraspecialSigns) eq RngIntElt /* and SeqElt[RngIntElt] for R2 */ then
        check := {R1`ExtraspecialSigns} eq Seqset(R2`ExtraspecialSigns);
    else /* SeqElt[RngIntElt] for R1 and RngIntElt for R2 */
        check := Seqset(R1`ExtraspecialSigns) eq {R2`ExtraspecialSigns};
    end if;

    if not check then return false; end if;

    check := R1`GammaAction`mats_rt cmpeq R2`GammaAction`mats_rt
         and R1`GammaAction`mats_co cmpeq R2`GammaAction`mats_co ;

    return check;
end intrinsic;

intrinsic 'eq'( R1::RootSys, R2::RootSys ) -> BoolElt
{True iff R1 and R2 are identical}
    k1 := BaseField( R1 );  k2 := BaseField( R2 );
    check := k1 cmpeq k2 
        and Rank( R1 )       eq Rank( R2 ) 
        and Dimension( R1 )  eq Dimension( R2 ) 
        and R1`SimpleRoots   eq R2`SimpleRoots 
        and R1`SimpleCoroots eq R2`SimpleCoroots;
        
    if not check then return false; end if;
    
    // Need Type here to distinguish between B and BC.
    // NumPosRoots is not enough! counterexample is B2xBC2 vs. BC2xB2
    type1 := toType(R1); type2 := toType(R2);
    check := #type1 eq #type2 and forall{i:i in [1..#type1]|type1[i] eq type2[i]};
    
    return check;
end intrinsic;



// ----------------------------------------------------
//
// Predicates
//

intrinsic IsCartanEquivalent( R1::RootSys, R2::RootSys ) -> BoolElt
{True iff R1 and R2 are Cartan equivalent}
  require IsCrystallographic(R1) and IsCrystallographic(R2) 
    : "The root systems must be crystallographic";
  require IsReduced(R1) and IsReduced(R2)
    : "The root systems must be reduced";
  return IsCartanEquivalent( CartanMatrix(R1), CartanMatrix(R2) );
end intrinsic;
intrinsic IsCartanEquivalent( R1::RootDtm, R2::RootDtm ) -> BoolElt
{True iff R1 and R2 are Cartan equivalent}
  require IsReduced(R1) and IsReduced(R2) : "The root data must be reduced";
  return IsCartanEquivalent( CartanMatrix(R1), CartanMatrix(R2) );
end intrinsic;

intrinsic IsIsomorphic( R1::RootSys, R2::RootSys ) -> BoolElt
{True iff R1 and R2 are isomorphic}
  return Category( BaseRing(R1) ) eq Category( BaseRing(R2) ) and 
  Dimension( R1 ) eq Dimension( R2 ) and 
  IsCoxeterIsomorphic( CoxeterMatrix(R1), CoxeterMatrix(R2) );
end intrinsic;

intrinsic IsIsomorphic( R1::RootDtm, R2::RootDtm ) -> BoolElt
{True iff R1 and R2 are isomorphic}
  require IsSplit(R1) and IsSplit(R2): "Root data must be split";
  d1 := Dimension( R1 );          d2 := Dimension( R2 );
  n1 := Rank( R1 );               n2 := Rank( R2 );
  if d1 ne d2 or n1 ne n2 then
    return false, _, _;
  elif n1 eq 0 then
    I := IdentityMatrix( BaseRing(R1), d1 );
    return true, [], hom< R1->R2 | [I,I] >;
  end if;
  iso, ims := IsCartanEquivalent( R1, R2 );
  if not iso then
    return false, _, _;
  else
    // this should only be temporary
    require IsSemisimple(R1) : 
      "IsIsomorphic is currently only implemented for semisimple root data";

    G := typeAutos( toType(R2) );  S := Sym( Degree(G) );
    permrows := func< A, g | Matrix( [ A[ims[i]^g] : i in [1..n1] ] ) >;
    A1 := SimpleRoots( R1 );  B1 := SimpleCoroots( R1 );
    A1, B1 := normalisedRootDatumMxs( A1, B1 );
    A2 := SimpleRoots( R2 );  B2 := SimpleCoroots( R2 );
    for g in G do
      A3 := permrows(A2,g);  B3 := permrows(B2,g);
      A3, B3 := normalisedRootDatumMxs( A3, B3 );
      if A1 eq A3 and B1 eq B3 then
        inj := [ ims[i]^g : i in [1..n1] ];
        return true, inj, hom< R1->R2 | inj >;
      end if;
    end for;
    return false, _, _;
  end if;
end intrinsic;

// Is semisimplicity necessary?
intrinsic IsIsogenous( R1::RootDtm, R2::RootDtm ) -> BoolElt
{True if R1 and R2 are isogenous}
  require IsSplit(R1) and IsSplit(R2): "Root data must be split";
  ok, inj := IsCartanEquivalent( R1, R2 );
  if ok then
    require IsSemisimple(R1) and IsSemisimple(R2) :
      "Only implemented for semisimple root data";
    n := Rank( R1 );  N := NumPosRoots( R1 );
    C := typeToCartan( toType( R1 ) );
    ad := RootDatum( C );  sc := RootDatum( C : Isogeny:="SC" );
    adToR2 := hom<ad->R2|inj>;
    inj := adToR2`data`inj;
    invinj := Eltseq( ( Sym(2*N) ! inj )^-1 );
    return ok, inj, ad, hom<ad->R1|[1..n]>, adToR2, 
      sc, hom<R1->sc|[1..n]>, hom<R2->sc|invinj>;
  else
    return ok, _, _,_,_, _,_,_;
  end if;
end intrinsic;


intrinsic IsFinite( R::RootStr ) -> BoolElt
{True iff R is finite}
  return IsCoxeterFinite( CoxeterGraph( R ) );
end intrinsic;

intrinsic IsAffine( R::RootStr ) -> BoolElt
{True iff R is affine}
  return IsCoxeterAffine( CoxeterGraph( R ) );
end intrinsic;

intrinsic IsSemisimple( R::RootStr ) -> BoolElt
{True iff R is semisimple}
  if not assigned R`IsSemisimple then
    R`IsSemisimple := Rank( R ) eq Dimension( R );
  end if;
  return R`IsSemisimple;
end intrinsic;

intrinsic IsProjectivelyIrreducible( R::RootStr ) -> BoolElt
{True iff quotient of R modulo its radical is irreducible}
  return IsConnected( CoxeterGraph(R) );
end intrinsic;

intrinsic IsIrreducible( R::RootStr ) -> BoolElt
{True iff R is irreducible}
  if not assigned R`IsIrreducible then
    R`IsIrreducible := IsSemisimple( R ) and IsProjectivelyIrreducible( R );
  end if;
  return R`IsIrreducible;
end intrinsic;

intrinsic IsAbsolutelyIrreducible( R::RootStr ) -> BoolElt
{True iff R is abolutely irreducible}
  return IsIrreducible( SplitRootDatum( R ) );
end intrinsic;




intrinsic IsCrystallographic( R::RootSys ) -> BoolElt
{} /* get comment from the next intrinsic */
  if not assigned R`IsCrystallographic then
    R`IsCrystallographic := IsCrystallographic( CartanMatrix( R ) );
  end if;
  return R`IsCrystallographic;
end intrinsic;

intrinsic IsCrystallographic( R::RootDtm ) -> BoolElt
{True iff R is crystallographic}
  return true;
end intrinsic;


intrinsic IsSimplyLaced( R::RootStr ) -> BoolElt
{True iff R is simply laced}
  return IsSimplyLaced( CoxeterGraph( R ) );
end intrinsic;

intrinsic IsWeaklyAdjoint( R::RootDtm ) -> BoolElt
{True iff R is (weakly) adjoint}
	if assigned R`IsWeaklyAdjoint then return R`IsWeaklyAdjoint; end if;
		
	rnkR := Rank(R); dimR := Dimension(R);
	if rnkR eq dimR then
		R`IsWeaklyAdjoint := IsTrivial( IsogenyGroup(R) );
	else
		assert rnkR lt dimR;
		GT := AbelianGroup([0 : i in [1..dimR-rnkR]]);
		R`IsWeaklyAdjoint := IsIsomorphic(GT, IsogenyGroup(R) );
	end if;

	return R`IsWeaklyAdjoint;
end intrinsic;

intrinsic IsWeaklySimplyConnected( R::RootDtm ) -> BoolElt
{True iff R is (weakly) simply connected}
	if assigned R`IsWeaklySimplyConnected then return R`IsWeaklySimplyConnected; end if;

	rnkR := Rank(R); dimR := Dimension(R);
	if rnkR eq dimR then
		R`IsWeaklySimplyConnected := IsTrivial( CoisogenyGroup(R) );
	else
		assert rnkR lt dimR;
		GT := AbelianGroup([0 : i in [1..dimR-rnkR]]);
		R`IsWeaklySimplyConnected := IsIsomorphic(GT, CoisogenyGroup(R) );
	end if;

	return R`IsWeaklySimplyConnected;
end intrinsic;


intrinsic IsAdjoint( R::RootDtm ) -> BoolElt
{True iff R is adjoint (implies semisimplicity)}
	if assigned R`IsAdjoint then return R`IsAdjoint; end if;
		
	rnkR := Rank(R); dimR := Dimension(R);
	R`IsAdjoint := (rnkR eq dimR) and IsWeaklyAdjoint(R);
	return R`IsAdjoint;
end intrinsic;

intrinsic IsSimplyConnected( R::RootDtm ) -> BoolElt
{True iff R is simply connected (implies semisimplicity)}
	if assigned R`IsSimplyConnected then return R`IsSimplyConnected; end if;
		
	rnkR := Rank(R); dimR := Dimension(R);
	R`IsSimplyConnected := (rnkR eq dimR) and IsWeaklySimplyConnected(R);

	return R`IsSimplyConnected;
end intrinsic;



// ----------------------------------------------------
//
// Printing and Dynkin diagrams
//

intrinsic HackobjPrintRootStr( R::RootStr, l::MonStgElt )
{internal}
    // all RootDtm, RootSys obj are ISA RootStr. 
    // but there must be no actual objects of this type!
    error "There must be no objects of type RootStr in Magma";
end intrinsic;

intrinsic HackobjPrintNamedRootDtm( R::RootDtm, l::MonStgElt, name::MonStgElt )
{Print the root datum R at level l}
  if l ne "Magma" and name ne "$" then
    printf "%o: ", name;
  end if;
  HackobjPrintRootDtm(R,l);
end intrinsic;

intrinsic HackobjPrintRootDtm( R::RootDtm, l::MonStgElt )
{Print the root datum R at level l}
  if not assigned R`CartanMatrix then
    printf "Incomplete root datum";
    return;
  end if;
  if l ne "Magma" then
    started:=false;
    if Category(R) eq RootDtmSprs then
      printf "Sparse "; started:=true;
    end if; 
    if IsTwisted(R) then
      printf started select "t" else "T";
      printf "wisted "; started:=true;
    end if; 
    if R`Rank eq 0 then
      printf started select "t" else "T";
      printf "oral root datum of dimension %o", Dimension( R );
      return;
    end if;
    cartan_name := IsTwisted(R) select TwistedCartanName( R ) else CartanName( R );
    if assigned R`IsAdjoint and R`IsAdjoint then
      printf started select "a" else "A";
      printf "djoint "; started:=true;
    elif assigned R`IsSimplyConnected and R`IsSimplyConnected then
      printf started select "s" else "S";
      printf "imply connected "; started:=true;
    elif assigned R`IsWeaklyAdjoint and R`IsWeaklyAdjoint then
      printf started select "(w" else "(W";
	  printf "eakly) adjoint "; started := true;
    elif assigned R`IsWeaklySimplyConnected and R`IsWeaklySimplyConnected then
      printf started select "(w" else "(W";
	  printf "eakly) simply connected "; started := true;
    end if;
    printf started select "r" else "R";
    printf "oot datum of dimension %o of type %o", Dimension(R), cartan_name;
    if l eq "Maximal" then
      printf "\n";
      print "with simple roots";        IndentPush();printf "%o\n", R`SimpleRoots;         IndentPop();
      print "and simple coroots";       IndentPush();printf "%o\n", R`SimpleCoroots;       IndentPop();
      print "and extraspecial signs";   IndentPush();printf "%o",   R`ExtraspecialSigns;   IndentPop();
      if IsTwisted(R) then
        printf "\n";
        print "The twist is given by the action of";    
                                        IndentPush();printf "%o\n", R`GammaAction`gamma;   IndentPop();
        print "on roots induced by";    IndentPush();printf "%o\n", R`GammaAction`mats_rt; IndentPop();
        print "on coroots induced by";  IndentPush();printf "%o",   R`GammaAction`mats_co; IndentPop();
      end if;
    end if;
  else
    if not IsReduced(R) then
        nonred := Sprintf(", Nonreduced := %o", nonredSimpleRoots(R) );
    else
        nonred := "";
    end if;
    if IsTwisted(R) then
        twist := Sprintf(", Twist := <%o,%o,%o>",  Sprint(R`GammaAction`gamma,  "Magma"),
                                                   Sprint(R`GammaAction`mats_rt,"Magma"),
                                                   Sprint(R`GammaAction`mats_co,"Magma") );
    else
        twist := "";
    end if;
    if Category(R) eq RootDtmSprs then printf "Sparse"; end if;
    printf "RootDatum( %o, %o : Signs := %o%o%o )",
    Sprint( R`SimpleRoots,       "Magma" ),
    Sprint( R`SimpleCoroots,     "Magma" ),
    Sprint( R`ExtraspecialSigns, "Magma" ),
    nonred,
    twist;
  end if;
end intrinsic;

intrinsic HackobjPrintNamedRootSys( R::RootSys, l::MonStgElt, name::MonStgElt )
{Print the root system R at level l}
  if l ne "Magma" and name ne "$" then
    printf "%o: ", name;
  end if;
  HackobjPrintRootSys(R,l);
end intrinsic;

intrinsic HackobjPrintRootSys( R::RootSys, l::MonStgElt )
{Print the root system R at level l}
  if l ne "Magma" then
    if R`Rank eq 0 then
      printf "Trivial root system of dimension %o", Dimension( R );
      return;
    end if;
    printf "Root system of dimension %o of type %o", Dimension( R ), CartanName( R );
    if l eq "Maximal" then
      printf "with simple roots\n%o\nand simple coroots\n%o",
             R`SimpleRoots, R`SimpleCoroots;
    end if;
  else
    printf "RootSystem( %o, %o )",
    Sprint( R`SimpleRoots,   "Magma" ),
    Sprint( R`SimpleCoroots, "Magma" );
  end if;
end intrinsic;


intrinsic DynkinDiagram( R::RootStr )
{Print the Dynkin diagram of the root system R}
  require IsCrystallographic( R ) : "R must be crystallographic";
  typeToDiagram( toType( R ) );
end intrinsic;

intrinsic CoxeterDiagram( R::RootStr )
{Print the Coxeter diagram of the root system R}
  typeToDiagram( toType( R ) : coxeter );
end intrinsic;



// ====================================================
//
// Creating new root data from old
//
// ====================================================

// ----------------------------------------------------
//
// Duals
//

// Used to sort the roots of duals and subdata
rootOrder := function( u, v )
  n := #Eltseq(u);
  height := func< v | &+Eltseq(v) >;

  h := height(u);  k := height(v);
  if h ne k then
    if   h gt 0 and k lt 0 then return -1;
    elif h lt 0 and k gt 0 then return 1;
    elif h gt 0 and k gt 0 then return h-k;
    else return k-h;
    end if;
  else
    if h eq 0 then return 0; end if;
    b := exists(i){i : i in [n..1 by -1] | u[i] ne v[i]};
    if u[i] gt 0 or v[i] gt 0 then
      return u[i]-v[i];
    else
      return v[i]-u[i];
    end if;
  end if;
end function;

fixCoordinates := function(v,coords,factor);
    return [ (i in coords select factor else 1)*v[i] : i in [1..Degree(v)] ];
end function;

rootDual := function( R );
  dtm := ISA(Category(R), RootDtm);
  attr := GetAttributes(Category(R));

  // to compute signs, wen unfortunately have to sort the roots first
  roots := Coroots( R : Basis := "Root" );  n := #roots;
  Vr := Universe(roots);
  if not IsReduced(R) then
    dblbl := nonredSimpleRoots(R);
    roots := {@ Vr | fixCoordinates(v,dblbl,2) : v in roots @};
  end if;
  perm  := (n ne 0) select Sym(n)!1 else Sym(1)!1;
  Sort( ~roots, rootOrder, ~perm );

  type := dualOfType( toType(R) );
  if dtm then
      l     := Rank(R);  N := NumPosRoots(R);
      signs := ExtraspecialSigns( R );
      signs := [ pos gt 0 select signs[pos] else 1 where pos := (i+l)^perm - l : i in [1..N-l] ];
      ga := R`GammaAction;
      new_ga := rec<GA_RF| gamma   := ga`gamma,   mats_rt := ga`mats_co,
                           perm_ac := ga`perm_ac, mats_co := ga`mats_rt >;
      dual, is_new := createRawDtm(R`SimpleCoroots,R`SimpleRoots,type,signs,new_ga);
      if not is_new then 
        I := IdentityMatrix( baseField(R), Dimension(R) );
        return dual, DualMorphism( R, dual, I, I : Check:=false );
      end if;
  else
      dual := createRawSys(R`SimpleCoroots,R`SimpleRoots);
      dual`Type := type;
  end if;

  for field in [ "BaseField", "NumPosRoots", "Rank", "Dimension",
  "CoxeterMatrix", "CoxeterGraph", "IsIrreducible",
  "IsCrystallographic", "IsSemisimple", "IsSimplyLaced", "MaximumMultiplicity" ] do
    if field in attr and assigned R``field then
      dual``field := R``field;
    end if;
  end for;

  d := Dimension(dual);
  if dtm then
    dual`RootSpace   := CreateRootVectorSpace( Rationals(), d, dual );
    dual`CorootSpace := CreateRootVectorSpace( Rationals(), d, dual : Coroots := true );
  else
    dual`RootSpace   := R`CorootSpace;
    dual`CorootSpace := R`RootSpace;
  end if;
  if assigned R`CartanMatrix then
    dual`CartanMatrix := Transpose( R`CartanMatrix );
  end if;

  // roots and perm were computed above.
  dual`RootSystem   := roots;
  Vc := Universe(R`RootSystem); 
  coroots := {@ Vc | R`RootSystem[ i^perm ] : i in [1..n] @};
  if not IsReduced(R) then
    // dblbl already compured above
    coroots := {@ Vc | fixCoordinates(v,dblbl,1/2) : v in coroots @};
  end if;
  dual`CorootSystem := coroots;
  dual`Name := typeToName( dual`Type );
  if assigned R`ReflectionPerms then
    dual`ReflectionPerms := [];
    for i in [1..2*NumPosRoots(R)] do
      if IsDefined( R`ReflectionPerms, i^perm ) then 
        dual`ReflectionPerms[i] := R`ReflectionPerms[ i^perm ]^(perm^-1);
      end if;
    end for;
  end if;
  if dtm then
    if assigned R`IsAdjoint then
      dual`IsSimplyConnected := R`IsAdjoint;
    end if;
    if assigned R`IsSimplyConnected then
      dual`IsAdjoint := R`IsSimplyConnected;
    end if;
  end if;
  if assigned R`RootNorms then
    dual`CorootNorms := [ R`RootNorms[ i^perm ] : i in [1..n] ];
  end if;
  if assigned R`CorootNorms then
    dual`RootNorms := [ R`CorootNorms[ i^perm ] : i in [1..n] ];
  end if;
  if assigned R`CoxeterForm then
    dual`DualCoxeterForm := R`CoxeterForm;
  end if;
  if assigned R`DualCoxeterForm then
    dual`CoxeterForm := R`DualCoxeterForm;
  end if;

  assignSpaces(~dual);

  if dtm then
    dual`multiplicationData := [ [Parent([Parent(<1,1,1,1>)|])|] : i in [1..N] ];
    dual`LieConstant_eta    := [ [Integers()|] : i in [1..2*N] ];
    dual`cartanIntegers     := [ [Integers()|] : i in [1..2*N] ];
  end if;

  if dtm then
    I := IdentityMatrix( baseField(R), Dimension(R) );
    return dual, DualMorphism( R, dual, I, I : Check:=false );
  else
    return dual;
  end if;
end function;

intrinsic Dual( R::RootStr ) -> RootStr, .
{The dual of R}
  return rootDual( R );
end intrinsic;

// ----------------------------------------------------
//
// Root subdata
//
// this function MUST return two objects: subdatum S and an injection S->R
// injection is in this case a sequence of integers mapping roots of S to roots of R.
//
// if this function returns less than two objects, we'll get STRANGE errors from C level.
// 
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
rootSub := function( R, simples : preserve:=false )

  // first, do an easy check if the whole thing is requested.
  if     preserve and simples eq &cat[t[2] : t in toType(R)] 
  or not preserve and Seqset(simples) eq {1..Rank(R)} 
  then 
    return R, [1..2*NumPosRoots(R)];
  end if;
  
  dtm := ISA(Category(R), RootDtm);

  if dtm then
    /* want the result to be sparse? */
    /* we can add a non-twisted torus to a sparse root datum */
    sprs := Category(R) eq RootDtmSprs and Seqset(simples) subset {1..Rank(R)}
                                       and simples eq Sort(simples);
  end if;


  k := BaseRing( R );
  if IsEmpty( simples ) then
    M := Matrix( k, 0, Dimension(R), [k|] );
    if dtm then
      ga := R`GammaAction;
      Ga := ga`gamma;
      return rootDatum( M, M, M*Transpose(M), [**], [Integers()|] 
                : twist := rec<GA_RF| gamma   := Ga,
                                      perm_ac := hom<Ga->Sym(1)|[1: i in [1..Ngens(Ga)]]>,
                                      mats_rt := ga`mats_rt,
                                      mats_co := ga`mats_co> ), [];
    else
      return rootSystem( M, M, M*Transpose(M), [**], R`RealInjection ), [];
    end if;
  end if;
  X := RootSpace( R );

  // compute roots in subdatum
  incl := OrbitClosure( sub<W|[Reflection(W,r):r in gens]>, gens )
    where W is CoxeterGroup( R ) where gens is Seqset(simples);
  incl := Set( incl );
  nonred := {};
  if not IsReduced(R) then
    for r in incl do
      pos := RootPosition(R,2*Root(R,r));
      if pos ne 0 then
        Include(~incl,pos);
        Include(~nonred,r);
      end if;
    end for;
  end if;
  incl   := Sort( Setseq( incl ) );
  if dtm then
    im := Image(R`GammaAction`perm_ac);
    if #Orbit(im, Set(incl)) ne 1 then
        return "GammaAction doesn't normalise the subdatum",_;
    end if;
  end if;

	// Check closedness
	if dtm then
		for i,j in incl do
			r := RootPosition(R, Root(R,i) + Root(R,j));
			if r ne 0 and r notin incl then error "The given roots do not produce a closed subdatum."; end if;
		end for;
	end if;
	
  // compute simple roots
  if not preserve then
    tdim := Dimension( sub< X | [Root(R,r) : r in simples] > );  
    new := [];  i := 1;  dim := 0;
    repeat
      if Dimension( sub< X | [Root(R,r) : r in Append(new,incl[i])] > ) gt dim then
        Append( ~new, incl[i] );  dim +:= 1;
      end if;
      i +:= 1;
    until dim eq tdim;
    simples := new;
  end if;

  // reorder roots
  spc := dtm select RSpace(k,#simples) else VectorSpace(k,#simples);
  if preserve and not IsIndependent( [ Root(R,r:Basis:="Root") : r in simples ] ) then
    return "The given roots are not simple in a subdatum",_ ;
  end if;    
  roots := {@ spc!Coordinates( V, V!Root(R,r:Basis:="Root") ) : r in incl @}
    where V is RSpaceWithBasis( [ Root(R,r:Basis:="Root") : r in simples ] );
  perm := Sym(#roots)!1;
  Sort( ~roots, rootOrder, ~perm );
  incl := [ incl[i^perm] : i in [1..#roots] ];
  subN := #roots div 2;

  // need special "Sign" intrinsic for non-crystallographic root systems
  if not dtm and ISA(Category(k), FldAlg) then
     mySign := func<x|[Sign(c) : c in Eltseq(x)]>;
  else
     mySign := Sign;
  end if;
  
  // check simplicity
  if preserve and not forall{ v : v in roots | #{ mySign(a) : a in Eltseq(v) | a ne 0 } eq 1 } then
    return "The given roots are not simple in a subdatum",_ ;
  end if;

  nonred := nonred meet Seqset(simples);
  nonred_sim := {Position(simples,r):r in nonred};
  A := Matrix( IndexedSetToSequence(  Roots(R))[[r:r in simples]] );
  B := Matrix( IndexedSetToSequence(Coroots(R))[[r:r in simples]] );
  C := Matrix( Integers(), A * Transpose(B) );
  type := cartanToType( C : nonred:=nonred_sim );
  // create the subsystem
  if dtm then
    if sprs then
      S := createRawSprsDtm ( A,B,type,100 ); // 100 is used as a HACK, since we can't compute signs here
    else
      gamma   := R`GammaAction`gamma;
      perm_ac := R`GammaAction`perm_ac;
      im := Image(perm_ac);
      oa := OrbitAction(im, incl);
      new_ga := rec<GA_RF| gamma   := gamma,
                           perm_ac := hom<gamma->Codomain(oa)| [ oa(perm_ac(gamma.i)) : i in [1..Ngens(gamma)]  ] >,
                           mats_rt := R`GammaAction`mats_rt, 
                           mats_co := R`GammaAction`mats_co> ;
      
      S, is_new := createRawDtm(A,B,type,100,new_ga); // 100 is used as a HACK, since we can't compute signs here

      // the following should never happen!  
			// AND YET IT DOES HAPPEN!! -- so I commented it out.
      //if not is_new then return S,incl; end if;
    end if;
  else;
      S := createRawSys(A,B);
      S`Type := type;
  end if;

  for field in [ "RootSpace", "CorootSpace", "Dimension" ] do
    if assigned R``field then
      S``field := R``field;
    end if;
  end for;
  if not dtm then  S`BaseField := k;  end if;
  S`CartanMatrix  := C;
  S`Name          := typeToName(type);
  if dtm and not sprs then 
    S`RootSystem    := roots;
  end if;
  S`NumPosRoots   := subN;
  S`Rank          := #simples;
  S`Dimension     := R`Dimension;
  assignSpaces(~S);
  if not dtm then
    S`RealInjection := R`RealInjection;
  end if;

  // compute coroots
  if assigned R`CorootSystem then
    S`CorootSystem := 
      {@ spc!Coordinates( V, V!Coroot(R,r:Basis:="Root") ) : r in incl @}
      where V is RSpaceWithBasis( [ Coroot(R,r:Basis:="Root") : r in simples ] );
  end if;

  if dtm then
    // ensure consistency of structure constants
    pairs := ExtraspecialPairs( S );
    signs := [Integers()|];
    for pair in pairs do
      Append( ~signs, e eq 0 select 1 else e where e is LieConstant_epsilon( R, incl[pair[1]], incl[pair[2]] ) );
    end for;
    if sprs then
        S`ExtraspecialSigns := signs;
    else 
        // now the following part is ugly:
        // drop the RootDatum
        InternalDropRootDatum(S);
        // assign new signs
        S`ExtraspecialSigns := signs;
        // and reinsert S
        S, is_new := InternalCreateRootDatum(S);
        if is_new then vprint  ROOTS,1 : "*"; end if;
        //if not is_new then return S,incl; end if;
    end if;
  end if;

  if dtm and not sprs then
    S`multiplicationData := [ [Parent([Parent(<1,1,1,1>)|])|] : i in [1..#roots div 2] ];
    S`LieConstant_eta    := [ [Integers()|] : i in [1..#roots] ];
    S`cartanIntegers     := [ [Integers()|] : i in [1..#roots] ];
  end if;

  return S, incl;
end function;


intrinsic HackobjSubConstrRootDtm( R::RootDtm, simples::SeqEnum ) -> RootDtm, .
{The root subdatum of R with the given simples}
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
  N := NumPosRoots( R );
  if not Seqset(simples) subset {0..2*N} then 
    return "Root indices not in the correct range",_; 
  end if;
  return rootSub( R, simples : preserve );
end intrinsic;

intrinsic HackobjSubConstrRootSys( R::RootSys, simples::SeqEnum ) -> RootSys, .
{The root subsystem of R with the given simples}
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
  N := NumPosRoots( R );
  if not Seqset(simples) subset {0..2*N} then 
    return "Root indices not in the correct range",_; 
  end if;
  return rootSub( R, simples : preserve );
end intrinsic;

intrinsic HackobjSubConstrRootDtm( R::RootDtm, gens::SetEnum ) -> RootDtm, .
{The root subdatum of R generated by gens}
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
  N := NumPosRoots( R );
  if not gens subset {0..2*N} then 
    return "Root indices not in the correct range",_; 
  end if;
  return rootSub( R, Setseq(gens) );
end intrinsic;

intrinsic HackobjSubConstrRootSys( R::RootSys, gens::SetEnum ) -> RootSys, .
{The root subsystem of R generated by gens}
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
  N := NumPosRoots( R );
  if not gens subset {0..2*N} then 
    return "Root indices not in the correct range",_; 
  end if;
  return rootSub( R, Setseq(gens) );
end intrinsic;

intrinsic HackobjSubConstrRootDtm( R::RootDtm, U::ModTupFld, V::ModTupFld ) -> RootDtm, .
{The root subdatum of R on the subspaces U (resp V) of the (co)root space}
// MUST NOT USE require/error. use
//      return "error nmessage", _;  [take care of the second return value!!!]
// in case of an error.
  //print "01";
  if Dimension(U) ne Dimension(V) then
    return "The given subspaces do not define a root subdatum",_;
  end if;
  N := NumPosRoots( R );
  rts  := [ r : r in [1..N] | Root(R,r) in U ];
  if rts ne [ r : r in [1..N] | Coroot(R,r) in V ] then
    return "The given subspaces do not define a root subdatum",_;
  end if;
  X := RootSpace( R );
  
  // compute simples
  tdim := Dimension( sub< X | [Root(R,r) : r in rts] > );  
  simples := [];  i := 0;  dim := 0;
  while dim lt tdim do
    i +:= 1;
    if Dimension( sub< X | [Root(R,r) : r in Append(simples,rts[i])] > ) gt dim then
      Append( ~simples, rts[i] );  dim +:= 1;
    end if;
  end while;

  S, incl := rootSub( R, simples );
  S`RootSpace := U;  S`CorootSpace := V;
  S`Dimension := Dimension(U);

  return S, incl;
end intrinsic;

// We currently recognise a covering structure if
// the root and coroot spaces have a covering stucture
// and R subseteq S, S subseteq R, or they span disjoint 
// subspaces.

// for twisted root data we say that a twisted one is contained 
// in it's untwisted form. and the covering structure for 
// twisted is not necessarily smallest possible.

existsCoveringStructure := function( R, S )
  if ISA(Category(R),RootDtm) and IsTwisted(R) then
    R := UntwistedRootDatum(R);
  end if;
  if ISA(Category(S),RootDtm) and IsTwisted(S) then
    S := UntwistedRootDatum(S);
  end if;
  XR := RootSpace( R );  XS := RootSpace( S );
  ok, X := ExistsCoveringStructure( XR, XS );
  if not ok then  return false, _, _, _, _;  end if;
  
  YR := CorootSpace( R );  YS := CorootSpace( S );
  ok, Y := ExistsCoveringStructure( YR, YS );
  if not ok then  return false, _, _, _, _;  end if;

  rtsR := ChangeUniverse( Roots( R ), X );
  rtsS := ChangeUniverse( Roots( S ), X );
  crsR := ChangeUniverse( Coroots( R ), Y );
  crsS := ChangeUniverse( Coroots( S ), Y );
  if rtsR subset rtsS and crsR subset crsS then
    rtpos := [ Position( rtsS, v ) : v in rtsR ];
    if rtpos eq [ Position( crsS, v ) : v in crsR ] then
      return true, S, true, rtpos, [1..#rtsS];
    end if;
  elif rtsS subset rtsR and crsS subset crsR then
    rtpos := [ Position( rtsR, v ) : v in rtsS ];
    if rtpos eq [ Position( crsR, v ) : v in crsS ] then
      return true, R, false, [1..#rtsR], rtpos;
    end if;
  else
    rtspanR := sub< X | ChangeUniverse( Roots( R ), X ) >;
    rtspanS := sub< X | ChangeUniverse( Roots( S ), X ) >;
    crspanR := sub< Y | ChangeUniverse( Coroots( R ), Y ) >;
    crspanS := sub< Y | ChangeUniverse( Coroots( S ), Y ) >;
    if rtspanR meet rtspanS eq sub<X|> and crspanR meet crspanS eq sub<X|> then
      A := VerticalJoin( SimpleRoots(R), SimpleRoots(S) );
      B := VerticalJoin( SimpleCoroots(R), SimpleCoroots(S) );
      if IsCartanMatrix( A*Transpose(B) ) then
        T := (Category(R) eq RootSys) select RootSystem(A,B) else RootDatum(A,B);
        return true, T, false, 
          [ RootPosition( T, v ) : v in rtsR ], [ RootPosition( T, v ) : v in rtsS ];
      end if;
    end if;
  end if;

  return false, _, _, _, _;
end function;


intrinsic InternalExistsCoveringStructureRootSystem( R::RootSys, S::RootSys ) ->
  BoolElt
{Intrinsic for internal use only}
  ok, T, sub, injR, injS := existsCoveringStructure( R, S );
  return ok, T, injR, injS;
end intrinsic;

intrinsic InternalCoveringStructureRootSystem( R::RootSys, S::RootSys ) ->
  BoolElt
{Intrinsic for internal use only}
  ok, T, sub, injR, injS := existsCoveringStructure( R, S );
  require ok : "No covering structure";
  return T, injR, injS;
end intrinsic;

intrinsic 'subset'( R::RootSys, S::RootSys ) -> BoolElt, .
{True if R is a subset of S}
  ok, T, sub, injR, injS := existsCoveringStructure( R, S );
  if sub then  return sub, injR;
  else         return sub, _;
  end if;
end intrinsic;


intrinsic InternalExistsCoveringStructureRootDatum( R::RootDtm, S::RootDtm ) ->
  BoolElt
{True if R is a subset of S}
  ok, T, sub, injR, injS := existsCoveringStructure( R, S );
  return ok;
end intrinsic;

intrinsic InternalCoveringStructureRootDatum( R::RootDtm, S::RootDtm ) ->
  BoolElt
{Intrinsic for internal use only}
  ok, T, sub, injR, injS := existsCoveringStructure( R, S );
  require ok : "No covering structure";
  return T;
end intrinsic;

intrinsic 'subset'( R::RootDtm, S::RootDtm ) -> BoolElt
{Intrinsic for internal use only}
  ok, T, is_sub, injR, injS := existsCoveringStructure( R, S );
  if ok and is_sub then  return is_sub, injR;
  else                   return false, _;
  end if;
end intrinsic;

//intrinsic 'subset'( 

/*intrinsic 'subset'( R::RootDtm, S::RootDtm ) -> BoolElt, []
{True iff R is a root subdatum of S}
  if Dimension(R) ne Dimension(S) then  return false;  end if;
  rtR := Roots( R );  rtS := Roots( S );
  crR := Coroots( R ); crS := Coroots( S );
  rtpos := [ Position( rtS, rtR[r] ) : r in 
end intrinsic;
*/

// ----------------------------------------------------
//
// Direct sums
//
rootSum := function( R1, R2 )
  dtm := ISA(Category(R1), RootDtm);

  if dtm then
    /* want the result to be sparse? */
    /* we can add a non-twisted torus to a sparse root datum */
    sprs := Category(R1) eq RootDtmSprs and Rank(R2) eq 0 and not IsTwisted(R2)
         or Category(R2) eq RootDtmSprs and Rank(R1) eq 0 and not IsTwisted(R1);
  end if;

  if dtm then
    k := CoveringStructure(BaseRing(R1),BaseRing(R2));
  else
    k1 := BaseField( R1 );
    k2 := BaseField( R2 );
    if Category( k1 ) eq FldRat then
      k := k2;
    elif Category( k2 ) eq FldRat then
      k := k1;
    elif Category( k1 ) eq FldCyc and Category( k2 ) eq FldCyc then
      ord1 := CyclotomicOrder( BaseRing( R1`RootSpace ) );
      ord2 := CyclotomicOrder( BaseRing( R2`RootSpace ) );
      k := CyclotomicField( Lcm(ord1, ord2) );
    // use MergeFields!!
    else
      error "Unable to find the join of the base fields";
    end if;
  end if;
  
  diag := func< A, B | DiagonalJoin( ChangeRing(A, k), ChangeRing(B, k) ) >;
  A := diag( R1`SimpleRoots,   R2`SimpleRoots   );
  B := diag( R1`SimpleCoroots, R2`SimpleCoroots );
  N1 := NumPosRoots(R1);  N2 := NumPosRoots(R2);  N := N1+N2;

  type2 := toType(R2);
  n1 := Rank(R1);
  for i in [1..#type2] do
    type2[i][2] := [ r+n1 : r in type2[i][2] ];
  end for;
  type := toType(R1) cat type2;

  if dtm then
    signs := ExtraspecialSigns( R1 ) cat ExtraspecialSigns( R2 );
    
    if not sprs then
        gamma1 := Domain(R1`GammaAction`perm_ac);
        gamma2 := Domain(R2`GammaAction`perm_ac);
        gamma  := DirectProduct( gamma1,gamma2 );
 
        I1 := MatrixAlgebra(Integers(),Dimension(R1))!1;
        I2 := MatrixAlgebra(Integers(),Dimension(R2))!1;

		Urt := Universe(R1`GammaAction`mats_rt);
		Uco := Universe(R1`GammaAction`mats_co);
        mats_rt := [ Urt | diag(m,I2) : m in R1`GammaAction`mats_rt ]
                cat[ diag(I1,m) : m in R2`GammaAction`mats_rt ];
        mats_co := [ Uco | diag(m,I2) : m in R1`GammaAction`mats_co ]
                cat[ diag(I1,m) : m in R2`GammaAction`mats_co ];

        ga := rec<GA_RF|gamma := gamma,
                        // can't compute that yet. do it after roots are computed.
                        // perm_ac := hom<Sym(1)->Sym(2*(NumPosRoots(R1)+NumPosRoots(R2)))|[]>,
                        mats_rt := mats_rt, mats_co:=mats_co>;

        sum, is_new := createRawDtm     ( A,B,type,signs,ga );
        if not is_new then return sum; end if;
    else
        sum         := createRawSprsDtm ( A,B,type,signs );
    end if;
  else
        sum         := createRawSys     ( A,B );
        sum`Type := type;
  end if;
  
  if not dtm then  
    sum`BaseField := k;
  end if;
  
  vssum := function( V1, V2 )
    if not dtm and Category(k) ne FldRat then
      V1 := ChangeRing( V1, k );  V2 := ChangeRing( V2, k );
    end if;
    return DirectSum( V1, V2 );
  end function;
  sum`RootSpace   := vssum( R1`RootSpace, R2`RootSpace );
  sum`CorootSpace := vssum( R1`CorootSpace, R2`CorootSpace );

  sum`NumPosRoots := N;
  for field in [ "Rank", "Dimension" ] do
    if assigned R1``field and assigned R2``field then
      sum``field := R1``field + R2``field;
    end if;
  end for;

  C := A*Transpose(B);
  is_c,newC := IsCoercible( MatrixAlgebra(Integers(),sum`Rank), C);
  if is_c then
    sum`CartanMatrix := newC;
  else
    sum`CartanMatrix := C;
  end if;
  

  sum`Name := R1`Name cat R2`Name;

  assignSpaces(~sum);

  vect := func< V, v, w | V!( Eltseq(v) cat Eltseq(w) ) >;

  if assigned R1`RootSystem and assigned R2`RootSystem then
    rts1 := R1`RootSystem;  rts2 := R2`RootSystem;
    V1 := Universe(rts1);   V2 := Universe(rts2);
    V := vssum( V1, V2 );
    R := [ vect( V, rts1[r], V2!0 ) : r in [1..N1] ] cat
         [ vect( V, V1!0, rts2[r] ) : r in [1..N2] ];
    perm := ( N1+N2 ne 0 ) select Sym(N1+N2)!1 else Sym(1)!1;
    Sort( ~R, rootOrder, ~perm );
    sum`RootSystem := {@ V | v : v in R @} join {@ V | -v : v in R @};
    if assigned R1`CorootSystem and assigned R2`CorootSystem then
      rts1 := R1`CorootSystem;  rts2 := R2`CorootSystem;
      V1 := Universe(rts1);   V2 := Universe(rts2);
      V := vssum( V1, V2 );
      R := [ vect( V, rts1[r], V2!0 ) : r in [1..N1] ] cat
        [ vect( V, V1!0, rts2[r] ) : r in [1..N2] ];
      R := [ R[r^perm] : r in [1..N1+N2] ];  
      sum`CorootSystem := {@ V | v : v in R @} join {@ V | -v : v in R @};
    end if;
  end if;
  
  if dtm and not sprs then
    rts := Roots(sum);
    codom := N eq 0 select Sym(1) else Sym(2*N);
    sum`GammaAction`perm_ac := 
        hom<gamma->codom| [ [ Position(rts,rts[r]*mats_rt[i]) 
                            : r in [1..2*N] 
                            ] 
                          : i in [1..Ngens(gamma)]
                          ]>;
  end if;
  
  for field in [ "IsSemisimple" ] cat ((dtm) select [ "IsAdjoint", "IsSimplyConnected" ] else [ "IsCrystallographic" ]) do
    if assigned R1``field and assigned R2``field then
      sum``field := R1``field and R2``field;
    end if;
  end for;
/*  if assigned R1`ReflectionPerms and assigned R2`ReflectionPerms then
    G1 := sub< Universe(R1`ReflectionPerms) | R1`ReflectionPerms >;
    G2 := sub< Universe(R2`ReflectionPerms) | R2`ReflectionPerms >;
    G := DirectProduct( G1, G2 )^perm;
    sum`ReflectionPerms := [ G.i : i in [1..NumberOfGenerators(G)] ];
  end if;*/
  if assigned R1`MaximumMultiplicity and assigned R2`MaximumMultiplicity then
    sum`MaximumMultiplicity := Max( R1`MaximumMultiplicity, R2`MaximumMultiplicity );
  end if;
  if assigned R1`RootNorms and assigned R2`RootNorms then
    sum`RootNorms := R1`RootNorms cat R2`RootNorms;
  end if;
  if assigned R1`CorootNorms and assigned R2`CorootNorms then
    sum`CorootNorms := R1`CorootNorms cat R2`CorootNorms;
  end if;
  if assigned R1`CoxeterForm and assigned R2`CoxeterForm then
    sum`CoxeterForm := DiagonalJoin( R1`CoxeterForm, R2`CoxeterForm );
  end if;
  if assigned R1`DualCoxeterForm and assigned R2`DualCoxeterForm then
    sum`DualCoxeterForm := DiagonalJoin( R1`DualCoxeterForm, R2`DualCoxeterForm );
  end if;

  if dtm and not sprs then
    sum`multiplicationData := [ [Parent([Parent(<1,1,1,1>)|])|] : i in [1..N] ];
    sum`LieConstant_eta    := [ [Integers()|] : i in [1..2*N] ];
    sum`cartanIntegers     := [ [Integers()|] : i in [1..2*N] ];
  end if;
  
  return sum;
end function;

// don't use RootStr here to avoid dubious checks ensuring 
// that wen don't sum a root datum and a root system  :)
intrinsic '+'( R1::RootDtm, R2::RootDtm ) -> RootDtm
{The (external) direct sum of R1 and R2}
  return rootSum( R1, R2 );
end intrinsic;
intrinsic '+'( R1::RootSys, R2::RootSys ) -> RootSys
{The (external) direct sum of R1 and R2}
  return rootSum( R1, R2 );
end intrinsic;


intrinsic DirectSum( R1::RootDtm, R2::RootDtm ) -> RootDtm
{The (external) direct sum of R1 and R2}
  return rootSum( R1, R2 );
end intrinsic;
intrinsic DirectSum( R1::RootSys, R2::RootSys ) -> RootSys
{The (external) direct sum of R1 and R2}
  return rootSum( R1, R2 );
end intrinsic;


// ----------------------------------------------------
//
// Join
//
rootJoin := function( R1, R2 )
    dtm := ISA(Category(R1),RootDtm);

    if dtm then
        singular := "datum"; plural := "data";
    else
        singular := "system"; plural := "systems";
    end if;
    
    if Dimension(R1) ne Dimension(R2) then
      return "The root " cat plural cat " must have the same dimension";
    elif dtm and (IsTwisted(R1) or IsTwisted(R2)) then
      return "The root " cat plural cat " must not be twisted";
    end if;
    
    d := Dimension(R1);       
    n1 := Rank(R1);  n2 := Rank(R2);     
    A1 := SimpleRoots(R1);     B1 := SimpleCoroots(R1);
    A2 := SimpleRoots(R2);     B2 := SimpleCoroots(R2);
    if not dtm then
        ok, K, inj, h1, h2 := cmpRealInj( RealInjection(R1), RealInjection(R2) );
        if Category(ok) eq MonStgElt then  return ok;  end if;
        A1 := Matrix( n1, d, [ h1(x) : x in Eltseq(A1) ] );
        B1 := Matrix( n1, d, [ h1(x) : x in Eltseq(B1) ] );
        A2 := Matrix( n2, d, [ h2(x) : x in Eltseq(A2) ] );
        B2 := Matrix( n2, d, [ h2(x) : x in Eltseq(B2) ] );
    end if;
    A  := VerticalJoin(A1,A2); B  := VerticalJoin(B1,B2);
    
    C := Matrix(A*Transpose(B));
    if not IsCartanMatrix(C) then
        return "The join of the root " cat plural cat 
          " is not a root " cat singular;
    end if;
    nonred := {};
    for t in toType(R1) do
        if t[1] eq "BC" then
           Include(~nonred,t[2][#t[2]]);
        end if;
    end for;
    for t in toType(R2) do
        if t[1] eq "BC" then
           Include(~nonred,t[2][#t[2]]+Rank(R1));
        end if;
    end for;
    if NumPosRoots(R1)+NumPosRoots(R2) ne NumPosRoots(C:Nonreduced:=nonred) then
        return "The root " cat plural cat " must be disjoint";
    end if;
    
    if dtm then
        signs := R1`ExtraspecialSigns cat R2`ExtraspecialSigns;
        R := RootDatum ( A,B : Nonreduced:=nonred, Signs:=signs );
    else
        // FIXME: take care of RealInjection
        R := RootSystem( A,B : Nonreduced:=nonred, RealInjection:=inj );
    end if;
    
    is_sub1, inj1 := R1 subset R;
    is_sub2, inj2 := R2 subset R;
    
    if not (is_sub1 and is_sub2) then
        return "The join of the root " cat plural cat
	  " is not a root " cat singular;
    end if;
    
    return R; //,inj1,inj2;
end function;

intrinsic 'join'( R1::RootStr, R2::RootStr ) -> RootStr, ., .
{The (internal) sum of R1 and R2}
  require Category(R1) eq Category(R2) :    
        Sprintf("Root structures must be of the same type.\nTypes given: %o, %o", Category(R1), Category(R2));
  R := rootJoin( R1, R2 );
  require Category(R) ne MonStgElt : R;
  return R;
end intrinsic;

// ----------------------------------------------------
//
// Ad and SC versions
//

intrinsic SimplyConnectedVersion( R::RootDtm ) -> RootDtm
{The simply connected version S of R; if R irreducible them homomorphism of S to R returned as 2nd value.}
  type := toType( R );
  type := addTorusToType( R, type ); 
  S := rootDatumByList( type, ["SC":i in [1..#type]], ExtraspecialSigns(R) );
  if IsSemisimple(R) then
    h := hom< S -> R | [1..2*NumPosRoots(R)] >;
    return S, h;
  else
    return S, _;
  end if;
end intrinsic;

intrinsic AdjointVersion( R::RootDtm ) -> RootDtm
{The adjoint version S of R; if R irreducible them homomorphism of R to S returned as 2nd value.}
  type := toType( R );
  S := rootDatumByList( type, ["Ad":i in [1..#type]], ExtraspecialSigns(R) );
  if IsSemisimple(R) then
    h := hom< R -> S | [1..2*NumPosRoots(R)] >;
    return S, h;
  else
    return S, _;
  end if;
end intrinsic;





// ----------------------------------------------------
//
// Radical and decompositions
//


intrinsic Radical( R::RootDtm ) -> RootDtm, .
{The radical of R}
  U := NullspaceOfTranspose( SimpleRoots(R) );
  V := NullspaceOfTranspose( SimpleCoroots(R) ); 
  return sub< R | U,V >;
end intrinsic;


// Also want two root datum version?
/*intrinsic '/'( R::RootDtm, U, V ) -> RootDtm
{}
  require U subset RootSpace( R ) : "U must be a subspace of the root space";
  require V subset CorootSpace( R ) : "V must be a subspace of the coroot space";
  require Dimension( U ) eq Dimension( V ) : "U and V must have the same dimension";
  N := NumPosRoots( R );
  rootidxs := [ r : r in [1..N] | Root(R,r) in U ];
  require rootidxs eq [ r : r in [1..N] | Coroot(R,r) in V ] :
  "The roots in U do not match the coroots in V";
  rootidxs := [ r : r in [1..N] | r notin rootidxs ];
  ret := sub< R | Seqset(rootidxs) >;
  ret`RootSpace := U;
  ret`CorootSpace := V;
  ret`Dimension := Dimension( U );
  return ret;  
end intrinsic;*/

intrinsic DirectSumDecomposition( R::RootDtm ) -> [], RootDtm, Map
{The (internal) direct sum decomposition of R}
  require IsSemisimple(R) : "The root datum must be semisimple";
  if IsSimplyConnected(R) or IsAdjoint(R) then
    S := R;  h := IdentityMap(R);
  else
    S, h := SimplyConnectedVersion( R );
  end if;
  type := toType(R);
  summands := [];//  homs := [];
  for t in type do
    if not ( t[1] in "Dd" and #t[2] eq 2  ) then
      summand := sub< S | t[2] >;
      Append( ~summands, summand );//  Append( ~homs, h );
    else
      Append( ~summands, sub< S | [t[2][1]] > );
      Append( ~summands, sub< S | [t[2][2]] > );
    end if;
  end for;
  return summands, S, h;
end intrinsic;

intrinsic IndecomposableSummands( R::RootDtm ) -> [], RootDtm, Map
{The (internal) direct sum decomposition of R}
  return DirectSumDecomposition(R);
end intrinsic;

intrinsic CentralSumDecomposition( R::RootDtm ) -> []
{The (internal) central sum decomposition of R}
  type := toType(R);
  summands := [];//  homs := [];
  for t in type do
    if not ( t[1] in "Dd" and #t[2] eq 2  ) then
      summand := sub< R | t[2] >;
      Append( ~summands, summand );//  Append( ~homs, h );
    else
      Append( ~summands, sub< R | [t[2][1]] > );
      Append( ~summands, sub< R | [t[2][2]] > );
    end if;
  end for;
  return summands, Radical(R);
end intrinsic;


intrinsic DirectSumDecomposition( R::RootSys ) -> []
{The (internal) direct sum decomposition of R}
//  require IsSemisimple(R) : "R must be semisimple";
  type := toType(R);
  summands := {};//  homs := [];
  for t in type do
    summand, h := sub< R | t[2] >;
    Include( ~summands, summand );//  Append( ~homs, h );
  end for;
  return summands;//, homs;
end intrinsic;
intrinsic IndecomposableSummands( R::RootSys ) -> []
{The (internal) direct sum decomposition of R}
  return DirectSumDecomposition(R);
end intrinsic;



// ----------------------------------------------------
//
// Schreier structures for roots
//
computeOrbitReps := procedure( ~R )
  N := NumPosRoots( R );
  if N eq 0 then
    R`SimpleRep := [];  R`SchreierVect := [];  R`BackPointers := [];
    return;
  end if;
  perms := SimpleReflectionPermutations( R );

  computeOrbit := procedure( ~reps, ~vect, ~back, rep )
    orbit := [ rep ];  pos := 1;
    repeat
      pnt := orbit[pos];
      for i in [1..#perms] do
        im := pnt ^ perms[i];
        if reps[im] eq 0 then
          reps[im] := rep;  vect[im] := i;  back[im] := pnt;
          Append( ~orbit, im );
        end if;
      end for;
      pos +:=1;
    until pos gt #orbit;
  end procedure;

  reps := [0 : i in [1..2*N]];
  vect := [];  back := [];
  for rt in [1..Rank(R)] do
    if reps[rt] eq 0 then
      reps[rt] := rt;  vect[rt] := 0;  back[rt] := 0;
      computeOrbit( ~reps, ~vect, ~back, rt );
    end if;
  end for;
  R`SimpleRep := reps;  R`SchreierVect := vect;  R`BackPointers := back;
end procedure;


// ----------------------------------------------------
//
// Root closures
//
intrinsic RootClosure( R::RootDtm, Q::SetEnum[RngIntElt] ) -> SetEnum[RngIntElt]
{The closure of the set of root indices Q}
  N := NumPosRoots( R );
  neg := func< r | (r le N) select r+N else r-N >;
  require Q subset {1..2*N} : "Incorrect root index";
  
  // This could be more efficient -- SHM
  newQ := { Sum(R,r,s) : r in Q, s in Q | r notin {s,neg(s)} }; 
  newQ := newQ diff Q; 
  Exclude( ~newQ, 0 );
  while not IsEmpty( newQ ) do
    newerQ :=  { Sum(R,r,s) : r in Q join newQ, s in newQ | r notin {s,neg(s)} }; 
    Exclude( ~newerQ, 0 );
    Q := Q join newQ;
    newQ := newerQ diff Q;
  end while;
  
  return Q;
end intrinsic;
  

// ----------------------------------------------------
//
// Induced and coinduced root data
//
/*intrinsic Induction( R::RootDtm, M::Lat ) -> RootDtm
{The induction of R to M}
  n := Rank( R );  d := Dimension( R );
  X := FullRootLattice( R );  Y := FullCorootLattice( R );
  require M subset X : "Not a sublattice of the full root lattice";
  require RootLattice(R) subset M : "Does not contain the root lattice";
  
  Mt := Dual( M );
  A := SimpleRoots( R );  B := SimpleCoroots( R );
  A := Matrix( [ Coordinates( M, M!X!A[i] ) : i in [1..n] ] );
  B := Matrix( [ Coordinates( Mt, Mt!Y!B[i] ) : i in [1..n] ] );
  S := RootDatum( A, B );
  phiX := hom< RootSpace(S) -> RootSpace(R) | 
    [ RootSpace(R)!X!m : m in Basis( M ) ] >;
  phiY := hom< CorootSpace(S) -> CorootSpace(R) |
    [CorootSpace(R)!Y!m : m in Basis( Mt ) ] >;
  return S, hom< S -> R | phiX, phiY >;
end intrinsic;


intrinsic Coinduction( R::RootDtm, M::Lat ) -> RootDtm
{The coinduction of R to M}
end intrinsic;
*/







/*
**
**  NON-REDUCED ROOT DATA
**    
**      May 2006, Sergei Haller
**
*/

/*
**   (ref: Bourbaki, VI)
**    Prop 13:
**      let R is irred, non-red., ramk >=2.
**      R_0 set of indivisible roots of R. then
**       (1) R_0 is reduced root datum,
**       (2) A and B are sets of short and long roots of R_0
**       (3) A and B are both non-empty
**       (4) any two non-prop elts in A are orthogonal
**       (5) R = A \cup B \cup 2A
**       (6) W(R) = W(R_0)
**
**    Prop 14:
**      let R_0 be any irred. and reduced. Assume (2)-(4) are true.
**      then R = R_0 \cup 2A is irred non-red
**      and R_0 is the set of indivisible roots of R.
**
**    summarising:
**      by (4) R_0 can only have type B_l (and R type BC_l)
**      by (6) the Weyl-grps and Cartan-mats of R and R_0 are the same
**      same dynkin diagram, but has the star on the simple roots,
**      whose double is a root
**
**    NOTES ON THE IMPLEMENTATION:
**      we store the Type attribute, which can now also contain tuples <"BC",[i1,...,in]>
**      which indicates in as _the_ short simple root (as in type "B") and at the same time
**      _the_ simple root, whose double is a root again.
**      No additional information is stored in the root datum.
**      
**      The Constructors, which take matrices or diagrams, accept optional parameter
**      Nonreduced, which is a set of simple roots, whose doubles are roots again.
**      e.g. if C is a Cartan Matrix of Type B5 x B6, this optional parameter could
**      be one of {}, {5}, {11}, {5,11} for the respective types of the Root Datum:
**      B5 x B6, BC5 x B6, B5 x BC6, BC5 x BC6
**
**
**
*/

intrinsic IsReduced( R::RootStr ) -> BoolElt
{True iff R is reduced. If true}
    return forall{t:t in toType(R)|t[1] ne "BC"};
end intrinsic;

// simple roots whose doubles are roots again.
nonredSimpleRoots := function(R)
    return { t[2][#t[2]] : t in toType(R) | t[1] eq "BC" };
end function;

intrinsic IndivisibleSubdatum( R::RootDtm ) -> RootDtm
{Indivisible subdatum of R}
    return RootDatum(R`SimpleRoots, R`SimpleCoroots);
end intrinsic;
intrinsic IndivisibleSubsystem( R::RootSys ) -> RootSys
{Indivisible subsystem of R}
    return RootSystem(R`SimpleRoots, R`SimpleCoroots);
end intrinsic;




// ====================================================
//
// The graveyard
//
// Old code/documentation that may be useful in the future
//

// this was dropped from SVN rev. 3465 to rev. 3466

