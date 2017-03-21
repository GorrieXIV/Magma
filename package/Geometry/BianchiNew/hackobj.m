freeze;

import "setlevel.m":
    SetLevel;
import "sharbly.m":
    SetSharblies;
import "cohomology.m":
    homologydata;
import "setup.m":
    Preset;
import "defs.m":
    ModFrmDataRec,
    LevelRec;
import "compute.m":
    FindCells;

/**********************************************************************
*                                                                     *
*                   BIANCHI MODULAR FORMS                             *
*                                                                     *
*     Definition of new attributes on ModFrmBianchi           	      *
*                                                                     *
*                    Dan Yasaki May 2009                              *
*                                                                     *
***********************************************************************/


/**********************************************************************
  ModFrmBianchi attributes  ...  
  Let M be a ModFrmBianchi over the FldNum F    
**********************************************************************/

declare type ModFrmBianchi [ModFrmBianchiElt]: ModFrmHil;

declare attributes ModFrmBianchi:
    Full_Dimension,//Dimension of H_0(S_*(Gamma0))
    //Hecke matrices for cusp space used to compute T_p for
    //non-principal primes in class number 3. Should not get used often
    Hecke_ap,//T_a,a,T_p from Cremona, restricted to cuspidal space
    ModFrmData, //Should eventually get organized.
    LevelData, //Should eventually get organized.
    is_Bianchi,//set true for Bianchi modular forms
    homology_coefficients,//Coefficients for homology computations.
	//Should be a field.  Don't know the interpretation when this is not.
    Hecke_pp, //Hecke matrices for Tp,p action
bmap, // tmp
red_cache
;

/*****************   Constructors for Bianchi spaces   *********************/



function BMF(F, N ,G,V, Coefficients)

    // check cache
    if assigned F`ModFrmHils then
        bool, cache := IsDefined(F`ModFrmHils, N);
        if bool then
            assert #cache eq 1;
            return cache[1];
        end if;
    end if;

    M := New(ModFrmBianchi);
    M`is_Bianchi := true;
    M`Field := F;
    M`Level := N;
    M`NewLevel := 1*Integers(F);
    M`DirichletCharacter := 1;
    M`Weight := [2];
    M`CentralCharacter := 0;
    M`is_cuspidal := true; // always true, currently
    M`homology_coefficients:=Coefficients;
    M`Hecke    := AssociativeArray();
    M`Hecke_pp := AssociativeArray();
    M`Hecke_ap := AssociativeArray();
    M`HeckeCharPoly := AssociativeArray();
    M`ModFrmData:=V;
    M`LevelData:=rec<LevelRec|>;

    M`red_cache := AssociativeArray();

    // If we precompute Voronoi at one level, we should be
    // able to save some data and avoid recomputing when we change level.

    Preset(M);
    
    if not assigned M`ModFrmData`standardorder then 
        FindCells(M);
        SetSharblies(M);
    end if;
    
    // cache on F
    if assigned F`ModFrmHils then
        assert not IsDefined(F`ModFrmHils, N);
        F`ModFrmHils[N] := [* M *];
    end if;

    return M;
end function;

intrinsic BianchiCuspForms(F::FldNum, N::RngOrdIdl:
    Coefficients:=RationalField(),G:="GL",VorData:=rec<ModFrmDataRec|G:=G,ideal_reps:=[]>)
    -> ModFrmBianchi 
    {The space of Bianchi modular forms over the imaginary quadratic field F
    with level N and weight 2.  Here N should be an ideal in the 
    maximal order of F.}
    
    require BaseField(F) eq Rationals() and Degree(F) eq 2 and Discriminant(F) lt 0 :
	"The base field F must be an imaginary quadratic extension of the rationals";
    require NumberField(Order(N)) eq F :
	"The level N must be an ideal in the base field";
    return BMF(F, N,G,VorData,Coefficients);
end intrinsic;

function DimensionBianchi(M)
    vprint Bianchi,1:"Computing dimension of the cuspidal space.";
     if not assigned M`Dimension then 
	homologydata(M);
    end if;
    return M`Dimension; 
end function;

intrinsic VoronoiData(M::ModFrmBianchi) -> Rec
    {Returns the Voronoi data for BaseField(M)}
    return M`ModFrmData;
end intrinsic;

intrinsic HomologyData(M::ModFrmBianchi) -> Rec
    {Returns the Homology data for BaseField(M)}
    d := DimensionBianchi(M);
    return M`LevelData`homology;
end intrinsic;

