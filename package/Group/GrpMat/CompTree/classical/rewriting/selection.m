freeze;

/* 
  Method selection.
*/
  
import "charp.m":ClearFirstRowCharP, 
                 EntriesOfRootElementCharP, 
                 WriteSimpleRootElementAsSLPCharP;

import "sl.m":ClearFirstRowSLBB, 
              EntriesOfRootElementBBSL, 
              ClearFirstColumnSLBB, 
              WriteSimpleRootElementAsSLPBBSL;

import "spsu.m":ClearFirstRowSpSUBB, 
                EntriesOfRootElementBBSpSU, 
                WriteSimpleRootElementAsSLPBBSpSU;

import "su34.m":ClearFirstRowSUBBDim3, ClearFirstRowSUBBDim4;

import "omegabb.m":ClearFirstRowOmegaBB, 
EntriesOfRootElementOmegaBB, WriteSimpleRootElementAsSLPOmegaBB;

import "bbclassical.m":BBType, BBDimension;

ClearFirstRow := function( G, g : 
                         FirstCall := false, 
                         Method := "BB",
                         Transpose := false )

    type := BBType( G );
    dim := BBDimension( G );
    
    if Method eq "CharP" then
        return ClearFirstRowCharP( G, g : FirstCall := FirstCall, 
                       Transpose := Transpose );
    elif Method eq "BB" and type eq "SL" and not Transpose then
        return ClearFirstRowSLBB( G, g : FirstCall := FirstCall );
    elif Method eq "BB" and type eq "SL" and Transpose then
        return ClearFirstColumnSLBB( G, g );
    elif Method eq "BB" and type eq "SU" and dim eq 4 then
        return ClearFirstRowSUBBDim4( G, g : FirstCall := FirstCall );
    elif Method eq "BB" and type eq "SU" and dim eq 3 then
        return ClearFirstRowSUBBDim3( G, g : FirstCall := FirstCall );
    elif Method eq "BB" and type in { "Sp", "SU" } then
        return ClearFirstRowSpSUBB( G, g : FirstCall := FirstCall );
    elif Method eq "BB" and type in { "Omega+", "Omega", "Omega-" } then
        return ClearFirstRowOmegaBB( G, g : FirstCall := FirstCall );
    end if;
    
end function;
    
EntriesOfRootElement := function( G, g : Method := "BB", 
				    GetWE1Entry := false )
    
    type := BBType( G );
    
    if Method eq "CharP" then
        return EntriesOfRootElementCharP( G, g );
    elif Method eq "BB" and type eq "SL" then
        return EntriesOfRootElementBBSL( G, g );
    elif Method eq "BB" and type in { "Sp", "SU" } then
        return EntriesOfRootElementBBSpSU( G, g : 
		       GetWE1Entry := GetWE1Entry );
    elif Method eq "BB" and type in { "Omega+", "Omega", "Omega-" } then
        return EntriesOfRootElementOmegaBB( G, g );
    end if;
    
end function;
      
WriteSimpleRootElementAsSLP := function( G, g, n : Method := "BB" )
    
    type := BBType( G );
    
    if Method eq "CharP" then
        return WriteSimpleRootElementAsSLPCharP( G, g, n );
    elif Method eq "BB" and type eq "SL" then
        return WriteSimpleRootElementAsSLPBBSL( G, g, n );
    elif Method eq "BB" and type in { "Sp", "SU" } then
        return WriteSimpleRootElementAsSLPBBSpSU( G, g, n );
    elif Method eq "BB" and type in { "Omega+", "Omega", "Omega-" } then
        return WriteSimpleRootElementAsSLPOmegaBB( G, g, n );
    end if;
    
end function;
