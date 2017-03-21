freeze;

/******************************************************************************
 *
 * localdata.m
 *
 * date:   08/01/2003
 * author: Nils Bruin
 *
 * Stores data in a structure, indexed by prime ideals.
 * Anyone interested can add fields to the recformat StrLocalRecFormat below.
 *
 * In order to not interfere with other clients of this structure, adhere to
 * the following call sequence:
 *
 * r:=GetLocalData(S,p);
 * r`fieldname:=value;
 * StoreLocalData(S,p,r);
 *
 * To use,
 *
 *import "localdata.m":GetLocalData,StoreLocalData;
 ******************************************************************************/
 
declare attributes Str:StrLocalData;

StrLocalDataRecFormat:=recformat<
    
    //for isogenies (2 and mult-by-2) of elliptic curves
    xlist,twotor,twotorimg,
    
    //for mwmaps (maps from abelian group to an elliptic curve)
    reduction,
    
    //for absolute algebras
    TwoSelmerMap,TwoSelmerMapComponents
    >;

function GetLocalData(S,p)
//  {Retrieve information stored on a structure, indexed by a prime ideal}
  if not(assigned(S`StrLocalData)) then
    S`StrLocalData:=[];
  end if;
  if exists(t){u[2]: u in S`StrLocalData | u[1] eq p} then
    return t;
  else
    return rec<StrLocalDataRecFormat|xlist:=[]>;
  end if;
end function;

procedure StoreLocalData(S, p, data) // (S::Str,p::RngOrdIdl,data::Rec)
//  {Store information on a structure, indexed by a prime ideal}
  if not(assigned(S`StrLocalData)) then
    S`StrLocalData:=[];
  end if;
  if exists(j){i:i in [1..#S`StrLocalData] | S`StrLocalData[i][1] eq p} then
    S`StrLocalData[j]:=<p,data>;
  else
    Append(~S`StrLocalData,<p,data>);
  end if;
end procedure;
