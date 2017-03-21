freeze;

/////////////////////////////////////////////////////////////////////////
// dim3_smooth.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38043 $
// $Date: 2012-04-01 01:05:07 +1100 (Sun, 01 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Reverse look-up tables for obtaining the database ID of a
// three-dimensional smooth polytope.
/////////////////////////////////////////////////////////////////////////

// Assuming P is a smooth Fano 3-tope, returns true followed by the
// corresponding ID in the database. May also return false followed by an error
// message.
function smooth_dim3_to_id(P)
    v:=Volume(P);
    if v eq 4 then
        return true,18;
    elif v eq 6 then
        d:=Volume(Dual(P));
        if d eq 54 then
            if IsIntegral(&+Vertices(P) / NumberOfVertices(P)) then
                return true,17;
            else
                return true,14;
            end if;
        elif d eq 56 then
            return true,15;
        elif d eq 62 then
            return true,2;
        end if;
    elif v eq 8 then
        d:=Volume(Dual(P));
        if d eq 44 then
            return true,13;
        elif d eq 46 then
            return true,11;
        elif d eq 48 then
            if IsIntegral(&+Vertices(P) / NumberOfVertices(P)) then
                return true,16;
            else
                return true,12;
            end if;
        elif d eq 50 then
            nf:=NormalForm(P);
            pt:=Eltseq(nf[6]);
            if pt[3] eq 0 then
                return true,1;
            elif pt[3] eq -1 then
                return true,7;
            end if;
        elif d eq 52 then
            return true,6;
        end if;
    elif v eq 10 then
        d:=Volume(Dual(P));
        if d eq 40 then
            return true,8;
        elif d eq 42 then
            return true,9;
        elif d eq 44 then
            return true,5;
        elif d eq 46 then
            return true,3;
        end if;
    elif v eq 12 then
        if IsIntegral(&+Vertices(P) / NumberOfVertices(P)) then
            return true,10;
        else
            return true,4;
        end if;
    end if;
    // We shouldn't be here
    return false,"Argument must be a smooth Fano 3-tope";
end function;

// Given the id of a smooth Fano 3-tope,returns a sequence [<db_name,id>] of
// the other database ids.
function smooth_dim3_id_to_ids(id)
    // Sanity check
    error if id le 0 or id gt 18,
        "Invalid database id (should be in the range 1..18)";
    // Recover the ids
    case id:
        when 1:
            ids:=[27,136,520127];
        when 2:
            ids:=[8,35,544387];
        when 3:
            ids:=[84,218,430516];
        when 4:
            ids:=[220,369,255778];
        when 5:
            ids:=[83,275,430513];
        when 6:
            ids:=[28,105,520139];
        when 7:
            ids:=[29,131,520136];
        when 8:
            ids:=[82,271,430515];
        when 9:
            ids:=[85,266,430514];
        when 10:
            ids:=[219,324,255779];
        when 11:
            ids:=[26,139,520137];
        when 12:
            ids:=[30,123,520138];
        when 13:
            ids:=[25,68,520135];
        when 14:
            ids:=[7,37,544390];
        when 15:
            ids:=[6,36,544391];
        when 16:
            ids:=[31,62,520140];
        when 17:
            ids:=[5,24,544392];
        when 18:
            ids:=[1,4,547386];
    end case;
    // Return the sequence of ids
    return [<"smooth3",id>, <"reflexive3",ids[1]>, <"terminal3",ids[2]>,
            <"canonical3",ids[3]>];
end function;
