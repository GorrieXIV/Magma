freeze;

/////////////////////////////////////////////////////////////////////////
// grdb.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 49982 $
// $Date: 2015-03-08 22:38:01 +1100 (Sun, 08 Mar 2015) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Utility functions for accessing the online Graded Ring Database.
/////////////////////////////////////////////////////////////////////////
// The Graded Ring Database can be viewed online at:
//  http://www.grdb.co.uk/
// You can specify an alternative address for the GRDB server via the
// environment variable "GRDB_SOURCE".
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the address of the GRDB server; e.g.
//  http://www.grdb.co.uk/
function GRDB_root()
    try
        addr:=GetEnv("GRDB_SOURCE");
    catch e
        addr:="";
    end try;
    if #addr eq 0 then
        addr:="http://www.grdb.co.uk/";
    else
        // We need to tidy up the string -- it might be sloppily presented
        addr:=Trim(addr);
        if #addr le 4 or addr[1..4] ne "http" then
            addr:="http://" cat addr;
        end if;
        if addr[#addr] ne "/" then
            addr cat:= "/";
        end if;
    end if;
    return addr;
end function;

// Returns the address of the GRDB's search.xml page; e.g.
//  http://www.grdb.co.uk/xml/search.xml?agent=magma&dataid=toricf3t&
function GRDB_xml_root( dataid : agent:="grdb", printlevel:=false )
    error if Type(dataid) ne MonStgElt,
        "GRDB_xml_root: The dataid must be a string";
    if Type(printlevel) ne BoolElt or printlevel then
        error if Type(printlevel) ne RngIntElt or printlevel lt 1,
            "GRDB_xml_root: The printlevel must be a positive integer";
    end if;
    error if Type(agent) ne MonStgElt,
        "GRDB_xml_root: The agent must be a string";
    url := GRDB_root() cat "xml/search.xml?agent=" cat agent cat "&";
    if Type(printlevel) eq RngIntElt then
        url cat:= "printlevel=" cat IntegerToString(printlevel) cat "&";
    end if;
    return url cat "dataid=" cat dataid cat "&";
end function;

// Returns the base address of the GRDB's search results page; e.g.
//  http://www.grdb.co.uk/search/toricf3t?printlevel=2&
function GRDB_search_root( dataid : printlevel:=false )
    error if Type(dataid) ne MonStgElt,
        "GRDB_search_root: The dataid must be a string";
    if Type(printlevel) ne BoolElt or printlevel then
        error if Type(printlevel) ne RngIntElt or printlevel lt 1,
            "GRDB_search_root: The printlevel must be a positive integer";
    end if;
    url := GRDB_root() cat "search/" cat dataid cat "?";
    if Type(printlevel) eq RngIntElt then
        url cat:= "printlevel=" cat IntegerToString(printlevel) cat "&";
    end if;
    return url;
end function;
