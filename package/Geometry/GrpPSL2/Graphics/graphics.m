freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//    Graphics for fundamental domains
//    Helena Verrill, May 2001                                    //
//                                                                // 
////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////
//                                                   //
//    basic postscript writing commands              //
//    for starting and ending files                  //
//                                                   //
///////////////////////////////////////////////////////

forward topmatter;
forward endmatter;

function startPsfile(filename,translation,width,height,overwrite,fontsize)
   if not overwrite then
      file:=Open(filename,"a");
      s := Read(filename);
      if #s gt 0 then
	 read reply, Sprintf("The file %o already exist.  Are you sure you want to overwrite it?  (Enter yes if you do, anything otherwise.)",filename);
         if reply eq "yes" or reply eq "Yes" or reply eq "YES" then
	    file:=Open(filename,"w");
	    fprintf file,topmatter(translation,width,height+fontsize,fontsize);
	    return true;
	 else
	    return false;
	 end if;      
      else
	 file:=Open(filename,"w");
	 fprintf file,topmatter(translation,width,height+fontsize,fontsize);
	 return true;
      end if;
   else
      file:=Open(filename,"w");
      fprintf file,topmatter(translation,width,height+fontsize,fontsize);
      return true;
   end if;
end function;


procedure endPsfile(filename)
     Write(filename,endmatter());
end procedure;

procedure showpsfile(filename)
    string:="gv " cat filename cat " &";
    System(string);
end procedure;

function topmatter(translation,width,height,fontsize)
    // this function returns material needed at the
    // beginning of the postscript file
    // translation determines where the origin (0,0)
    // appears in the page
    translation:=0;
    border := 20;
    percent := "%%";
    outputstring:="%%!PS-Adobe-3.0 EPSF-3.0\n"
    cat percent
    cat percent
    cat Sprintf("BoundingBox: 0 0 %o %o\n",width+2*border,height+border
    + 5*fontsize)
    cat percent
    cat percent
    cat Sprintf("HiResBoundingBox: 0 0 %o %o
    
    0.2 setlinewidth\n",width+2*border,height+border+5*fontsize)
    cat Sprintf("%o %o translate",border,border+5*fontsize)
    // note, for more acuracy, a better translation would be
    // required as a function of the fontsize, which might be
    // non linear
    cat Sprintf("
    4 4 scale
    
    newpath %o 0 moveto %o 0 lineto stroke\n\n",
    -Floor(border*0.25)-translation,Floor((width + border)*0.25) -translation)
    cat Sprintf("%o 0 translate\n",-translation);
    return outputstring;
end function;


function endmatter()
    // this function returns material needed at the
    // end of the postscript file
    return "\n showpage";
end function;


///////////////////////////////////////////////////////
//                                                   //
//    functions for drawing individual               //
//         lines and polygons                        //
//                                                   //
///////////////////////////////////////////////////////


function DrawEdgeBetween(a,b,scale,translation,topOfScreen)
    // this function will take elements a,b of UpperHalfplaneunioncusps
    // and give the postscript for the line between them.
    // note that start and end functions for a whole path will
    // be needed to draw something.    
    MAX_ALLOWED := 10000;
    too_big := false;
    //    scale:=150;
    oldR := GetDefaultRealField();
    SetDefaultRealField(RealField(10));
    H := UpperHalfPlaneWithCusps();
    R := RealField();
    if a eq b then
	return "";
    end if;
    inf := H!Infinity();
    if a eq inf then
	XVAL := Real(b)*scale-translation;
	if XVAL gt MAX_ALLOWED then return ""; end if;
	outputstring :=
	Sprintf("%o %o lineto %o %o lineto\n",
	XVAL,topOfScreen,
	XVAL,Imaginary(b)*scale);
	return outputstring;
    end if;
    if b eq inf then
	XVAL := Real(a)*scale-translation;
	if XVAL gt MAX_ALLOWED then return ""; end if;
	outputstring :=
	Sprintf("%o %o lineto %o %o lineto\n",
	XVAL,Imaginary(a)*scale,
	XVAL,topOfScreen);
	return outputstring;
    end if;
    if Abs((Real(b) - Real(a))*scale) lt 0.001 then
	XVAL := Real(a)*scale-translation;
	if XVAL gt MAX_ALLOWED then return ""; end if;
	outputstring :=
	Sprintf("%o %o lineto %o %o lineto\n",
	XVAL,Imaginary(a)*scale,
	XVAL,Imaginary(b)*scale);
	return outputstring;
    end if;
    if IsCusp(a) and IsCusp(b) then	
	A := R!Real(a)*scale;
	B := R!Real(b)*scale;
	if Real(b) gt Real(a) then
	    XVAL := (A+B)/2-translation;
	    if XVAL gt MAX_ALLOWED then return ""; end if;
	    outputstring:=Sprintf("%o 0 %o 180 0 arcn\n",
	    XVAL,(B-A)/2);
	else
	    XVAL := (A+B)/2-translation;
	    if XVAL gt MAX_ALLOWED then return ""; end if;
	    outputstring:=Sprintf("%o 0 %o 180 0 arc\n",
	    XVAL,(B-A)/2);
	end if;
	return outputstring;
    end if;
    x := Real(a);
    y := Imaginary(a);
    u := Real(b);
    v := Imaginary(b);
    c := (v^2 + u^2 - x^2 - y^2)/(u-x)/2;
    r := SquareRoot((x-c)^2 + y^2);
    dist1 := x - c;
    dist2 := u - c;
    PI:=Pi(R);
    cos1 := dist1/r;  cos2 := dist2/r;
    // make sure these values are in the domain of Arccos
    if Abs(cos1) gt 1 then cos1 := Round(cos1); end if;
    if Abs(cos2) gt 1 then cos2 := Round(cos2); end if;
    ang1 := Real((Arccos(cos1))*180/PI); // mod 180;
    ang2 := Real((Arccos(cos2))*180/PI); // mod 180;
    if ang1 gt ang2 then
	XVAL := c*scale-translation;
	if XVAL gt MAX_ALLOWED then return ""; end if;
	outputstring:=Sprintf("%o 0 %o %o %o	
	arcn\n",XVAL,r*scale,ang1,ang2);
    else
	XVAL := c*scale-translation;
	if XVAL gt MAX_ALLOWED then return ""; end if;
	outputstring:=Sprintf("%o 0 %o %o %o
	arc\n",XVAL,r*scale,ang1,ang2);
    end if;
    SetDefaultRealField(oldR);
    return outputstring;
end function;


function DrawEdge(E,scale,topOfScreen,translation)
    // E should consist of just two elements of SpcHyp
    
    string1 := Sprintf("%o %o %o setrgbcolor\n",0,0,0);
    x := scale*Real(E[1]) - translation;
    y := scale*Imaginary(E[1]);
    if y eq Infinity() then y := topOfScreen; end if;
    string2 := Sprintf("newpath\n %o %o moveto\n",x,y);
    string3 := DrawEdgeBetween(E[1],E[2],scale,translation,topOfScreen);
    if string3 eq "" then return ""; end if;
    string4 := "stroke\n\n";
    outputstring := string1 cat string2 cat string3 cat string4;
    return outputstring;
end function;
    

function DrawPolygon(S,colour,pencolour,
   scale,outline,fill,translation,topOfScreen,
   Radius)
    // S is a sequence of elements of Upperhalfplaneunioncusps
    // colour is a triple of numbers between 0 and 1.
    // try scale around 100 - it's the number of pixels per unit
    // try top of screen about 400 - or as large as you want.
    
    //   topOfScreen := 400;
    //    scale:=150;
    MAX_ALLOWED := 10000;
    if Type(S) ne SeqEnum or  #S eq 0 then
	return "";
     end if;
     c1,c2,c3 := Explode(colour);
     pc1,pc2,pc3 := Explode(pencolour);
    //    printf "%o %o\n",Parent(S),Parent([S[1]]);
    elt_of_S := func<i | i le #S select S[i] else S[1]>;
    S1 := [Parent(S[1])|elt_of_S(i) : i in [1..(#S+1)]];   
    //       S1 := S cat [S[1]];
    if #S eq 1 and (not (IsCusp(S[1]) and
       (Type(ExactValue(S[1])) eq SetCspElt and ExactValue(S[1])
       eq Cusps()!Infinity()))) then
       x := scale*Real(S[1]) - translation;
       y := scale*Imaginary(S[1]);
       startString := Sprintf("%o %o %o setrgbcolor\n",c1,c2,c3);
       polystring :=
       Sprintf("newpath  \n %o %o %o 0 360 arc fill\n\n",x,y,Radius);
       return startString cat polystring;
    end if;
       
    
    startStringA := Sprintf("%o %o %o setrgbcolor\n",c1,c2,c3);
    startStringB := Sprintf("%o %o %o setrgbcolor\n",pc1,pc2,pc3);
    if not
       (IsCusp(S[1]) and Type(ExactValue(S[1])) eq SetCspElt and
       ExactValue(S[1]) eq Cusps()!Infinity())
       then
       x := scale*Real(S[1]) - translation;
       y := scale*Imaginary(S[1]);
    else
       y := topOfScreen;
       x:=0 - translation;
    end if;    
    polystring := Sprintf("newpath\n %o %o moveto\n",x,y);
    if x gt MAX_ALLOWED then return ""; end if;
    for i in [2..#S1] do
	newedge := DrawEdgeBetween(S1[i-1],S1[i],scale,translation,topOfScreen);
	// give up on the polygon if it's not in drawable area.
	// this gives a bug ! need to fix!
	//	if newedge eq "" then return ""; end if;
	polystring := polystring cat newedge;
    end for;
    endstringA := "fill\n\n";
    endstringB := "stroke\n\n";
    if outline and fill then
       outputstring := startStringA cat polystring cat endstringA
       cat startStringB cat polystring cat endstringB;
    elif fill then
       outputstring := startStringA cat polystring cat endstringA;
    else
       outputstring := startStringB cat polystring cat endstringB;
    end if;
    return outputstring;
end function;

forward AutoHeight;
forward AutoWidth;
forward AutoScale;
forward labeling;


intrinsic DisplayPolygons(P::SeqEnum,filename::MonStgElt:
    Colours := [1,1,0],
    PenColours := [0,0,0],
    Outline := [true : p in P],
    Fill := [true : p in P],
    Fontsize := 2,
    Labels := [Rationals()|0,1],
    Radius := 0.5,
    Pixels := 300,
    Size := [],
    Show := false,
    Overwrite := true) -> SeqEnum
    {Create/display a postscript drawing of the polygon with given vertices}

    // P is a sequence of sequences, each representing a polygon
    // colour is a list of triples of numbers between 0 and 1.
    // filename is some string where the file should be written
    // Show is a boolean; if it's true pop up the ps file with
    // a system command.
    //
    require Type(Labels) cmpeq SeqEnum:
    "Labels must be a sequence of rationals or cusps";
    require (#Labels eq 0 or Parent(Labels[1]) cmpeq Rationals()
    or Parent(Labels[1]) cmpeq Integers()
    or Parent(Labels[1]) cmpeq Cusps()
    or Type(Labels[1]) cmpeq SpcHypElt):
    "Labels must be a sequence of rationals or cusps";    
    if  #Labels gt 0 and Parent(Labels[1]) cmpeq Integers() then
       Labels := [Rationals()|x : x in Labels];
    end if;

    // for hyperbolic space elements, only add labels if they are
    // cusps
    if  #Labels gt 0 and Type(Labels[1]) cmpeq SpcHypElt then
       Labels := [Cusps()|ExactValue(x) : x in Labels | IsCusp(x)];
    end if;

    require Parent(Pixels) cmpeq Integers(): "Pixels should be an integer";
    if Pixels lt 10 then
       Pixels := 10;
    end if;
    
    if not ((Type(Size) eq SeqEnum and #Size eq 4 and Type(Universe(Size)) in {RngInt, FldRe, FldRat}))     then
       Autoscale := true;
    else
       if (Type(Universe(Size)) ne FldRe) then
	  Size := [RealField() | x : x in Size];
       end if;
       Autoscale := false;
    end if;
       
    require #P gt 0: "Please give a list of polygons";    
    require Type(P[1]) in {SeqEnum, SpcHypElt, SetCspElt}:
    "Please give a list of polygons";
    require Type(P[1]) in {SpcHypElt, SetCspElt}
    or Type(P[1][1]) in {SpcHypElt, SetCspElt}:
    "Please give a list of polygons";
    if Type(P[1]) in {SpcHypElt, SetCspElt} then
       P := [P];
    end if;    
    if Type(P[1][1]) eq SetCspElt then
       H := UpperHalfPlaneWithCusps();
       P := [[H|x : x in p] : p in P];
    end if;
    
    // note requirements for Colours must come after requirements for P
    require Type(Colours) eq SeqEnum and #Colours gt 0:
    "Colours must be a sequence of sequences of numbers";
    require Type(Colours[1]) in {SeqEnum,RngIntElt,FldRatElt,FldReElt}:
    "Colours must be a sequence of sequences of numbers";
    require (Type(Colours[1]) in {RngIntElt,FldRatElt,FldReElt}) or
    (Type(Colours[1][1]) in {RngIntElt,FldRatElt,FldReElt}):
    "Colours must be a sequence of sequences of 3 numbers";
    require ((Type(Colours[1]) in {RngIntElt,FldRatElt,FldReElt})
    and #Colours ge 3)
    or (Min([#Colours[i] : i in [1..#Colours]]) ge 3):
    "Colours must be a sequence of sequences of 3 integers";
    if Type(Colours[1]) in {RngIntElt,FldRatElt,FldReElt} then
       Colours := [[Colours[i] : i in [1..3]]];
    end if;
    if #Colours lt #P then       
       Colours := Colours cat [Colours[1] : i in [(#Colours+1)..#P]];
    end if;
    if Type(Colours[1][1]) eq FldRatElt then
       Colours := [[RealField() | 1.0*i : i in c] : c in Colours];
    end if;


    // note requirements for PenColours must come after requirements for P
    require Type(PenColours) eq SeqEnum and #PenColours gt 0:
    "PenColours must be a sequence of sequences of numbers";
    require Type(PenColours[1]) in {SeqEnum,RngIntElt,FldRatElt,FldReElt}:
    "PenColours must be a sequence of sequences of numbers";
    require (Type(PenColours[1]) in {RngIntElt,FldRatElt,FldReElt}) or
    (Type(PenColours[1][1]) in {RngIntElt,FldRatElt,FldReElt}):
    "PenColours must be a sequence of sequences of 3 numbers";
    require ((Type(PenColours[1]) in {RngIntElt,FldRatElt,FldReElt})
    and #PenColours ge 3)
    or (Min([#PenColours[i] : i in [1..#PenColours]]) ge 3):
    "PenColours must be a sequence of sequences of 3 integers";
    if Type(PenColours[1]) in {RngIntElt,FldRatElt,FldReElt} then
       PenColours := [[PenColours[i] : i in [1..3]]];
    end if;
    if #PenColours lt #P then       
       PenColours := PenColours cat [PenColours[1] : i in [(#PenColours+1)..#P]];
    end if;
    if Type(PenColours[1][1]) eq FldRatElt then
       PenColours := [[RealField() | 1.0*i : i in c] : c in PenColours];
    end if;

    
       
    require (Type(Outline) eq BoolElt)
    or (Type(Outline) eq SeqEnum and #Outline gt 0):
    "Outline must be a boolean or sequence of booleans";
    require (Type(Outline) eq BoolElt) or
    (#Outline gt 0 and Type(Outline[1]) eq BoolElt):
    "Outline must be a boolean or sequence of booleans";
    if Type(Outline) eq BoolElt then
       Outline := [Outline];
    end if;
    if #Outline lt #P then
       Outline := Outline cat [Outline[1] : i in [(#Outline+1)..#P]];
    end if;

    
    require Type(Fill) in {SeqEnum,BoolElt} and
    (Type(Fill) eq BoolElt or #Fill gt 0):
    "Fill must be a boolean or sequence of booleans";
    require (Type(Fill) eq BoolElt) or
    (#Fill gt 0 and Type(Fill[1]) eq BoolElt):
    "Fill must be a boolean or sequence of booleans";
    if Type(Fill) eq BoolElt then
       Fill := [Fill];
    end if;
    if #Fill lt #P then       
       Fill := Fill cat [Fill[1] : i in [(#Fill+1)..#P]];
    end if;

    require Parent(Fontsize) cmpeq Integers(): "Fontsize should be an integer";
    require Type(Show) cmpeq BoolElt: "Show must be a boolean";
    require Type(Autoscale) cmpeq BoolElt: "Autoscale must be a boolean";

    TOO_BIG := false;
    // note scale in ps file, currently 4 4 scale, above, thus the following:
    scale4 := 4;    

    if  Autoscale then
       h := AutoHeight(P);    
       w1,w2 := AutoWidth(P);
       S := AutoScale(Pixels,h,w1,w2);           
       // following needs improving!
       // the points is that currently the height is computed
       // so that all vertices of a polygon are included in a
       // displayed area, but if the vertices are all cusps in
       // the real line, then they all have 0 hight, so one
       // should compute the maximum points on the lines between
       // the instead, but so far, this is not done, and we
       // just take a hight 0.5.
       if h eq 0 then h:=0.5; end if; 
    else
       w1 := Size[1];
       w2 := Size[2];
       h := Size[3];
       S := Size[4];
    end if;

    translation := Integers()!Ceiling(S*w1/scale4);
    w := w2 - w1;
    if Abs(w*S) lt 0.001
       then width:=0.5;
    elif Abs(w*S) gt 10000 then
       width:=10000;      
    else
       width := Min(Integers()!Ceiling(w*S),10000);
    end if;
    height := Min(Integers()!Ceiling(h*S),10000);
    topOfScreen := height;

    writable := startPsfile(filename,translation,width,height,
    Overwrite,Fontsize);
    if writable then

       oldR := GetDefaultRealField();
       SetDefaultRealField(RealField(10));
       for i in [1..#P] do
	  polystring := DrawPolygon(P[i],Colours[i],PenColours[i],1.0*(S/4),
	  Outline[i],Fill[i],translation,topOfScreen,Radius);
	  if #P[i] gt 0 and polystring eq "" then
	     TOO_BIG := true;
	  end if;
	  Write(filename,polystring);
       end for;
       if #Labels gt 0 then
	  Write(filename,labeling(Labels,1.0*(S/4),Fontsize,translation));
       end if;
       endPsfile(filename);
       if Show then
	  showpsfile(filename);
       end if;
       if TOO_BIG then
	  printf "Some polygons have not been drawn, due to size
	  limitations";
       end if;
       SetDefaultRealField(oldR);
    else
       printf "No file created.\n";
    end if;
    return [w1,w2,h,S];
end intrinsic;

function frac(a)
   return a[1]/a[2];
end function;

function gluinglabel(a,b,l,scale,fontsize,translation)
   // a and b are rationals, l is the label
   outputstring := "";
   endstring := "";
   shift := 0.1*fontsize;
   if scale*(b-a) lt fontsize then  
      newfont := (scale*(b-a));
      shift := 0.5*newfont;
//      print [scale*(b-a),100*fontsize,newfont];
      outputstring := Sprintf(
      "/Times-Roman findfont %o scalefont setfont\n",newfont);
      endstring := Sprintf(
      "/Times-Roman findfont %o scalefont setfont\n",fontsize);      
   end if;
   n := (a+b)/2;
   if l ne -3 then
      Xpos := scale*n-0.5*fontsize  - translation;
      Ypos := scale*(b-a)/2;
   else
      P := PSL2(Integers());
      H := UpperHalfPlaneWithCusps();
      x := [Numerator(a),Denominator(a)];
      y := [Numerator(b),Denominator(b)];
      E := (P![y[1],x[1],y[2],x[2]])*H.2;
      Xpos := scale*Real(E)-0.5*fontsize  - translation;
      Ypos := scale*Imaginary(E) + 0.5;
   end if;
   return 
   outputstring cat
   Sprintf("%o %o moveto (%o) show\n",Xpos+shift,Ypos+0.3,l)
   cat endstring;
end function;

function endlabels(shift,a,l,scale,fontsize,height,translation)
   if l ne -3 then
      Xpos := scale*a + shift  - translation;
      Ypos := scale*0.3;
      return Sprintf("%o %o moveto (%o) show\n",Xpos,Ypos+0.3,l);
   end if;
   Xpos := scale*a + 2*shift - scale*0.5*Sign(shift) - translation;
   Ypos := scale*0.9;
   return Sprintf("%o %o moveto (%o) show\n",Xpos,Ypos+0.3,l);
end function;

function allGlueLabels(labels,cusps,scale,fontsize,height,translation)
   outputstring:= Sprintf("
   0 0 0 setrgbcolor
   0 setlinewidth 
   /Times-Roman findfont 
   %o scalefont setfont\n",fontsize);
   numbers := cusps;
   if Type(Universe(numbers)) eq SetCsp then
      inf := Cusps()!Infinity();
      numbers := [frac(Eltseq(a)) : a in numbers | a ne inf]; 
   end if;
   for i in [1..#numbers-1] do
      a := numbers[i];
      b := numbers[i+1];
      l := labels[i+1];
      outputstring := outputstring cat gluinglabel(a,b,l,scale,fontsize,
      translation);
   end for;
   outputstring := outputstring cat
   endlabels(0.5,numbers[1],labels[1],scale,fontsize,height,translation);
   outputstring := outputstring cat
   endlabels(-2,numbers[#numbers],labels[#labels],scale,fontsize,
   height,translation);
   return outputstring;
end function;

// function for adding lables to picture:
function labeling(numbers,scale,fontscale,translation)
   if Type(Universe(numbers)) eq SetCsp then
      inf := Cusps()!Infinity();
      numbers := [frac(Eltseq(a)) : a in numbers | a ne inf]; 
   end if;
   outputstring:= Sprintf("
   0 0 0 setrgbcolor
   0 setlinewidth 
   /Times-Roman findfont 
   %o scalefont setfont\n",fontscale);	 
   for n in numbers do
      num := Sprintf("%o",Numerator(n));
      dem := Sprintf("%o",Denominator(n));
      if dem eq "1" then
	 pos := scale*n-0.2  - translation;
	 outputstring:= outputstring cat Sprintf("
	 0 0 0 setrgbcolor
	 0 setlinewidth 
	 /Times-Roman findfont 
	 %o scalefont setfont\n",fontscale*2);	 
	 outputstring := outputstring  cat
	 Sprintf("%o -%o moveto (%o) show\n",pos,2*fontscale,num)
	 cat
	 Sprintf("
	 0 0 0 setrgbcolor
	 0 setlinewidth 
	 /Times-Roman findfont 
	 %o scalefont setfont\n",fontscale);	 
      else
	 pos := scale*n-0.2  - translation;
	 len := Max(#num,#dem);
	 outputstring := outputstring  cat
	 Sprintf("%o -%o moveto (%o) show\n",pos,fontscale,num)
	 cat
	 Sprintf("%o -%o moveto (%o) show\n",pos,2.1*fontscale,dem)      
	 cat
	 Sprintf("%o %o moveto %o %o lineto stroke\n",
	 pos-fontscale/10,-fontscale*1.15,
	 pos+fontscale/10 + len*fontscale*0.4,-fontscale*1.15);
      end if;
   end for;
   return outputstring;
end function;
   


///////////////////////////////////////////////////////
//                                                   //
//   Some functions for the user to draw             //
//   fundamental domains                             //
//                                                   //
///////////////////////////////////////////////////////


intrinsic DisplayFareySymbolDomain(FS::SymFry,filename::MonStgElt:
   Colour := [1,1,0],
   PenColour := [0,0,0],
   Overwrite := true,
   Pixels := 1000,
   Size := [],
   Show := false,
   Autoscale := true,
   ShowInternalEdges := false,
   Fontsize := 2,
   Labelsize := 3
   ) -> SeqEnum
   {Display a fundametal domain corresponding to the
   Farey Symbol FS, with edge identifications and cusps labeled.}

   cusps := Cusps(FS);
   labels := Labels(FS);
   
   if Autoscale and Size cmpeq [] then
      // assume the first and last elements of FS are infinite
      // this test should be extended to give a complete test
      // that FS really is a Farey symbol
      CFS := Cusps(FS);
      inf := Parent(CFS[1])!Infinity();
      require CFS[1] eq inf and
      CFS[#CFS] eq inf:"sequence must be a Farey
      sequence, starting and ending with infinity";
      widths := [(b[1]/b[2] - a[1]/a[2])/2 where a := Eltseq(CFS[i]) where
      b := Eltseq(CFS[i+1]) : i in [2..#CFS-2]];
      //      print widths;
      h := Max(widths cat [1]) * (6/5);
      firstCusp := Eltseq(cusps[2]);
      w1 := 1.0*(firstCusp[1]/firstCusp[2]);
      lastCusp := Eltseq(cusps[#cusps-1]);      
      w2 := 1.0*(lastCusp[1]/lastCusp[2]);
      if labels[#labels]
	 eq -3 then w2 := w2 + 0.5;
	 h := 1;
      end if;
      if labels[1]
	 eq -3 then w1 := w1 - 0.5;
	 h := 1;
      end if;
      S := AutoScale(Ceiling(Pixels/(w2-w1)),h,w1,w2)/4;    
    else
       w1 := Size[1];
       w2 := Size[2];
       h := Size[3];
       S := Size[4];
    end if;

    // note scale in ps file, currently "4 4 scale", above.
    scale4 := 4;    
    translation := Integers()!Ceiling(S*w1/scale4);
    w := w2 - w1;
    width := Min(Integers()!Ceiling(w*S),10000);
    height := Min(Integers()!Ceiling(h*S),10000);
    topOfScreen := height;


    writable := startPsfile(filename,translation,width,height,Overwrite,Fontsize);
    if writable then
       FD := FundamentalDomain(FS);
       H := Parent(FD[1]);
       polystring := DrawPolygon(FD,Colour,PenColour,1.0*(S/4),
                                 true,true,translation,topOfScreen,0.5);
       Write(filename,polystring);
       edges := InternalEdges(FS);
       if ShowInternalEdges then
	  for e in edges do
	     ee := [H| c : c in e];
	     polystring := DrawPolygon(ee,Colour,PenColour,1.0*(S/4),
                                       true,false, translation,topOfScreen,0.5);
	     Write(filename,polystring);
	  end for;
	  // assume that the sequence FD starts and ends with oo,
	  // and there are no other infinities in FD.
	  frac := func<x | Eltseq(ExactValue(x))[1]/Eltseq(ExactValue(x))[2]>;
	  found := false;
	  i := 2;
	  while not found and i lt #FD do
	     c1 := FD[i];
	     if IsCusp(c1) then			     
		startCusp := frac(c1);
		found := true;
	     end if;
	     i+:=1;
	  end while;
	  if found then
	     i := #FD -1;
	     found := false;
	     while not found and i gt 1 do
		c1 := FD[i];
		if IsCusp(c1) then			     
		   endCusp := frac(c1);
		   found := true;
		end if;
		i-:=1;
	     end while;
	     if endCusp - startCusp gt 1 then
		fracs := [frac(i) : i in FD | IsCusp(i) and
		i ne H!Infinity()];
		int_fracs := [Integers()!fracs[i] : i in [2..#fracs-1] |
		IsIntegral(fracs[i])];
		for i in int_fracs do
		   polystring := DrawPolygon([H|i,Infinity()],Colour,PenColour,1.0*(S/4),
                                             true,false,translation,topOfScreen,0.5);
		   Write(filename,polystring);
		end for;
	     end if;
	  end if;
       end if;
       Write(filename,labeling(cusps,1.0*(S/4),Fontsize,translation));
       Write(filename,allGlueLabels(labels,cusps,1.0*(S/4),Labelsize,height,translation));
       
       endPsfile(filename);
       if Show then
	  showpsfile(filename);
       end if;
    else
       printf "No file created.\n";
    end if;
    return [w1,w2,h,S];
end intrinsic;



intrinsic DisplayFareySymbolDomain(G::GrpPSL2,filename::MonStgElt:
   Colour := [1,1,0],
   PenColour := [0,0,0],
   Overwrite := true,
   Pixels := 1000,
   Size := [],
   Show := false,
   Autoscale := true,
   ShowInternalEdges := false,
   Fontsize := 2,
   Labelsize := 3
   ) -> SeqEnum
   {Display a fundametal domain corresponding to the
   Farey Symbol of a group G, with edge identifications and cusps labeled.}
   FS := FareySymbol(G);

   return DisplayFareySymbolDomain(FS,filename:
   Colour    := Colour, 
   PenColour := PenColour, 
   Overwrite := Overwrite,
   Pixels    := Pixels   ,
   Size      := Size     ,
   Show      := Show     ,
   Autoscale := Autoscale,
   ShowInternalEdges := ShowInternalEdges,
   Fontsize  := Fontsize ,
   Labelsize := Labelsize);

end intrinsic;

   


///////////////////////////////////////////////////////
//                                                   //
//  functions for detmining size of output           // 
//                                                   //
//                                                   //
///////////////////////////////////////////////////////


function AutoHeight(P)
    max := 0;
    // the following loop takes each edge e_i:=PP[i],PP[i+1] of each
    // polygon PP in the list P of polygons
    // for e_i we compute the point on e_i with largest imaginary part.
    // If the slope of the euclidean straight line between the end points
    // if e_i is greater than 1, then one of the end points has greatest
    // imaginary value.  Otherwise the greatest value is at the mid point
    // of the semi circle which extends e_i
    if #P eq 0 then
       return 0;
    end if;
    Pnontriv := [p : p in P | #p gt 0];
    inf := Parent(Pnontriv[1][1])!Infinity();
    for PP in Pnontriv do
       pLast:=PP[#PP];
       realLast := Real(pLast);
       imLast := Imaginary(pLast);
       for p in PP do
	  im := Imaginary(p);
	  real := Real(p);
	  // for determining width of picture:
	  if p eq inf or pLast eq inf then
	     contains_infinity := true;
	  elif real ne realLast and
	     (Abs((im-imLast)/(real - realLast)) lt 1) then
	     // find the height of the mid point on an arc
	     // between two points:
	     endpoints := ExtendGeodesic([Parent(p)|p,pLast],Parent(p));
	     // it is assumed that if (real - realLast) gt 0.01 then
	     // neither of the end points of the extended geodesic between
	     // p and pLast can be infinity.
	     im := Abs((Real(endpoints[1]) - Real(endpoints[2]))/2);
	  end if;
	  if im gt max and p ne inf then
	     max := im;
	  end if;
	  pLast := p;
	  realLast := real;
	  imLast := im;
       end for;   
    end for;
    // to get some clearance from top point:
    max := max*1.05;
    return max;    
end function;


// function to return index and value of
// first thing not equal to x in sequene S
function firstNot(S,x)
    notfound := true;
    i := 0;
    while notfound and i lt #S do
	i +:= 1;
	if S[i] ne x then
	    notfound := false;
	end if;
    end while;
    if notfound then
	return 0,0;
    else
	return i, S[i];
    end if;
end function;


// function to return index and value of
// first thing not equal to x in sequene
// of seqneces S
function firstNotSeq(S,x)
    notfound := true;
    i := 0;
    j := 0;
    while notfound and i lt #S do
	i +:= 1;
	j := 0;
	while notfound and j lt #(S[i]) do
	    j +:= 1;
	    if S[i][j] ne x then
		notfound := false;
	    end if;
	end while;
    end while;    
    if notfound then
	return 0,0;
    else
	return i,j, S[i][j];
    end if;
end function;

function AutoWidth(P)
    H := UpperHalfPlaneWithCusps();
    i,j,s := firstNotSeq(P,H!Infinity());
    if i*j eq 0 then return 10;
    end if;
    max := Real(P[i][j]);
    min := Real(P[i][j]);
    for PP in P do
	for p in PP do
	    if p ne H!Infinity() then
		re := Real(p);
		if re gt max then
		    max := re;
		elif re lt min then
		    min := re;
		end if;
	    end if;
	end for;
    end for;
    return min,max;        
end function;


function AutoScale(S,h,w1,w2);
    // S representents max dimeension, in
    // both directions
    w := w2 - w1;
    // currently return something arbitrary (100) for the case of h = w =0
    if h eq 0 and w eq 0 then
	return 100;
    elif h eq 0 then
	return Integers()!Ceiling(1.0*S/w);
    elif w eq 0 then
	return Integers()!Ceiling(1.0*S/h);
    else
	H := 1.0*S/h;
	W := 1.0*S/w;
	return Integers()!Ceiling(Max(H,W));
    end if;
end function;











