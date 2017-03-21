#!/usr/bin/perl

print "content-type: text/html\n\n";

$debug = 0;

%reg = &read_input;

$term = $reg{'term'};
$term =~ s/%20/ /g;
$term =~ s/%5[eE]/^/g;
$term =~ s/%25/\$/g;
$term =~ s/%5[cC]/\\/g;
$term =~ s/"//g;
$term =~ s/'//g;
@terms = split /\s+/, $term;

$start = $reg{'start'};
if (! defined $reg{'case'}) {
  $case = 1 | 4 | 8 | 16;
} else {
  $case = $reg{'case'};
}

$use_case = $case & 1;
$use_exact = $case & 2;
$find_chap = $case & 4;
$find_ex = $case & 8;
$find_sig = $case & 16;
$find_all = $case & 32;

if (defined $reg{'advanced'}) {
  $use_case = defined $reg{'use_case'};
  $use_exact = defined $reg{'use_exact'};
  $find_chap = defined $reg{'find_chap'};
  $find_ex = defined $reg{'find_ex'};
  $find_sig = defined $reg{'find_sig'};
  $find_all = defined $reg{'find_all'};
}

$case = (($use_case!=0)*1) | (($use_exact!=0)*2) | (($find_chap!=0)*4) | (($find_ex!=0)*8) | (($find_sig!=0)*16) | (($find_all!=0)*32);

if ($use_case) {
  $gcmd = "grep -i ";
} else {
  $gcmd = "grep ";
}
$cmd = "";
foreach my $term (@terms) {
  if ($use_exact) { 
    $cmd .= " | $gcmd -e ".'"\b'.$term.'\b"';
  } else {
    $cmd .= " | $gcmd -e '$term'";
  }
}  

open RES, "cat ind-all $cmd |" || die();

print q@ 
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html>
    <head>
        <link rel='stylesheet' href='../magma.css' type='text/css'>
        <link rel='stylesheet' href='help.css' type='text/css'>
        <link rel="shortcut icon" href="../magma.ico" type="image/x-icon">
        <link rel="icon" href="../magma.ico" type="image/x-icon">

    <TITLE>Search Results
    </TITLE>
   </head>
    <body BGCOLOR="#FFFFFF">
@;
system "cat ../header.ssi";
print q@
        <table border='0' cellspacing='15' cellpadding='0' width='100%'>
            <tr>
                <td valign='top' width='15%'>
@;
system "cat ../side-cgi.ssi";
print q@
    <tr><td colspan = 2>
      <form action="magma-index.pl" method=get>
        <table><tr>
        <td>
@;
print " <input type=text name='term' size=20 maxlength=20 value='$term'>\n";
print q@
        </input>
        </td></tr><tr><td>
        <input type=submit value="Search the index";></input>
@;
print "<input type=hidden name=start value=0></input>\n";
print "<input type=hidden name=case value=$case></input>\n";
print q@
        </td></tr></table>
      </form>
      </td></tr>
</table>
                </td>
                <td valign='top'>
                    <table cellpadding='2'>
                    <tbody>
                        <tr>
                            <td>
@;                            

%res = ();
if ($debug) {
  print "<h2>Raw</h2>\n";
  print "<pre>\n";
}
while ($name = <RES>) {
  chop $name;
  if ($#res > 10000) {
    last;
  }
  $first = substr $name, 0, 1;
  if (!$find_chap && ($first =~ /[123]/)) {
    next;
  }
  if (!$find_ex && ($first eq '4')) {
    next;
  }
  if (!$find_sig && ($first eq '5')) {
    next;
  }
  my @all = split /<->/, $name;
  if ($debug) {
    print "$name\n";
  }
  if ($find_all) {
    $res{$name} = \@all;
  } else {
    $res{$all[0]."<->".$all[2]} = \@all;
  }
}

if ($debug) {
  print "</pre>\n";
}  
close RES;
@res = sort {$r = $res{$a} -> [0] cmp $res{$b} -> [0]; if ($r) {return $r} ; return $res{$a} ->[1] cmp $res{$b} -> [1]} keys %res;



$head = "<H2>Advanced search</h2></td></tr>\n";
$head .= "<tr><td><form action='magma-index.pl' method=get>\n";
$head .= " <input type=text name='term' size=20 maxlength=20 value='$term'>\n";
$head .= "</input><input type=submit value='Search the index';></input>\n";
$head .= "</td></tr>\n";
$head .= "<tr><td><input type=checkbox name=use_case value=1 ".($use_case ? "checked" :"").">Case insensitive</input>";
$head .= "<input type=checkbox name=use_exact value=1 ".($use_exact ? "checked" :"").">Exact match</input>";
$head .= "<input type=checkbox name=find_chap value=1  ".($find_chap ? "checked" :"").">Find Chapters</input>";
$head .= "<input type=checkbox name=find_ex value=1  ".($find_ex ? "checked" :"").">Find Examples</input>";
$head .= "<input type=checkbox name=find_sig value=1  ".($find_sig ? "checked" :"").">Find Functions</input>";
$head .= "<input type=checkbox name=find_all value=1  ".($find_all ? "checked" :"").">Show All Signatures</input>";
$head .= "<input type=hidden name=advanced value=1></input>";
$head .= "</td></tr></form>\n";

$head .= "<tr><td><H2>Search results for <b>$term</b></H2></td></tr>\n";

if ($#res == -1) {
  $nav = "[____] [____] [____] [____] [<a href='MAGMA.htm'>Up</a>] [<a href='ind.htm'>Index</a>] [<a href='MAGMA.htm'>Root</a>]</td></tr><tr><td>\n";
  #[Next][Prev] [Right] [Left] [Up] [Index] [Root]
  print $nav;
  print $head;
  print "<tr><td>No matches found\n";
  print "</td></tr></tbody>\n"; 
} else {
  $end = $start + 50;
  if ($end > $#res) {
    $end = $#res;
  }
  $next = "";
  $prev = "";
  if ($#res > 50) {
    $head .= "<tr><td>Results $start .. $end of $#res are displayed.";
    if ($end < $#res) {
      $next = "<a href='magma-index.pl?term=$reg{'term'}&start=$end&case=$case'>";
      $head .= " ".$next.'[Next 50]</a>';
    }  
    if ($start) {
      $st = $start - 50;
      if ($st < 0) {
        $st = 0;
      }
      $prev = "<a href='magma-index.pl?term=$reg{'term'}&start=$st&case=$case'>";
      $head .= " $prev".'[Previous 50]</a>';
    }
    $head .= "</td></tr>\n"; 
  }
  $nav = "";
  if ($next eq "") {
    $nav .= "[____] ";
  } else {
    $nav .= "$next".'[Next]</a> ';
  }
  if ($prev eq "") {
    $nav .= "[____] ";
  } else {
    $nav .= "$prev".'[Prev]</a> ';
  }
  if ($next eq "") {
    $nav .= "[_____] ";
  } else {
    $nav .= "$next".'[Right]</a> ';
  }
  if ($prev eq "") {
    $nav .= "[____] ";
  } else {
    $nav .= "$prev".'[Left]</a> ';
  }
  $nav .= "[<a href='MAGMA.htm'>Up</a>] [<a href='ind.htm'>Index</a>] [<a href='MAGMA.htm'>Root</a>]</td></tr><tr><td>\n";

  print $nav;
  print $head;
  $last=-1;
  for ($i = $start; $i<= $end; $i++) {
    @r = @{$res{$res[$i]}};
    if ($last != $r[0]) {
      print "</tbody><tbody>\n";
      print "<tr><td>&nbsp;</td></tr>\n";
      $last = $r[0];
    }
    print "<tr><td><a href='$r[2]'>$r[3]</a></td></tr>\n";
  }
  print "</tbody>\n";

  if ($#res > 50) {
    print "<tbody><tr><td>Results $start .. $end of $#res are displayed.";
    if ($end < $#res) {
      print " $next".'[Next 50]</a>';
    }  
    if ($start) {
      $st = $start - 50;
      if ($st < 0) {
        $st = 0;
      }
      print " $prev".'[Previous 50]</a>';
    }
    print '</td></tr><tr><td>';
  } else {
    print "<tbody><tr><td>\n";
  }
  print $nav;
  print "</td></tr></tbody>\n"; 
}

print q@
                    </table>
                </td>
            </tr>
        </table>
        <br><small>Version: V2.14-1 of <I>
        Mon Oct 28 17:27:42 EST 2007
        </I></small><br>
@;
system "cat ../footer.ssi";
print q@
    </body>
</html>
@;

exit (0);


# Subroutine to read CGI input.
# Script stuck together from work by S.E.Brenner@bioc.cam.ac.uk
# and ronnie@scs.leeds.ac.uk by nik@scs.leeds.ac.uk
#
# Subroutine &read_input takes and decodes data either from
# QUERY_STRING (for GET method, default) or STDIN (for POST method)
# Returned is an associative array of names and values.
#
# For the latest version of this script see Steve Brenner's page on
# http://www.bio.cam.ac.uk/web/form.html


sub read_input
{
    local ($buffer, @pairs, $pair, $name, $value, %FORM);
    # Read in text
    $ENV{'REQUEST_METHOD'} =~ tr/a-z/A-Z/;
    if ($ENV{'REQUEST_METHOD'} eq "POST")
    {
        read(STDIN, $buffer, $ENV{'CONTENT_LENGTH'});
    } else
    {
        $buffer = $ENV{'QUERY_STRING'};
    }
    # Split information into name/value pairs
    @pairs = split(/&/, $buffer);
    foreach $pair (@pairs)
    {
        ($name, $value) = split(/=/, $pair);
        $value =~ tr/+/ /;
        $value =~ s/%(..)/pack("C", hex($1))/eg;
        $FORM{$name} = $value;
    }
    %FORM;
}

