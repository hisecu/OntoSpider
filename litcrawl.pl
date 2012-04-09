#!/usr/bin/perl -w
#
# $Id: litcrawl.pl,v 1.1 2005/06/07 15:55:12 carelf Exp carelf $
#
# Literature Crawler
#
# Carel Fenijn, May 2005
#

use Data::Dumper;

$ENV{'PATH'}="";

#
# ----------------------- Mainly Declarations ----------------------
#

my $testmode=1;
my $max_bibliographic_line_length=400;

my $data_dir="./data";
my $tmp_dir="$data_dir/tmp";
#
# Initially, @url_ary should contain URLs of seed documents. At a later
# point, it will contain other documents
# Please enter at least one URL of a PDF paper with English content here:
#
my @url_ary=(
          'http://roa.rutgers.edu/files/537-0802/537-0802-PRINCE-0-0.PDF'
            );

my $google_retrieve_command="./googly.pl";
my $wget_command="/usr/local/bin/wget";
my $pdftohtml_command="/usr/local/bin/pdftohtml";

my $pdftohtml_command_options;
if($testmode)
{
  $pdftohtml_command_options='-i -noframes';
}
else
{
  $pdftohtml_command_options='-i -noframes -q';
}

#
# ------------------------- Main Program ----------------------
#


check_availability_of_resources();

my $bibliography_ary_ref;
my $i=0;                   # while loop counter
while(1)
{
  if($i>0)                 # no seed documents anymore
  {
    @url_ary=@{bibliography_to_url_ary($bibliography_ary_ref)};
  }
  my($doc_ary_ref)=retrieve_docs(\@url_ary);
  if($testmode)
  {
    print_data_str_to_file(\@url_ary,"$tmp_dir/url_ary_contents\_$i");
    print_data_str_to_file($doc_ary_ref,"$tmp_dir/doc_ary_contents\_$i");
  }
  ($bibliography_ary_ref,$doc_vector_hash_ref)=process_docs($doc_ary_ref);
  if($testmode)
  {
    print_data_str_to_file($bibliography_ary_ref,"$tmp_dir/bibliography_ary_contents\_$i");
    print_data_str_to_file($doc_vector_hash_ref,"$tmp_dir/doc_vector_hash_contents\_$i");
  }
  $i++;
}


#
# ------------------------- Subroutines ----------------------
#


sub check_availability_of_resources
#
# Check the availability of resources:
# Create directories if necessary, check that commands that the
# program uses are available, etc.
#
{
  foreach my $dir ($data_dir,$tmp_dir)
  {
    if(! -d "$dir")
    {
      print_test("Creating $dir\n");
      mkdir $dir,0755;
    }
  }
  foreach my $command (
                       $google_retrieve_command,
                       $wget_command,
                       $pdftohtml_command
                      )
  {
    if(! -x $command)
    {
      die "FATAL: Not an executable: \'$command\'\n";
    }
  }
}


sub retrieve_docs
#
# Retrieve documents from remote servers if necessary
#
# Input: Reference to array with URLs of documents, e.g. seed documents
# Output: Reference to array with filenames of retrieved documents
#
{
  my $url_ary_ref=$_[0];
  my @url_ary=@{$url_ary_ref};
  my @doc_ary;
  foreach my $url (@url_ary)
  {
    $url=~s/\s+$//g;
    print_test("URL: \'$url\'\n");
    if($url=~/http:\/\/.*\/([^\/]+\.pdf$)/i)
    {
      my $pdf_fname=$1;
      if(-f "$data_dir/$pdf_fname")
      {
        print("$data_dir/$pdf_fname already present, no need to retrieve it\n");
        push(@doc_ary,"$data_dir\/$pdf_fname");
      }
      else
      { 
        my $previous_dir=chdir($data_dir);
        system("$wget_command $doc");
        chdir($previous_dir);
        if(-f "$data_dir/$pdf_fname")
        {
          push(@doc_ary,"$data_dir\/$pdf_fname");
        }
        else
        {
          print STDERR "Warning: Could not retrieve $doc\n";
        }
      }
    }
    else
    {
      print_test("Invoking $google_retrieve_command \'$url\'");
      local *GOOGLEF;
      open(GOOGLEF,"$google_retrieve_command \'$url\' |") ||
        die "FATAL: Could not pipe $google_retrieve_command \'$url\': $!";
      while(<GOOGLEF>)
      {
        if(/http.*pdf/i)
        {
          print_test("Google hit: $_\n");
        }
      }
      close(GOOGLEF);
    }
  }
  return(\@doc_ary);
}


sub process_docs
#
# Process documents that have been retrieved, PDF documents will first
# be converted to HTML
#
# Input: Reference to array with documents 
# Output: Two references:
#           Reference to array with bibliographic entries
#           Reference to hash with vector representations of documents
#
{
  my($doc_ary_ref)=$_[0];
  my(@retrieved_doc_ary)=@{$doc_ary_ref};
  my(@bibliography_ary);
  my(%doc_vector_hash);
  foreach my $doc (@retrieved_doc_ary)
  {
    my @doc_vector_ary=(0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);   # init
    print_test("Processing doc $doc\n");
    print_test("Converting doc to html...\n");
    system("$pdftohtml_command $pdftohtml_command_options $doc");
    my $html_file=$doc;
    $html_file=~s/\.pdf/\.html/i;
    if(-f "$html_file")
    {
      local *HTMLF;
      open(HTMLF, "$html_file") ||
        die "FATAL: Could not open $html_file for reading: $!";
      while(<HTMLF>)
      {
        if(probably_a_bibliographic_reference($_))
        {
          print_test("Probably a bibliographic reference: $_\n");
          push(@bibliography_ary,$_);
        }
      }
      close(HTMLF);
      $doc_vector_hash{$doc}=\@doc_vector_ary;
    }
  }
  return(\@bibliography_ary,\%doc_vector_hash);
}


sub probably_a_bibliographic_reference
#
# Detect bibliographic references
#
# First arg: line from a paper
# Returns 1 if the line is probably a bibliographic reference,
#         0 otherwise
#
# Note that the algorithm should be refined 
#
{
  my $line=$_[0];
  my $title_candidate;
  my $year_candidate;
  my $author_candidate_substr;
  #
  # Figure out the title of the paper 
  #
  if($line=~/\<i\>(.*)\<\/i\>/ &&
     length($line) <= $max_bibliographic_line_length)
  {
    $title_candidate=$1;
  }
  elsif($line=~/((\w+\,\s+\w+[\.|\,]){2,})/ &&
        length($line) <= $max_bibliographic_line_length)
  {
    $title_candidate=$1;
  }
  #
  # Figure out the year of publication
  #
  if($line=~/\b(\d{4})\b/)
  {
    $year_candidate=$1;
  }
  if($line=~/^(\S+)\s/)
  {
    $author_candidate_substr=$1;
    $author_candidate_substr=~s/\,$//;
  }
  if($title_candidate && $year_candidate && $author_candidate_substr)
  {
    #
    # At this point, it is very likely that we've found a bibliographic
    # entry
    #
    return(1);
  }
  return(0);  
}


sub bibliography_to_url_ary
#
# Input: Reference to array with bibliographic entries (strings)
# Output: Reference to array with URLs of these bibliographic entries
#
# Note: This approach is very crude and can be refined, if a google
# search for a bibliographic entry does not yield a URL of a PDF or
# PS file, it will simply be omitted. 
#
{
  my $bibliography_ary_ref=$_[0];
  my @url_ary;
  foreach my $bibliographic_entry (@{$bibliography_ary_ref})
  {
    $bibliographic_entry=standardize_bibliographic_entry($bibliographic_entry);
    print_test("Invoking $google_retrieve_command \'$bibliographic_entry\'");
    local *GOOGLEF;
    open(GOOGLEF,"$google_retrieve_command \'$bibliographic_entry\' |") ||
      die "FATAL: Could not pipe $google_retrieve_command \'$bibliographic_entry\': $!";
    while(<GOOGLEF>)
    {
      if(/http.*pdf/i)
      {
        print_test("Google hit: $_\n");
        push(@url_ary,$_);
      }
    }
    close(GOOGLEF);
  }
  return(\@url_ary);
}


sub standardize_bibliographic_entry
#
# Standardize a bibliographic entry
#
# Input: 'raw' bibliographic entry
# Output: standardized bibliographic entry, without comma's, markup, etc.
#
{
  my($bibliographic_entry)=$_[0];
print_test("Biblio before: \'$bibliographic_entry\'");
  $bibliographic_entry=~s/\.//g;
  $bibliographic_entry=~s/\,//g;
  $bibliographic_entry=~s/\<[^\>]+\>//g;
print_test("Biblio after: \'$bibliographic_entry\'");
press_enter_to_continue;
  return($bibliographic_entry);
}

sub print_test
{
  if($testmode)
  {
    print("TESTMODE \=\> @_");
  }
}


sub print_data_str_to_file
#
# Write Data::Dumper dump of data structure to file
#
{
  my($data_str_ref,$fname)=@_;

  print("Saving data structure contents to $fname\n"); 
  local *OUTPUTF;
  open(OUTPUTF,">$fname") ||
    die "Could not open $fname for overwriting: $!";

  my $string_representation=Dumper($data_str_ref);
  print OUTPUTF "$string_representation\n";
  close(OUTPUTF);
}


sub press_enter_to_continue
{
  print("Press ENTER to continue...");
  <STDIN>;
}

