#
# $Id: OntoSpider.pm,v 1.9 2007/10/02 07:06:20 carelf Exp carelf $
#
# General perl module for OntoSpider that contains code that can be
# used by both the Literature Crawler and the General Purpose Focused
# Crawler. 
#
# Note that this is work in progress.
#
# Carel Fenijn, October 2007
#


package OntoSpider;
use strict;  
use Exporter ();


#
# --------------------- Mainly Declarations ---------------------------
#

use vars qw(@ISA @EXPORT @EXPORT_OK $VERSION);
@ISA  = qw(Exporter);
@EXPORT_OK = qw($verboseornoverbose $debug);
$VERSION="1.0";

my $english_stopword_file="english_stopwords";
my $english_verb_file="english_verbs_list.txt";
my $english_noun_file="english_nouns_list.txt";
my $english_adjectives_and_adverbials_file="english_adjectives_or_adverbials_list.txt";
my $debugmode;
my $testmode=1;

END { }

#
# -------------------------- Subroutines ------------------------------
#


sub normalize_words
#
# For starters a simple approach: remove probable html
# tags and then all non-word chars from a string
#
{
  my $str=$_[0];
  print_test("str: \'$str\'\n");
  $str=~s/\<[^\>]+\>//g;
  $str=~s/\W/ /g;
  $str=~s/\b\d+\b/ /g;
  $str=~s/  / /g;
  return($str);
}


sub remove_stopwords
#
# This subroutine will remove stopwords
#
# First arg: string from which stopwords should be removed
# Second arg: reference to array with stopwords 
#    If the second arg is the string 'default' or there is
#    no second arg, the default stopword list (array) will be used.
# Returns string without the stop words
#
{
  my $str=$_[0];
  my $stopword_ary_ref;
  if($_[1] eq 'default' || !($_[1]))
  {
    $stopword_ary_ref=create_stopword_ary();
  }
  else
  {
    $stopword_ary_ref=$_[1];
  }
  foreach my $stopword (@{$stopword_ary_ref})
  {
    while($str=~/\b$stopword\b/i)
    {
      $str=~s/\b$stopword\b/ /gi;
    }
  }
  return($str);
}


sub press_enter_to_continue
{
  print("Press ENTER to continue...\n");
  <STDIN>;
}


sub standardize_string
#
# Standardize a string, i.e. remove spurious whitespace and
# single characters
#
# First arg: string that must be standardized
# Returns standardized string
#
{
  my $str=$_[0];
  while($str=~/\s\S\s/)
  {
    $str=~s/\s\S\s/ /g;  # remove single chars
  }
  $str=~s/\s+/ /g;      # remove spurious whitespace
  return($str);
}


sub create_stopword_ary
#
# Returns a reference to an array with stop words
#
{
  my @stopword_ary;
  local *STOPWORDF;
  open(STOPWORDF,"$english_stopword_file") ||
    die "FATAL: Could not open $english_stopword_file for reading: $!";
  while(my $l=<STOPWORDF>)
  {
    $l=~s/\|.*//;               # strip comments
    $l=~s/\s+$//;
    next if $l=~/^\s*$/;        # skip lines with only whitespace or comments
    push @stopword_ary, $l;
  }
  close(STOPWORDF);
  return(\@stopword_ary);
}


sub determine_centroid
#
# Determine the centroid based on an array with words from documents
#
# INPUT
#
# First argument: either str. 'initial_calculation' or 'recalculation'
#   If the first arg. is 'initial_calculation', all values of the centroid
#   vector will be set to 1.
#   if the first arg. is 'recalculation', actual TF.IDF values will be used.
#   In the latter case, please make sure that there is enough data for
#   sensible TF.IDF values.
# Second argument: reference to @doc_ary, which contains the words of
#   documents from which the centroid will be created.
# Third argument: average doclength so far (non-zero real)
#
# OUTPUT
#
# Returns: references to the following data structures:
#
#    @centroid_words_ary
#    %centroid_hash
#    @centroid_vector_ary
#
# Example: @centroid_words_ary=('doctor','physician','illness','melon');
#          @centroid_vector_ary=(.9,.9,.8,0);
#          %centroid_hash=(
#                          'doctor' => .9,
#                          'phycisian' => .9,
#                          'illness' => .8,
#                          'melon' => 0
#                         );
#
{
  my $mode=$_[0];
  my @centroid_words_ary=@{$_[1]};
  my $avg_doclen=$_[2];
  my $total_amount_of_docs=$_[3];
  my $df_hash_ref=$_[4];
  my %centroid_hash;
  my %tf_hash;
  my @centroid_vector_ary;
  foreach my $word (@centroid_words_ary)
  {
    $tf_hash{$word}++;
    print_debug($debugmode,"adding \'$word\' to tf_hash\n");
  }
  my $doclen=$#centroid_words_ary;
  print_test("doclen: \'$doclen\'\n");

  foreach my $word (@centroid_words_ary)
  {
    if($mode=~/initial_calculation/i)
    {
      $centroid_hash{$word}=1;
      print_test("adding \'$word\' to centroid_hash\n");
    }
    elsif($mode=~/recalculation/i)
    {
      my $tf;
      if(defined($tf_hash{$word}))
      {
        $tf=$tf_hash{$word};
      }
      else
      {
        $tf=0;
      }
      print_test("recalculation of centroid, tf: \'$tf\'\n");
      #
      # Robertson/Okapi TF: nice-ir0203-week02-2.pdf p. 85ff
      #
      my $okapi_tf=$tf/($tf+.5+(1.5*($doclen/$avg_doclen)));
      print_test("recalculation of centroid, okapi_tf: \'$okapi_tf\'\n");
      #
      # IDF Karen Sparck Jones 1972 nice-ir0203-week02-2.pdf p. 89ff
      #
      my $df=0;
      if(${$df_hash_ref}{$word})
      {
        $df=${$df_hash_ref}{$word};
        print_test("df: \'$df\' based on df_hash \'$word\'\n");
      }
      if($df==0)
      {
        print STDERR "WARNING: centroid $df should not be zero\n";
        print STDERR "Setting centroid weight for $word to 1\n";
        $centroid_hash{$word}=1;
      }
      else
      {
        my $idf=1+log($total_amount_of_docs/$df);
        my $tf_idf_weight=$okapi_tf*$idf;
        $centroid_hash{$word}=$tf_idf_weight;
        print_test("idf: \'$idf\'\n");
        print_test("tf_idf_weight: \'$tf_idf_weight\'\n");
        print_test("centroid_hash $word becomes \'$tf_idf_weight\'\n");

      }
    }
    else
    {
      print STDERR "WARNING: mode should be either initial_calculation or recalc
ulation, assuming initial_calculation\n";
      $centroid_hash{$word}=1;
      print_test("initial calculation assumed, centroid_hash \'$word\' becomes 1\n");
      next;
    }
  }
  @centroid_words_ary=();     # reset
  foreach my $word (sort keys(%centroid_hash))
  {
    push @centroid_words_ary,$word;
    print_test("\'$word\' added to centroid_words_ary\n");
    push @centroid_vector_ary,$centroid_hash{$word};
    print_test("\'$centroid_hash{$word}\' added to centroid_vector_ary\n");
  }
  return(\@centroid_words_ary, \%centroid_hash, \@centroid_vector_ary);
}


sub google_hits_list_to_url_ary
#
# Input: filename of HTML file that contains URLs
# Output: reference to an array with URLs that have been extracted
#
{
  my $google_hits_file=$_[0];
  print_test("google_hits_file: $google_hits_file\n");
  if(!(-T $google_hits_file))
  {
    print STDERR "Error: Not an ASCII file: \"$google_hits_file\"\n";
    exit;
  }
  local *GOOGLEHITF;

  open(GOOGLEHITF,"$google_hits_file") ||
    die "Error: could not open \'$google_hits_file\' for reading: $!";
  while(<GOOGLEHITF>)
  {
    my $url;
    if(/\&q\=(http:\/\/\S+\.pdf)/)
    {
      $url=$1;
    }
    if($url)
    {
      print_test("URL: \'$url\'\n");
    }
  }
  close(GOOGLEHITF);
  my @output_ary;
  return(\@output_ary);
}


sub print_debug
{
  my $debugmode=$_[0];
  if($debugmode)
  {
    print("DEBUGMODE\> @_");
  }
}


sub print_test
{
  if($testmode)
  {
    print("TESTMODE\> @_");
  }
}


sub extract_rdf_triplets
#
# This subroutine will attempt to extract RDF triplets from
# a flat ASCII text file.
# The RDF triplets will be represented as a hash, %rdf_triplet_hash,
# in which the keys are the RDF relations and the values are the
# objects between which the relations hold.
#
# TODO: Try to find third party software that does this job.
#
# First argument: the filename of the document with its full path
# Returns: a reference to %rdf_triplet_hash
#
{
  my $input_document=$_[0];
  local *INPUTF;
  my(%rdf_triplet_hash);
  if(! -T $input_document)
  {
    print("Error: \'$input_document\' should be the filename including path of a plain ASCII text file\n");
    exit;
  }
  my %english_verbs_hash=%{create_english_verbs_hash()};
  my %english_nouns_hash=%{create_english_nouns_hash()};
  my %english_ad_hash=%{create_english_ad_hash()};
  open(INPUTF,"$input_document") ||
    die "Error: Fatal: Could not open $input_document for reading: $!";
  while(my $l=<INPUTF>)
  {
    next if $l=~/^\s*\#|\;/;   # allow for comments
    $l=remove_stopwords($l,'default');
    print_test("$l");
    my @words_ary=split(/\s+/,$l);
    foreach my $word (@words_ary)
    {
      $word=~s/\,|\.$//; # remove trailing interpunction signs
      next if $word !~ /[a-z][a-z]/i;
      if($english_verbs_hash{$word})
      {
        print("$word=VERB ");
      }
      elsif($english_nouns_hash{$word})
      {
        print("$word=NOUN ");
      }
      elsif($english_ad_hash{$word})
      {
        print("$word=ADJ_OR_ADV ");
      }
      else
      {
        if($word=~/s$/)
        {
          $word=~s/s$//;
          if($english_verbs_hash{$word})
          {
            print("$word=VERB ");
          }
          elsif($english_nouns_hash{$word})
          {
            print("$word=NOUN ");
          }
          else
          {
            print("$word=UNKNOWN_CATEGORY ");
          }
        }
        else
        {
          print("$word=UNKNOWN_CATEGORY ");
        }
      }
    }
  }
  close(INPUTF);
  return(\%rdf_triplet_hash);
}


sub create_english_verbs_hash
{
  my(%english_verbs_hash);
  local *VERBF;
  open(VERBF,"$english_verb_file") ||
    die "Error: Fatal: Could not open $english_verb_file for reading: $!";
  while(my $l=<VERBF>)
  {
    next if $l=~/^\s*\#|\;/;   # allow for comments
    $l=~s/\s+$//g;
    if($l=~/(\S+)/)
    {
      $english_verbs_hash{$l}=1;
    }
  }
  close(VERBF);
  return(\%english_verbs_hash);
}


sub create_english_nouns_hash
{
  my(%english_nouns_hash);
  local *NOUNF;
  open(NOUNF,"$english_noun_file") ||
    die "Error: Fatal: Could not open $english_noun_file for reading: $!";
  while(my $l=<NOUNF>)
  {
    next if $l=~/^\s*\#|\;/;   # allow for comments
    $l=~s/\s+$//g;
    if($l=~/(\S+)/)
    {
      $english_nouns_hash{$l}=1;
    }
  }
  close(NOUNF);
  return(\%english_nouns_hash);
}


sub create_english_ad_hash
{
  my(%english_ad_hash);
  local *ADF;
  open(ADF,"$english_adjectives_and_adverbials_file") ||
    die "Error: Fatal: Could not open $english_adjectives_and_adverbials_file for reading: $!";
  while(my $l=<ADF>)
  {
    next if $l=~/^\s*\#|\;/;   # allow for comments
    $l=~s/\s+$//g;
    if($l=~/(\S+)/)
    {
      $english_ad_hash{$l}=1;
    }
  }
  close(ADF);
  return(\%english_ad_hash);
}

1;
