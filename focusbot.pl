#!/usr/bin/perl -w
#
# $Id: focusbot.pl,v 1.2 2007/10/02 07:05:56 carelf Exp carelf $
#
# Focused Crawler that was originally written for assignment 4
# of the course Information Retrieval 2002/2003 UVA and later adapted
# for a thesis.
#
# Note that this is work in progress.
#
# Carel Fenijn, October 2007
#

#
# ----------------------- Some General Notes ----------------------------
#

#
# This code is based on code that was written for earlier assignments for
# this course, so there is quite some overlap.
#
# The following assumptions were made:
#
#  - All retrieved docs are in English, and stop word removal and stemming
#    is based on that
#

#
# Note 0: If a comment is marked with [lwp], it means it was copy&pasted
# from the libwww-perl manpage(s)
#
# Note 1: If the comments of a subroutine mention an Input, this will be
# @_; if it they mention an Output, this refers to the return value(s). 
#

use strict;
use Digest::MD5  qw(md5_base64);
use URI;
use LWP::UserAgent;
use LWP::MediaTypes qw(guess_media_type);
require WWW::RobotRules;

select(STDOUT);
$|=1;           # Unbuffer STDOUT

#
# ------------------------ Mainly Declarations -------------------------
#

my $testmode=0;
my $max_amount_of_retrieved_pages=2000000000;
my $max_amount_of_retrieved_bytes=1048576000000;
my $page_download_delay=10; # Amount of seconds to wait between page downloads

my $data_dir=".";
my $base_download_dir="$data_dir/downloads/$^T";
my $url_to_fname_mappings_file="$base_download_dir/url_to_fname_mappings";
my $url_rankings_file="$base_download_dir/url_rankings_file";
my $focusbot_flagfile="/tmp/focusbot.flag";
my $centroid_file="$base_download_dir/centroid_data";
my $long_fname_suffix="focusbotfname";
my $max_fname_length=20;   # not so important value, avoid very long fnames
my $long_subdir_suffix="focusbotsubdir";
my $max_subdir_length=20;  # not so important value, avoid very long subdirs 

my $english_stopword_file="$data_dir/english_stopwords";
my $english_stemmer_command="$data_dir/estemmer";

#
# Some datastructures that will be used for the centroid 
#
my @centroid_words_ary;  # contains all words of centroid in sorted order
my %centroid_words_hash; # hash of all centroid words
my @centroid_vector_ary; # represents centroid vector with weight values 
my $amount_of_pages_after_which_to_recalculate_centroid=15;

#
# We let URLs inherit the cosine similarity values of their parents,
# but do want to downplay this a bit, for starters, subtract a small value.
#
my $sim_value_inheritance_downplay_factor=.1;

#
# For starters, we manually define @seed_url_ary, the seed document
# set that we will start the crawl with. This can become a set that the
# user supplies manually or the top N documents to some relevant query
# in Google.
#
my @seed_url_ary=(
     'http://www.yourdictionary.com/morph.html',
     'http://www.facstaff.bucknell.edu/rbeard/'
                 );

#
# To make the crawls more restrictive, we require certain substrings
# in URLs, this restriction can be dropped without any problem.
#
my $required_url_substr=qq
!morph|lingui|synta|semant|phon|edu|uni|sci|dict|lex|word!;

my $client_id='focusbot/$Revision: 1.2 $'; # Use RCS version, auto-updated
$client_id=~s/\$\s*Revision\s*\:\s*(\S+)\s*\$/$1/; # Only use bare RCS rev nr

my $amount_of_retrieved_pages=0;   # init
my $amount_of_retrieved_bytes=0;   # init
my $avg_doclen=0;                  # init
my $total_amount_of_docs=0;        # init
my $total_amount_of_words=0;       # init

#
# @q_ary is the Queue of URLs that must be retrieved. It will NOT 
# be like a FIFO stack (breadth-first) or LIFO stack (depth-first),
# but ordering will be adjusted on the fly based on cosine similarity
# values to get a focused crawl.
#
my @q_ary=@seed_url_ary;   # initially, only the seed URLs will be visited
my @uri_start_ary=('A HREF','FRAME SRC');

#
# %sim_value_hash and %sim_value_url_hash will contain cosine
# similarity values of documents
#
my %sim_value_hash;
my %sim_value_url_hash;
#
# %df_hash will contain df values of words
#
my %df_hash;
#
# %processed_urls_hash URLs that have been processed as keys
#
my %processed_urls_hash;        # init
#
# %docid_hash keeps track of DOC IDs
#
my $docid_counter=0;            # init
my %docid_hash;                 # init
#
# %md5_hash records MD5 checksums of downloaded content.
#
my %md5_hash;

#
# ---------------------------- Main Program ----------------------------
#

my @stopword_ary=@{&create_stopword_ary};

&print_test("Using base URLs: \'@seed_url_ary\'\n");
&print_test("Identify to the webserver as: \'$client_id\'\n");
&print_test("Base download dir: \'$base_download_dir\'\n");


if(! -d "$base_download_dir")
{
  mkdir $base_download_dir, 0755 ||
    die "FATAL: Could not create $base_download_dir: $!";
}
local *MAPF;
open(MAPF,">$url_to_fname_mappings_file") ||
  die "Could not open $url_to_fname_mappings_file for overwriting: $!";

&determine_centroid('initial_calculation');

while($amount_of_retrieved_pages < $max_amount_of_retrieved_pages &&
      $amount_of_retrieved_bytes < $max_amount_of_retrieved_bytes)
{
  last if $#q_ary==-1;           # Finish when the queue is empty
  my $url=shift(@q_ary);         # Not FIFO, for @q_ary is adjusted
  next if $processed_urls_hash{$url};
  if($amount_of_retrieved_pages % $amount_of_pages_after_which_to_recalculate_centroid == 0)
  {
    &determine_centroid('recalculation');
  }
  &print_test("Processing next url from queue: \'$url\'\n");
  if($url !~ /^http:\/\//i)
  {
    &print_test("Skipping $url, not starting with http:\/\/\n");
    $processed_urls_hash{$url}=1;
    next;
  }
  my($robotsrules)=&get_robots_rules("$url/robots.txt",$client_id);
  if($robotsrules->allowed($url))
  {
    if(&valid_mediatype($url))
    {
      if(&retrieve_page_and_extract_urls($url))
      {
        $processed_urls_hash{$url}=1;
      }
      else
      {
        print STDERR "WARNING: Did not retrieve $url or not an ASCII file\n";
        next;
      }
    }
    else
    {
      &print_test("Not a valid mediatype of $url\n");
      $processed_urls_hash{$url}=1;
      next;
    }
  }
  else
  {
    &print_test("RobotRules disallow accessing URL $url\n");
    $processed_urls_hash{$url}=1;
    next;
  }
  my($amount_of_urls_in_queue);
  if($testmode)
  {
    $amount_of_urls_in_queue=$#q_ary;
  }
  &print_test("$amount_of_urls_in_queue URLs currently in the queue\n");
  @q_ary=@{&recalculate_q_ary(\@q_ary)};
  &print_test("Sleeping $page_download_delay seconds to avoid hammering the site...\n");
  print("Note that you can abort the crawl by touching /tmp/focusbot.flag\n");
  print("You could press CTRL_Z, then enter: touch /tmp/focusbot.flag \; fg\n");
  sleep($page_download_delay);
  if(-f "$focusbot_flagfile")
  {
    unlink($focusbot_flagfile);
    last;
  }
  print(".") unless $testmode;
}

close(MAPF);

my $amount_of_seconds_used=time-$^T;

print <<"FINALOUTPUT";

-----------------------------------------------------------------------------

Finished!

Amount of retrieved pages: $amount_of_retrieved_pages
Amount of retrieved bytes: $amount_of_retrieved_bytes
Amount of seconds used: $amount_of_seconds_used

Downloads can be found in this dir: $base_download_dir
URL to Filename mappings can be found in the following file:
	$url_to_fname_mappings_file
Ranking of the URLs can be found in this file:
	$url_rankings_file

-----------------------------------------------------------------------------

FINALOUTPUT


#
# ---------------------------- Subroutines ----------------------------
#


sub retrieve_page_and_extract_urls
#
# Input: First arg: standardized URL
#        Second arg (optional): 'centroid_relevant' or 'centroid_nonrelevant'
# Output: 1 upon success
#         0 otherwise
#
# Side-effect(s):
#   Retrieve page and store this on disk
#   Make @q_ary grow if new URLs are detected, but not if
#   second arg eq 'centroid_nonrelevant'
#
{
  my $url=$_[0];
  my $centroid_relevant_mode=0;
  my $centroid_nonrelevant_mode=0;
  my @doc_vector_ary;
  my @total_words_ary;
  if($_[1] eq 'centroid_relevant')
  {
    $centroid_relevant_mode=1;
  }
  elsif($_[1] eq 'centroid_nonrelevant')
  {
    $centroid_nonrelevant_mode=1;
  }
  my $initial_working_dir=`pwd`;
  chomp($initial_working_dir);
  &print_test("Trying to derive data from url \'$url\'...\n");
  #
  # Create a user agent object [lwp]
  #
  my $ua=LWP::UserAgent->new;
  $ua->agent("$client_id ");

  #
  # Create a request [lwp]
  #
  my $req=HTTP::Request->new(GET => "$url");

  #
  # Pass request to the user agent and get a response back [lwp]
  #
  my $res=$ua->request($req);
  #
  # Check the outcome of the response [lwp]
  #
  if($res->is_success) 
  {
    $amount_of_retrieved_pages++;
    my $page_content=$res->content;
    my($fname,$subdir)=&url2fname($page_content);
    if($fname eq "")
    {
      &print_test("Skipping url $url, probably known MD5 checksum\n");
      return(0);
    }
    my $output_file="$subdir/$fname";
    &print_test("Subdir: \'$subdir\'\n");
    &print_test("Output File: \'$output_file\'\n");
    my $stopped_page_content=&remove_stopwords($page_content);
    local *OUTF;
    local *STOPOUTF;
    my $stop_output_file="$output_file\.stop";
    if(!(open(OUTF,">$output_file")))
    {
      print STDERR "WARNING: Could not open $output_file for overwriting: $!";
      chdir($initial_working_dir);
      return(0);
    }
    if(!(open(STOPOUTF,">$stop_output_file")))
    {
      print STDERR "WARNING: Could not open $stop_output_file for overwriting: $!";
      chdir($initial_working_dir);
      return(0);
    }
    print OUTF "$page_content";
    close(OUTF);
    print STOPOUTF "$stopped_page_content";
    close(STOPOUTF);
    if(! -T $output_file)
    {
      print STDERR "Oops, accidentally downloaded non-ASCII file\n";
      if($output_file=~/$base_download_dir/) # double check
      {
        if(unlink($output_file) &&
           unlink($stop_output_file))
        {
          &print_test("Unlinked $output_file and $stop_output_file\n");
        }
        else
        {
          print STDERR "Could not unlink $output_file or $stop_output_file: $!";
        }
      }
      chdir($initial_working_dir);
      return(0);
    }
    my $stem_output_file="$stop_output_file\.stem";
    system("$english_stemmer_command $stop_output_file \> $stem_output_file");
    if(!($centroid_nonrelevant_mode))
    {
      local *STEMF;
      open(STEMF,"$stem_output_file") ||
        die "FATAL: Could not open $stem_output_file for reading: $!";
      while(my $l=<STEMF>)
      {
        $l=&normalize_words($l);
        my(@words_ary)=split(/\s+/,$l);
        if($centroid_relevant_mode)
        {
          @centroid_words_ary=(@centroid_words_ary,@words_ary);
        }
        else
        {
          @total_words_ary=(@total_words_ary,@words_ary);
        }
      }
      close(STEMF);
    }
    my $sim_value=1;
    if($centroid_relevant_mode)
    {
      $sim_value_url_hash{$url}=.9;
    }
    else
    {
      my $doc_vector_ary_ref=&words_ary2vector_ary(\@total_words_ary,\@centroid_words_ary);
      $sim_value=&sim(\@centroid_vector_ary,$doc_vector_ary_ref);
      if($sim_value==0)
      {
        &print_test("Skipping document with cosine similarity value of 0\n");
        return(0);
      }
      $sim_value_hash{$sim_value}=$url;
      $sim_value_url_hash{$url}=$sim_value;
    }
    if(!($centroid_nonrelevant_mode))
    {
      print MAPF "$url\:$fname\n";
    }
    my($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
     $atime,$mtime,$ctime,$blksize,$blocks)=stat($output_file);
    $amount_of_retrieved_bytes+=$size;
    if(!($centroid_nonrelevant_mode))
    {
      while($page_content=~/\<a\s+href\=\"([^\"]+)\"/i)
      {
        my $detected_url=URI->new_abs($1,$res->base);  # absolutize URLs
        $page_content=~s/\<a\s+href\=\"([^\"]+)\"//i;
        &print_test("detected_url before standardization: \'$detected_url\'\n");
        $detected_url=&standardize_url($detected_url);
        &print_test("detected_url after standardization: \'$detected_url\'\n");
        if($url !~ /$required_url_substr/)
        {                       
          &print_test("Skipping $url, $required_url_substr is not substr\n");
        }
        elsif($url=~/^http:\/\//)
        {
          push @q_ary, $detected_url;
          #
          # Note: at this point, the detected URL inherits the
          # cosine similarity value of the page in which it was found,
          # as initial value wich can be adjusted later on! 
          #
          if($centroid_relevant_mode) # exception for the seed URL set
          {
            $sim_value_url_hash{$detected_url}=.9;
          }
          else
          {
            $sim_value_url_hash{$detected_url}=($sim_value_url_hash{$url}-$sim_value_inheritance_downplay_factor);
            if($sim_value_url_hash{$detected_url} < 0)
            {
              $sim_value_url_hash{$detected_url}=.00001;
            }
          }
        }
        else
        {
          &print_test("Not adding \'$detected_url\' to queue, does not start with http:\/\/\n");
        }
      }
    }
  }
  else
  {
    print STDERR "Apparently I did not succeed in gathering data from $url\n";
    return(0);
  }
  chdir($initial_working_dir);
  return(1);
}


sub print_test
{
  if($testmode)
  {
    print("TESTMODE\> $_[0]");
  }
}


sub clean_up_url
#
# Clean a URL up, e.g. remove trailing double quotes, whitespace 
#
{
  my $url=$_[0];
  $url=~s/\s+$//;
  $url=~s/^\s+//;
  $url=~s/^\"//;
  $url=~s/\"$//;
  return($url);
}


sub standardize_url
#
# Input:  URL
# Output: URL in standardized format, if it is relative,
#         it will become an absolute URL.
#
{
  my $url=$_[0];
  $url=&clean_up_url($url);
  return($url);
}


sub valid_mediatype
#
# Return 1 if MediaType is octet/stream or text/*
#        0 otherwise
#
{
  my $url=$_[0];
  my $guessed_content_type=guess_media_type($url);
  &print_test("Guessed MediaType: $guessed_content_type\n");
  if($guessed_content_type=~/^text\// || 
     $guessed_content_type=~/^application\/octet-stream$/i)
  {
    return(1);
  }
  return(0);
}


sub url2fname
#
# Input: string with content of retrieved page
# Output: filename of the downloaded page if the MD5 checksum is 'new',
#         emtpy string otherwise
#
{
  my $str=$_[0];
  my $fname;
  my $subdir;
  my $digest=md5_base64($str);
  if(defined($md5_hash{$digest}))
  {
    &print_test("Known MD5 checksum\n");
    return("","");
  }
  else
  {
    $md5_hash{$digest}=1;
  }
 
  while($docid_hash{$docid_counter})
  {
    $docid_counter++;
  }
  $docid_hash{$docid_counter}=1;
  $fname=$docid_counter;

  if($fname=~/(.)(.)(.)$/)
  {
    $subdir="$base_download_dir/$3/$2/$1";
  }
  elsif($fname=~/(.)(.)$/)
  {
    $subdir="$base_download_dir/0/$2/$1";
  }
  elsif($fname=~/(.)$/)
  {
    $subdir="$base_download_dir/0/0/$1";
  }
  if(system("mkdir -p $subdir") != 0)
  {
    print STDERR "WARNING: Could not create subdir: \'$subdir\'\n";
  }
  else
  {
    &print_test("$subdir created\n");
  }
  return($fname,$subdir);
}


sub get_robots_rules
#
# Note: much of this code is copy&pasted from the
# WWW::RobotRules manpage(s) and slightly adapted.
#
{
  my($url,$client_id)=@_;
  my($robotsrules)=new WWW::RobotRules "$client_id";

  use LWP::Simple qw(get);

  my($robots_txt)=get($url);
  $robotsrules->parse($url,$robots_txt);

  return($robotsrules);
}


sub remove_stopwords
#
# This subroutine will remove stopwords
#
# First arg: string from which stopwords should be removed
# Returns string without the stop words
#
{
  my $str=$_[0];
  foreach my $stopword (@stopword_ary)
  {
    while($str=~/\b$stopword\b/i)
    {
      $str=~s/\b$stopword\b/ /gi;
    }
  }
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


sub words_ary2vector_ary
#
# First arg: reference to array with words
# Second arg: reference to @centroid_words_ary
#
# Returns: reference to @query_vector_ary
#
{
  my @words_ary=@{$_[0]};
  my @centroid_words_ary=@{$_[1]};
  my $doclen=$#words_ary;
  my @vector_ary;
  my %words_hash;
  my %tf_hash;
  $total_amount_of_docs++;
  $total_amount_of_words+=$doclen;
  $avg_doclen=$total_amount_of_words/$total_amount_of_docs;
  foreach my $word (@words_ary)
  {
    $tf_hash{$word}++;
  }
  foreach my $word (keys(%tf_hash))
  {
    $df_hash{$word}++;
  }
  for(my $i=0;$i<=$#centroid_words_ary;$i++)
  {
    my $word=$centroid_words_ary[$i];
    my $tf;
    if(defined($tf_hash{$word}))
    {
      $tf=$tf_hash{$word};
    }
    else
    {
      $tf=0;
    }
    #
    # Robertson/Okapi TF: nice-ir0203-week02-2.pdf p. 85ff
    #
    my $okapi_tf=$tf/($tf+.5+(1.5*($doclen/$avg_doclen)));
    #
    # IDF Karen Sparck Jones 1972 nice-ir0203-week02-2.pdf p. 89ff
    #
    my $df=0;
    if($df_hash{$word})
    {
      $df=$df_hash{$word};
    }
    if($df==0)
    {
      $vector_ary[$i]=0;
    }
    else
    {
      my $idf=1+log($total_amount_of_docs/$df);
      my $tf_idf_weight=$okapi_tf*$idf;
      $vector_ary[$i]=$tf_idf_weight;
    }
  }
  &print_test("vector_ary: @vector_ary\n");
  return(\@vector_ary);
}


sub normalize_words
#
# For starters a simple approach: remove probable html
# tags and then all non-word chars 
#
{
  my $str=$_[0];
  $str=~s/\<[^\>]+\>//g;
  $str=~s/\W/ /g;
  $str=~s/\b\d+\b/ /g;
  $str=~s/  / /g;
  return($str);
}


sub sim
#
# Cosine Similarity between a centroid vector and a document vector
# From college slides nice-ir0203-week02-2.pdf p. 136
#
# First arg: reference to centroid vector array
# Second arg: reference to document vector array of one document
#
# Returns: Cosine Similarity
#
{
  my $query_vector_ary_ref=$_[0];
  my $doc_vector_ary_ref=$_[1];
  my @query_vector_ary=@{$query_vector_ary_ref};
  my @doc_vector_ary=@{$doc_vector_ary_ref};
  my $numerator=0;    # init
  my $denominator=0;  # init - we'll avoid dividing by zero, of course
  #
  # The Cosine Similarity formula is a fraction
  # We calculate the numerator first 
  #
  for(my $i=0;$i<=$#query_vector_ary;$i++)
  {
    $numerator+=($query_vector_ary[$i]*$doc_vector_ary[$i]);
  }

  #
  # The denominator in the Cosine Similarity formula is a product
  # of which we first calculate the left product term and then the
  # right product term, they could be dealt with in the same induction 
  # on the length of the vector as both lenghts are equal anyway, but
  # I think the code is clearer if it they are calculated separately.
  #
  my $left_product_term=0;  # init
  my $right_product_term=0; # init
  for(my $i=0;$i<=$#query_vector_ary;$i++)
  {
    $left_product_term+=(($query_vector_ary[$i])^2);
    $right_product_term+=(($doc_vector_ary[$i])^2);
  }
  $left_product_term=sqrt($left_product_term);
  $right_product_term=sqrt($right_product_term);
  $denominator=$left_product_term*$right_product_term;

  my $cosine_similarity;
  if($denominator != 0)
  {
    $cosine_similarity=$numerator/$denominator;
  }
  else
  {
    $cosine_similarity=0;
  }
  return($cosine_similarity);
}


sub determine_centroid
#
# Determine the centroid based on a set of relevant URLs: @seed_url_ary
#
# First argument: either str. 'initial_calculation' or 'recalculation'
# If the first arg. is 'initial_calculation', all values of the centroid
# vector will be set to 1.
# if the first arg. is 'recalculation', actual TF.IDF values will be used.
# In the latter case, please make sure that there is enough data for
# sensible TF.IDF values.
#
{
  my $mode=$_[0];
  foreach my $seed_url (@seed_url_ary)
  {
    &print_test("Processing seed URL $seed_url\n");
    my($robotsrules)=&get_robots_rules("$seed_url/robots.txt",$client_id);
    if($robotsrules->allowed($seed_url))
    {
      if(&valid_mediatype($seed_url))
      {
        if(&retrieve_page_and_extract_urls($seed_url,'centroid_relevant'))
        {
          $processed_urls_hash{$seed_url}=1;
        }
        else
        {
          print STDERR "WARNING: Did not retrieve $seed_url or not an ASCII file\n";
        }
      }
      else
      {
        &print_test("Not a valid mediatype of $seed_url\n");
        $processed_urls_hash{$seed_url}=1;
      }
    }
    else
    {
      &print_test("RobotRules disallow accessing URL $seed_url\n");
      $processed_urls_hash{$seed_url}=1;
    }
  }
  my %tf_hash;
  foreach my $word (@centroid_words_ary)
  {
    $tf_hash{$word}++;
  }
  my $doclen=$#centroid_words_ary;

  foreach my $word (@centroid_words_ary)
  {
    if($mode=~/initial_calculation/i)
    {
      $centroid_words_hash{$word}=1;
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
      #
      # Robertson/Okapi TF: nice-ir0203-week02-2.pdf p. 85ff
      #
      my $okapi_tf=$tf/($tf+.5+(1.5*($doclen/$avg_doclen)));
      #
      # IDF Karen Sparck Jones 1972 nice-ir0203-week02-2.pdf p. 89ff
      #
      my $df=0;
      if($df_hash{$word})
      {
        $df=$df_hash{$word};
      }
      if($df==0)
      {
        print STDERR "WARNING: centroid $df should not be zero\n";
        print STDERR "Setting centroid weight for word to 1\n";
        $centroid_words_hash{$word}=1;
      }
      else
      {
        my $idf=1+log($total_amount_of_docs/$df);
        my $tf_idf_weight=$okapi_tf*$idf;
        $centroid_words_hash{$word}=$tf_idf_weight;
      }
    }
    else
    {
      print STDERR "WARNING: mode should be either initial_calculation or recalculation, assuming initial_calculation\n";
      $centroid_words_hash{$word}=1;
      next;
    }
  }
  @centroid_words_ary=();
  foreach my $word (sort keys(%centroid_words_hash))
  {
    push @centroid_words_ary,$word;
    push @centroid_vector_ary,$centroid_words_hash{$word};
  }
}


sub recalculate_q_ary
#
# Here we reorder @q_ary based on cosine similarity values.
# In fact, we "throw away" the old @q_ary and replace it by
# one with reverse rankings of cosine similarity values.
#
# Side effect: the ranked URLs will be stored in $url_rankings_file
#
{
  my @q_ary;
  local *RANKF;
  open(RANKF,">$url_rankings_file") ||
    die "FATAL: Could not open $url_rankings_file for overwriting: $!";
  foreach my $url (sort { $sim_value_url_hash{$b} <=> $sim_value_url_hash{$a} } keys %sim_value_url_hash)
  {
    push(@q_ary,$url);
    print RANKF "$url $sim_value_url_hash{$url}\n";
  }
  close(RANKF);
  return(\@q_ary);
}


#
# ----------------------------- End Of Script ------------------------------
#


