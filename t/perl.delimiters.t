#!/usr/bin/env perl

use strict;
use warnings;

use Test::More;

use Text::Balanced::Marpa;

# -----------

my($count)  = 0;
my($parser) = Text::Balanced::Marpa -> new
(
	open  => ['qw/', 'qr/', 'q|', 'qq|'],
	close => [  '/',   '/',  '|',   '|'],
);
my(@text) =
(
	q!qw/one two/!,
	q!qr/^(+.)$/!, # Must single-quote this because of the $.
	q!Literally: \q\r\/^(+.)$\/!, # Ditto.
	q!q|a|!,
	q!Literally: \q\|q|a|\|!,
	q!Literally: q|\q\|a\||!,
	q!qq|a|!,
	q!Literally: \q\q\|qq|a|\|!,
	q!Literally: qq|\q\q\|a\||!,
);

for my $text (@text)
{
	$count++;

	$parser -> text($text);

	ok($parser -> parse == 0, "Parsed $text");

	#diag join("\n", @{$parser -> tree -> tree2string});
}

done_testing($count);
