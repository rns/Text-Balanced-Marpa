#!/usr/bin/env perl

use strict;
use warnings;

use Test::More;

use Text::Balanced::Marpa ':constants';

# -----------

my($count)  = 0;
my($parser) = Text::Balanced::Marpa -> new
(
	open    => ['<:'],
	close   => [':>'],
	options => nesting_is_fatal,
);
my(@text) =
(
	q||,
	q|a|,
	q|<: a :>|,
	q|a {b <: c :> d} e|,
	q|a <: b <: c :> d :> e|, # nesting_is_fatal triggers an error here.
);

my($result);

for my $text (@text)
{
	$count++;

	$parser -> text($text);

	$result = $parser -> parse;

	if ($count == 5)
	{
		ok($result == 1, "Deliberate error: Failed to parse $text");
	}
	else
	{
		ok($result == 0, "Parsed $text");
	}

	#diag join("\n", @{$parser -> tree -> tree2string});
}

done_testing($count);
