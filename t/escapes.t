#!/usr/bin/env perl

use strict;
use warnings;

use Test::More;

use Text::Balanced::Marpa ':constants';

# -----------

my($count)  = 0;
my($parser) = Text::Balanced::Marpa -> new
(
	open    => ['<', '{', '[', '(', '"', "'", '<:'],
	close   => ['>', '}', ']', ')', '"', "'", ':>'],
	options => nesting_is_fatal,
);
my(@text) =
(
	q|Escaped opening delimiters\: \<, \{, \[, \(, \" and \'.|,
	q|Escaped closing delimiters\: \>, \}, \], \), \" and \'.|,
	q|a|,
	q|{\{a\}}|,
	q|[\[a\]]|,
	q|a {b} c \{\}|,
	q|"\"a\"" [b] c|,
	q|a {b \{c \"\"\"\} d} e|,
	q|Escaping permits nested but non-fatal delimiters\: <: $string \<\: $string \:\> :>|,
	q|I said "I sang 'Δ Lady'" [\"Contains UTF8\"]|,
);

my($result);

for my $text (@text)
{
	$count++;

	$parser -> text($text);

	$result = $parser -> parse;

	ok($result == 0, "Parsed $text");

	diag join("\n", @{$parser -> tree -> tree2string});
}

done_testing($count);
