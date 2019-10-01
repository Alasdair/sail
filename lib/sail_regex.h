#pragma once

#include<regex.h>

#include"sail.h"

bool string_match(sail_string, sail_string);

typedef struct {
  unsigned int ref_count;
  bool matched;
  sail_string str;
  size_t nmatches;
  regmatch_t *matches;
} sail_match_t;

typedef sail_match_t *sail_match;

SAIL_BUILTIN_TYPE(sail_match);

void __split(sail_match *, sail_string, sail_string, sail_int);
bool __matched(sail_match);
void __group(sail_string *, sail_int, sail_match);

void hex_parse(lbits *, sail_int, sail_string);
void decimal_parse(lbits *, sail_int, sail_string);
void binary_parse(lbits *, sail_int, sail_string);

void hex_string(sail_string *, lbits);
void decimal_string(sail_string *, lbits);
void binary_string(sail_string *, lbits);