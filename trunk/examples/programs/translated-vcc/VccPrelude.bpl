//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Boogie types
// ----------------------------------------------------------------------------

// for each C type there is a value of $ctype Boogie type
type $ctype; 

// a typed pointer -- i.e. a pair of a $ctype and an int
type $ptr;

// name of a C field -- each field of a C struct gets a constant of this type
//   like A.b for field b of struct A.
type $field; 

// describes a kind of a C type:
//  - primitive (includes mathematical types (sequences, maps, sets) and pointers)
//  - array
//  - composite
//  - thread_id_t
//  - claim
type $kind; 

// Encoding trick, we store all type-related information together, including:
//  - if the pointer if typed
//  - the embedding of the pointer
//  - the last element of a path (field name) leading to the pointer
//  - if the pointer is volatile
//  - if the pointer points to an (interior) of an array
// We store it togther as all that information changes together
type $type_state;

// Another encoding trick, here we keep:
//  - closed bit
//  - the current owner (can be thread)
type $status;

// for float and double
type $primitive;

// for structs passed by value
type $struct;

// used for constants describing position in the source code (debugging/model printing only)
type $token;

// the statue of the machine, includes what used to be called $state (now $memory(...) function)
// and $meta (now $typemap(...) and $statusmap(...))
type $state;

// A constant is generated for each pure function, used for ordering frame axioms.
type $pure_function;

// For labeled contracts.
type $label;

// ----------------------------------------------------------------------------
// built-in types
// ----------------------------------------------------------------------------

function $kind_of($ctype) returns($kind);

// these are the only possible kinds
const unique $kind_composite : $kind;
const unique $kind_primitive : $kind;
const unique $kind_array : $kind;
const unique $kind_thread : $kind;

function $sizeof($ctype)returns(int); // in bytes

//Notation: types get a ^ as prefix...
const unique ^^i1: $ctype;
const unique ^^i2: $ctype;
const unique ^^i4: $ctype;
const unique ^^i8: $ctype;
const unique ^^u1: $ctype;
const unique ^^u2: $ctype;
const unique ^^u4: $ctype;
const unique ^^u8: $ctype;
const unique ^^void: $ctype;
const unique ^^bool: $ctype;
const unique ^^f4: $ctype;
const unique ^^f8: $ctype;
const unique ^^claim: $ctype;
const unique ^^root_emb: $ctype;
const unique ^^mathint: $ctype;
// struct A will get ^A :$ctype

axiom $sizeof(^^i1) == 1;
axiom $sizeof(^^i2) == 2;
axiom $sizeof(^^i4) == 4;
axiom $sizeof(^^i8) == 8;
axiom $sizeof(^^u1) == 1;
axiom $sizeof(^^u2) == 2;
axiom $sizeof(^^u4) == 4;
axiom $sizeof(^^u8) == 8;
axiom $sizeof(^^f4) == 4;
axiom $sizeof(^^f8) == 8;

// for types for which $in_range_t(...) is defined
function $as_in_range_t($ctype) returns($ctype);
axiom $as_in_range_t(^^i1) == ^^i1;
axiom $as_in_range_t(^^i2) == ^^i2;
axiom $as_in_range_t(^^i4) == ^^i4;
axiom $as_in_range_t(^^i8) == ^^i8;
axiom $as_in_range_t(^^u1) == ^^u1;
axiom $as_in_range_t(^^u2) == ^^u2;
axiom $as_in_range_t(^^u4) == ^^u4;
axiom $as_in_range_t(^^u8) == ^^u8;
axiom $as_in_range_t(^^f4) == ^^f4;
axiom $as_in_range_t(^^f8) == ^^f8;


// -- sizeof bool, void, mathint uninterpreted

const unique ^$#thread_id_t: $ctype;
const unique ^$#ptrset : $ctype;
const unique ^$#state_t : $ctype;
const unique ^$#struct : $ctype;

axiom $sizeof(^$#thread_id_t) == 1;
axiom $sizeof(^$#ptrset) == 1;

axiom $ptr_level(^^i1) == 0;
axiom $ptr_level(^^i2) == 0;
axiom $ptr_level(^^i4) == 0;
axiom $ptr_level(^^i8) == 0;
axiom $ptr_level(^^u1) == 0;
axiom $ptr_level(^^u2) == 0;
axiom $ptr_level(^^u4) == 0;
axiom $ptr_level(^^u8) == 0;
axiom $ptr_level(^^f4) == 0;
axiom $ptr_level(^^f8) == 0;

axiom $ptr_level(^^mathint) == 0;
axiom $ptr_level(^^bool) == 0;
axiom $ptr_level(^^void) == 0;
axiom $ptr_level(^^claim) == 0;
axiom $ptr_level(^^root_emb) == 0;
axiom $ptr_level(^$#ptrset) == 0;
axiom $ptr_level(^$#thread_id_t) == 0;
axiom $ptr_level(^$#state_t) == 0;
axiom $ptr_level(^$#struct) == 0;
axiom $is_composite(^^claim);
axiom $is_composite(^^root_emb);

// inverse functions here (unptr_to, map_domain, map_range) are for the prover
// so it knows that int*!=short*, i.e. * is injective

// pointers to types
function $ptr_to($ctype) returns($ctype);
function $spec_ptr_to($ctype) returns ($ctype);
function $unptr_to($ctype) returns($ctype);
function $ptr_level($ctype) returns(int);

const $arch_ptr_size : int; // arch-specific; to be defined by a compiler-generated axiom
axiom (forall #n:$ctype :: {$ptr_to(#n)} $unptr_to($ptr_to(#n)) == #n);
axiom (forall #n:$ctype :: {$spec_ptr_to(#n)} $unptr_to($spec_ptr_to(#n)) == #n);
axiom (forall #n:$ctype :: {$ptr_to(#n)} $sizeof($ptr_to(#n)) == $arch_ptr_size);
axiom (forall #n:$ctype :: {$spec_ptr_to(#n)} $sizeof($ptr_to(#n)) == $arch_ptr_size);

function $map_t($ctype, $ctype) returns($ctype);
function $map_domain($ctype) returns($ctype);
function $map_range($ctype) returns($ctype);

axiom (forall #r:$ctype, #d:$ctype :: {$map_t(#r,#d)} $map_domain($map_t(#r,#d)) == #d);
axiom (forall #r:$ctype, #d:$ctype :: {$map_t(#r,#d)} $map_range($map_t(#r,#d)) == #r);

// Make it possible to distinguish between pointers and maps with different number of stars/brackets
// The two numbers should be relatively large primes (so that they least common multiple is large
// enough so that the clash is unlikely for reasonable code).
axiom (forall #n:$ctype :: {$ptr_to(#n)} $ptr_level($ptr_to(#n)) == $ptr_level(#n) + 17);
axiom (forall #n:$ctype :: {$spec_ptr_to(#n)} $ptr_level($spec_ptr_to(#n)) == $ptr_level(#n) + 31);
axiom (forall #r:$ctype, #d:$ctype :: {$map_t(#r,#d)} $ptr_level($map_t(#r,#d)) == $ptr_level(#r) + 23);

// {:weight 0} makes it possible to trigger on $is_primitive(...)
// $is_primitive(t) should be only used when it is known that t is really
// primitive, i.e. not in a precondition or in a premise of an implication
// (unless guarded by a trigger). If it is unknown, use $is_primitive_ch(...).
// The same applies to $is_composite(...) and $is_arraytype(...).

function {:weight 0} $is_primitive(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_primitive }

function {:inline true} $is_primitive_ch(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_primitive }

function {:weight 0} $is_composite(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_composite }

function {:inline true} $is_composite_ch(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_composite }

function {:weight 0} $is_arraytype(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_array }

function {:inline true} $is_arraytype_ch(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_array }

function {:weight 0} $is_threadtype(t:$ctype) returns(bool)
  { $kind_of(t) == $kind_thread }

function {:inline true} $is_thread(p:$ptr) returns(bool)
  { $is_threadtype($typ(p)) }

function {:inline true} $is_ptr_to_composite(p:$ptr) returns(bool)
  { $kind_of($typ(p)) == $kind_composite }

function $field_offset($field) returns(int);
function $field_parent_type($field) returns($ctype);

function $is_non_primitive(t:$ctype) returns(bool);
axiom (forall t:$ctype :: {:weight 0} {$is_composite(t)} $is_composite(t) ==> $is_non_primitive(t));
axiom (forall t:$ctype :: {:weight 0} {$is_arraytype(t)} $is_arraytype(t) ==> $is_non_primitive(t));
axiom (forall t:$ctype :: {:weight 0} {$is_threadtype(t)} $is_threadtype(t) ==> $is_non_primitive(t));

function {:inline true} $is_non_primitive_ch(t:$ctype) returns(bool)
  { $kind_of(t) != $kind_primitive }

function {:inline true} $is_non_primitive_ptr(p:$ptr) returns(bool)
  { $is_non_primitive($typ(p)) }

axiom (forall #r:$ctype, #d:$ctype :: {$map_t(#r,#d)} $is_primitive($map_t(#r,#d)));
axiom (forall #n:$ctype :: {$ptr_to(#n)} $is_primitive($ptr_to(#n)));
axiom (forall #n:$ctype :: {$spec_ptr_to(#n)} $is_primitive($spec_ptr_to(#n)));
axiom (forall #n:$ctype :: {$is_primitive(#n)} $is_primitive(#n) ==> !$is_claimable(#n));
axiom (forall #n:$ctype :: {$is_claimable(#n)} $is_claimable(#n) ==> $is_composite(#n));
axiom $is_primitive(^^void);
axiom $is_primitive(^^bool);
axiom $is_primitive(^^mathint);
axiom $is_primitive(^$#ptrset);
axiom $is_primitive(^$#state_t);
axiom $is_threadtype(^$#thread_id_t);

axiom $is_primitive(^^i1);
axiom $is_primitive(^^i2);
axiom $is_primitive(^^i4);
axiom $is_primitive(^^i8);
axiom $is_primitive(^^u1);
axiom $is_primitive(^^u2);
axiom $is_primitive(^^u4);
axiom $is_primitive(^^u8);
axiom $is_primitive(^^f4);
axiom $is_primitive(^^f8);

const $me_ref : int;
function $me() returns($ptr);
axiom $in_range_spec_ptr($me_ref);
axiom $me() == $ptr(^$#thread_id_t, $me_ref);

function {:inline true} $current_state(s:$state) returns($state) { s }

type $memory_t;
function $select.mem($memory_t, $ptr) returns(int);
function $store.mem($memory_t, $ptr, int) returns($memory_t);
axiom (forall M:$memory_t, p:$ptr, v:int :: {:weight 0}
  $select.mem($store.mem(M, p, v), p) == v);
axiom (forall M:$memory_t, p:$ptr, q:$ptr, v:int :: {:weight 0}
  p == q
  ||
  $select.mem($store.mem(M, p, v), q) == $select.mem(M, q)
  );

type $typemap_t;
function $select.tm($typemap_t, $ptr) returns($type_state);
function $store.tm($typemap_t, $ptr, $type_state) returns($typemap_t);
axiom (forall M:$typemap_t, p:$ptr, v:$type_state :: {:weight 0}
  $select.tm($store.tm(M, p, v), p) == v);
axiom (forall M:$typemap_t, p:$ptr, q:$ptr, v:$type_state :: {:weight 0}
  p == q
  ||
  $select.tm($store.tm(M, p, v), q) == $select.tm(M, q)
  );

type $statusmap_t;
function $select.sm($statusmap_t, $ptr) returns($status);
function $store.sm($statusmap_t, $ptr, $status) returns($statusmap_t);
axiom (forall M:$statusmap_t, p:$ptr, v:$status :: {:weight 0}
  $select.sm($store.sm(M, p, v), p) == v);
axiom (forall M:$statusmap_t, p:$ptr, q:$ptr, v:$status :: {:weight 0}
  p == q
  ||
  $select.sm($store.sm(M, p, v), q) == $select.sm(M, q)
  );


function $memory(s:$state) returns($memory_t);
function $typemap(s:$state) returns($typemap_t);
function $statusmap(s:$state) returns($statusmap_t);

function {:inline true} $mem(s:$state, p:$ptr) returns(int)
  { $select.mem($memory(s), p) }
function {:inline true} $mem_eq(s1:$state, s2:$state, p:$ptr) returns(bool)
  { $mem(s1, p) == $mem(s2, p) }
function {:inline true} $st_eq(s1:$state, s2:$state, p:$ptr) returns(bool)
  { $st(s1, p) == $st(s2, p) }
function {:inline true} $ts_eq(s1:$state, s2:$state, p:$ptr) returns(bool)
  { $ts(s1, p) == $ts(s2, p) }

// ----------------------------------------------------------------------------
// nesting of structs
// ----------------------------------------------------------------------------
function $extent_hint(p:$ptr, q:$ptr) returns(bool);
axiom (forall p:$ptr, q:$ptr, r:$ptr :: {$extent_hint(p, q), $extent_hint(q, r)}
  $extent_hint(p, q) && $extent_hint(q, r) ==> $extent_hint(p, r));
axiom (forall p:$ptr :: {$typ(p)} $extent_hint(p, p));

function $nesting_level($ctype) returns(int);
function $is_nested($ctype, $ctype) returns(bool);

function $nesting_min($ctype, $ctype) returns(int);
function $nesting_max($ctype, $ctype) returns(int);
function $is_nested_range(t:$ctype, s:$ctype, min:int, max:int) returns(bool)
  { $is_nested(t, s) && $nesting_min(t, s) == min && $nesting_max(t, s) == max }

/*
// emb = emb(emb(...(emb(p))..)), where the number of nested emb is lev
function $is_emb_at_lev(p:$ptr, emb:$ptr, q:$ptr, lev:int) returns(bool)
  { $is_nested($typ(p), $typ(q)) && 
    $nesting_min($typ(p), $typ(q)) <= lev && lev <= $nesting_max($typ(p), $typ(q)) &&
    emb == q }

axiom (forall p:$ptr, q:$ptr, S:$state :: {$in_extent_of(S, p, q), $is_primitive($typ(p))}
  $good_state(S) ==>
    $is_primitive($typ(p)) && $in_extent_of(S, p, q) ==> 
      p == q || $in_extent_of(S, $emb(S, p), q));

function $st_extent($status) returns($ptrset);
axiom (forall S:$state, p:$ptr :: {$extent(S, p)}
  $extent(S, p) == $st_extent($st(S, p)));
*/

// $in_extent_of(S, p, q) ==> p == q || $is_emb_at_lev(p, $emb(S, p), q, 1) || $is_emb_at_lev(p, $emb(S, $emb(S, p)), q, 2) || ... 
// $in_extent_of(S, p, q) <== p == q || $emb(S, p) == q || $emb(S, $emb(S, p)) == q || ... 

//function $no_known_nesting($ctype) returns(bool);
//function $single_known_nesting($ctype, $ctype) returns(bool);
//function $is_known_type($ctype) returns(bool);

//axiom (forall T:$ctype, S:$ctype :: {$is_nested(T, S)}
//  $is_nested(T, S) ==> $nesting_level(T) < $nesting_level(S));

// ----------------------------------------------------------------------------
// typed pointers
// ----------------------------------------------------------------------------

function $typ($ptr)returns($ctype);
function $ref($ptr)returns(int);
function $ptr($ctype,int)returns($ptr);
axiom (forall #t:$ctype, #b:int :: {:weight 0} $typ($ptr(#t,#b))==#t);
axiom (forall #t:$ctype, #b:int :: {:weight 0} $ref($ptr(#t,#b))==#b);
//axiom (forall #p:$ptr :: {$typ(#p)} {$ref(#p)} $ptr($typ(#p), $ref(#p)) == #p);

// Use for computing references for ghost fields, instead of saying p+$field_offset(f) we use
// $ghost_ref(p,f). This has an added bonus that the embedding and path can be the same reagrdless
// of the current $meta
function $ghost_ref($ptr, $field) returns(int);
function $ghost_emb(int) returns($ptr);
function $ghost_path(int) returns($field);
axiom (forall p:$ptr, f:$field :: {:weight 0} {$ghost_ref(p, f)}
  $ghost_emb($ghost_ref(p, f)) == p && $ghost_path($ghost_ref(p, f)) == f );

axiom (forall p:$ptr, f:$field :: {$ghost_ref(p, f)}
  $in_range_spec_ptr($ghost_ref(p,f)));

function $physical_ref(p:$ptr, f:$field) returns(int);
// Make the physical fields, when we do not generate offset axioms, behave like ghost fields
//  (this is unsound, but not so much).
//axiom (forall p:$ptr, f:$field :: {:weight 0} {$physical_ref(p, f)}
//  $ghost_emb($physical_ref(p, f)) == p && $ghost_path($physical_ref(p, f)) == f );

function $array_path(basefield:$field, off:int) returns($field);

function $is_base_field($field) returns(bool);

function $array_path_1($field) returns($field);
function $array_path_2($field) returns(int);
axiom (forall fld:$field, off:int :: {:weight 0} {$array_path(fld, off)}
  !$is_base_field($array_path(fld, off)) &&
  $array_path_1($array_path(fld, off)) == fld &&
  $array_path_2($array_path(fld, off)) == off);

const $null:$ptr;
axiom $null == $ptr(^^void, 0);

//function {:inline true} $is(p:$ptr, t:$ctype) returns (bool)
//  { $typ(p)==t }

//typed pointer test
function $is($ptr,$ctype) returns (bool);
axiom (forall #p:$ptr, #t:$ctype :: {:weight 0} $is(#p,#t)== ($typ(#p)==#t));
// create $ptr(...) function symbol, so later we have something to trigger on
axiom (forall #p:$ptr, #t:$ctype :: {$is(#p, #t)} $is(#p, #t) ==> #p == $ptr(#t, $ref(#p)));

function {:inline true} $ptr_cast(#p:$ptr,#t:$ctype) returns($ptr)
  { $ptr(#t, $ref(#p)) }

function {:inline true} $read_ptr(S:$state, p:$ptr, t:$ctype) returns($ptr)
  { $ptr(t, $mem(S, p)) }

//dot and (its "inverse") emb/path access
function $dot($ptr,$field) returns ($ptr);
function {:inline true} $emb(S:$state,#p:$ptr) returns ($ptr)
  { $ts_emb($ts(S, #p)) }
function {:inline true} $path(S:$state,#p:$ptr) returns($field)
  { $ts_path($ts(S, #p)) }

function $containing_struct(p:$ptr, f:$field) returns($ptr);
function $containing_struct_ref(p:$ptr, f:$field) returns(int);

axiom (forall r:int, f:$field :: 
  { $containing_struct($dot($ptr($field_parent_type(f), r), f), f) } 
  $containing_struct($dot($ptr($field_parent_type(f), r), f), f) == $ptr($field_parent_type(f), r));

axiom (forall p:$ptr, f:$field :: 
  {$containing_struct(p, f)}
  $containing_struct(p, f) == $ptr($field_parent_type(f), $containing_struct_ref(p, f)));

axiom (forall p:$ptr, f:$field :: 
  {$dot($containing_struct(p, f), f)}
  $field_offset(f) >= 0 ==> // only for physical fields
  $ref($dot($containing_struct(p, f), f)) == $ref(p));

// assumed by the compiler in struct translation
function $is_primitive_non_volatile_field($field) returns(bool);
function $is_primitive_volatile_field($field) returns(bool);
function $is_primitive_embedded_array(f:$field, sz:int) returns(bool);
function $is_primitive_embedded_volatile_array(f:$field, sz:int, t:$ctype) returns(bool);

function $embedded_array_size(f:$field, t:$ctype) returns(int);

function {:inline true} $static_field_properties(f:$field, t:$ctype) returns(bool)
  { $is_base_field(f) && $field_parent_type(f) == t }

function {:inline true} $field_properties(S:$state, p:$ptr, f:$field, tp:$ctype, isvolatile:bool)  returns(bool)
  { $typed2(S, $dot(p, f), tp) &&
    $emb(S, $dot(p, f)) == p &&
    $path(S, $dot(p, f)) == f &&
    $is_volatile(S, $dot(p, f)) == isvolatile 
  }

function $ts_typed($type_state) returns(bool);
function $ts_emb($type_state) returns($ptr);
function $ts_path($type_state) returns($field);
function $ts_is_volatile($type_state) returns(bool);
  
axiom (forall ts:$type_state :: {$ts_emb(ts)} $kind_of($typ($ts_emb(ts))) != $kind_primitive && $is_non_primitive($typ($ts_emb(ts))) );

//V2:
axiom (forall S:$state, p:$ptr :: {$typed(S, p), $ts(S, $emb(S, p))} $typed(S, p) ==> $typed(S, $emb(S, p)));
//axiom (forall S:$state, p:$ptr :: {$typed(S, p), $typed(S, $emb(S, p))} $typed(S, p) ==> $typed(S, $emb(S, p)));

// it has no further embedding (not embedded inside another struct)
function {:inline true} $is_object_root(S:$state, p:$ptr) returns(bool)
  { $emb(S, p) == $ptr(^^root_emb, $ref(p)) }

function {:inline true} $is_volatile(S:$state, p:$ptr) returns(bool)
  { $ts_is_volatile($ts(S, p)) }

axiom (forall S:$state, p:$ptr ::
  {$is_volatile(S, p)} $good_state(S) && $is_volatile(S, p) ==> $is_primitive_ch($typ(p)));

// just tmp
function {:inline true} $is_malloc_root(S:$state, p:$ptr) returns(bool)
  { $is_object_root(S, p) }

/*
function $prim_emb(S:$state, p:$ptr) returns($ptr);
axiom (forall S:$state, p:$ptr :: {$is_primitive($typ(p)), $prim_emb(S, p)}
  $is_primitive($typ(p)) ==> $prim_emb(S, p) == $emb(S, p));
axiom (forall S:$state, p:$ptr :: {$is_non_primitive($typ(p)), $prim_emb(S, p)}
  $is_non_primitive($typ(p)) ==> $prim_emb(S, p) == p);
*/

function $current_timestamp(S:$state) returns(int);
axiom (forall S:$state, p:$ptr :: {:weight 0} {$st(S, p)}
  $timestamp(S, p) <= $current_timestamp(S) ||
  !$ts_typed($ts(S, p))
  );

function {:inline true} $is_fresh(M1:$state, M2:$state, p:$ptr) returns(bool)
  { $current_timestamp(M1) < $timestamp(M2, p) && $timestamp(M2, p) <= $current_timestamp(M2) }

function $in_writes_at(time:int, p:$ptr) returns(bool);

function {:inline true} $writable(S:$state, begin_time:int, p:$ptr) returns(bool)
  { ($in_writes_at(begin_time, p) || $timestamp(S, p) >= begin_time) && $mutable(S, p) }

function {:inline true} $top_writable(S:$state, begin_time:int, p:$ptr) returns(bool)
  { ($in_writes_at(begin_time, p) || $timestamp(S, p) >= begin_time)
    && $thread_owned_or_even_mutable(S, p) }

// ----------------------------------------------------------------------------
// Value structs
// ----------------------------------------------------------------------------

const $struct_zero : $struct;

axiom ($good_state($vs_state($struct_zero)));

function {:inline true} $vs_base(s:$struct, t:$ctype) returns($ptr)
  { $ptr(t, $vs_base_ref(s)) }
function $vs_base_ref($struct) returns(int);

function $vs_state($struct) returns($state);
axiom (forall s:$struct :: $good_state($vs_state(s)));

function $vs_ctor(S:$state, p:$ptr) returns($struct);
axiom (forall S:$state, p:$ptr :: {$vs_ctor(S, p)}
  $good_state(S) ==>
    $vs_base_ref($vs_ctor(S, p)) == $ref(p) && $vs_state($vs_ctor(S, p)) == S);

axiom (forall f:$field, t:$ctype :: { $mem($vs_state($struct_zero), $dot($vs_base($struct_zero, t), f)) }
  $mem($vs_state($struct_zero), $dot($vs_base($struct_zero, t), f)) == 0);

// ----------------------------------------------------------------------------
// Records
// ----------------------------------------------------------------------------

type $record;
const $rec_zero : $record;
function $rec_update(r:$record, f:$field, v:int) returns($record);
function $rec_fetch(r:$record, f:$field) returns(int);

function $rec_update_bv(r:$record, f:$field, val_bitsize:int, from:int, to:int, repl:int) returns($record)
  { $rec_update(r, f, $bv_update($rec_fetch(r, f), val_bitsize, from, to, repl)) }

axiom (forall f:$field :: $rec_fetch($rec_zero, f) == 0);

axiom (forall r:$record, f:$field, v:int :: {$rec_fetch($rec_update(r, f, v), f)}
  $rec_fetch($rec_update(r, f, v), f) == $unchecked($record_field_int_kind(f), v));

axiom (forall r:$record, f:$field :: {$rec_fetch(r, f)}
  $in_range_t($record_field_int_kind(f), $rec_fetch(r, f)));

axiom (forall r:$record, f1:$field, f2:$field, v:int :: {$rec_fetch($rec_update(r, f1, v), f2)}
  $rec_fetch($rec_update(r, f1, v), f2) == $rec_fetch(r, f2) || f1 == f2);

function $is_record_type(t:$ctype) returns(bool);
function $is_record_field(parent:$ctype, field:$field, field_type:$ctype) returns(bool);

axiom (forall t:$ctype :: {$is_record_type(t)} $is_record_type(t) ==> $is_primitive(t));

function $as_record_record_field($field) returns($field);
axiom (forall p:$ctype, f:$field, ft:$ctype :: {$is_record_field(p, f, ft), $is_record_type(ft)}
  $is_record_field(p, f, ft) && $is_record_type(ft) ==> $as_record_record_field(f) == f);

function $record_field_int_kind(f:$field) returns($ctype);

function $rec_eq(r1:$record, r2:$record) returns(bool)
  { r1 == r2 }
function $rec_base_eq(x:int, y:int) returns(bool)
  { x == y }

function $int_to_record(x:int) returns($record);
function $record_to_int(r:$record) returns(int);

axiom (forall r:$record :: $int_to_record($record_to_int(r)) == r);

axiom (forall r1:$record, r2:$record :: {$rec_eq(r1, r2)}
  $rec_eq(r1, r2) <==
  (forall f:$field :: $rec_base_eq($rec_fetch(r1, f), $rec_fetch(r2, f))));

axiom (forall r1:$record, r2:$record, f:$field ::
 {$rec_base_eq($rec_fetch(r1, f), $rec_fetch(r2, $as_record_record_field(f)))}
 $rec_base_eq($rec_fetch(r1, f), $rec_fetch(r2, f)) <==
   $rec_eq($int_to_record($rec_fetch(r1, f)), $int_to_record($rec_fetch(r2, f))));


// ----------------------------------------------------------------------------
// state
// ----------------------------------------------------------------------------
var $s: $state;

function $good_state($state) returns(bool);
function $invok_state($state) returns(bool);

const $state_zero : $state; // for record/map initialization

function $has_volatile_owns_set(t:$ctype) returns(bool);
axiom $has_volatile_owns_set(^^claim);

function $owns_set_field(t:$ctype) returns($field);

axiom (forall #p: $ptr, t:$ctype :: { $dot(#p, $owns_set_field(t)) } 
  $dot(#p, $owns_set_field(t)) == $ptr(^$#ptrset, $ghost_ref(#p, $owns_set_field(t))));

function $st_owner($status) returns($ptr);
function $st_closed($status) returns(bool);
function $st_timestamp($status) returns(int);
function $st_ref_cnt(s:$status) returns(int);

function $owner(S:$state, p:$ptr) returns($ptr);
function $closed(S:$state, p:$ptr) returns(bool);
function $timestamp(S:$state, p:$ptr) returns(int);

axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_primitive($typ(p)), $owner(S, p)}
  $is_primitive($typ(p)) ==> $owner(S, p) == $owner(S, $emb(S, p)));
axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_non_primitive($typ(p)), $owner(S, p)}
  $is_non_primitive($typ(p)) ==> $owner(S, p) == $st_owner($st(S, p)));
 
axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_primitive($typ(p)), $closed(S, p)}
  $is_primitive($typ(p)) ==> $closed(S, p) == $st_closed($st(S, $emb(S, p))));
axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_non_primitive($typ(p)), $closed(S, p)}
  $is_non_primitive($typ(p)) ==> $closed(S, p) == $st_closed($st(S, p)));
 
axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_primitive($typ(p)), $timestamp(S, p)}
  $is_primitive($typ(p)) ==> $timestamp(S, p) == $st_timestamp($st(S, $emb(S, p))));
axiom (forall S:$state, p:$ptr :: {:weight 0} {$is_non_primitive($typ(p)), $timestamp(S, p)}
  $is_non_primitive($typ(p)) ==> $timestamp(S, p) == $st_timestamp($st(S, p)));
 
function $position_marker() returns(bool);
axiom $position_marker();

axiom (forall s:$status :: {$st_owner(s)} $kind_of($typ($st_owner(s))) != $kind_primitive && $is_non_primitive($typ($st_owner(s))));

function {:inline true} $st(S:$state, p:$ptr) returns($status)
  { $select.sm($statusmap(S), p) }

function {:inline true} $ts(S:$state, p:$ptr) returns($type_state)
  { $select.tm($typemap(S), p) }

function {:weight 0} $owns(S:$state, #p:$ptr)returns($ptrset)
  { $int_to_ptrset($mem(S, $dot(#p, $owns_set_field($typ(#p))))) }

function {:inline true} $nested(S:$state, p:$ptr) returns(bool)
  { $kind_of($typ($owner(S, p))) != $kind_thread }

function {:inline true} $nested_in(S:$state, p:$ptr, owner:$ptr) returns(bool)
  { $owner(S, p) == owner && $closed(S, p) }

function {:inline true} $wrapped(S:$state, #p:$ptr, #t:$ctype) returns(bool)
  { $closed(S, #p) && $owner(S, #p) == $me() && $typed2(S, #p, #t) && $kind_of(#t) != $kind_primitive && $is_non_primitive(#t) }

function {:inline true} $irrelevant(S:$state, p:$ptr) returns(bool)
  { $owner(S, p) != $me() || ($is_primitive_ch($typ(p)) && $closed(S, p)) }

function {:weight 0} $mutable(S:$state, p:$ptr) returns(bool)
  { $typed(S, p) && $owner(S, p) == $me() && !$closed(S, p) }

function {:inline true} $thread_owned(S:$state, p:$ptr) returns(bool)
  { $typed(S, p) && $owner(S, p) == $me() }

function {:inline true} $thread_owned_or_even_mutable(S:$state, p:$ptr) returns(bool)
  { $typed(S, p) && $owner(S, p) == $me() && ($is_primitive_ch($typ(p)) ==> !$closed(S, p)) }

function $typed(S:$state, p:$ptr) returns(bool);
axiom
  (forall S:$state, #p:$ptr :: {:weight 0} {$typed(S,#p)} $good_state(S) ==> $typed(S,#p) == $ts_typed($ts(S, #p)));
axiom
  (forall S:$state, #p:$ptr :: {$typed(S,#p)} $good_state(S) && $typed(S,#p) ==> $ref(#p) > 0);

function $in_range_phys_ptr(#r:int) returns(bool)
  { $in_range(0, #r, $arch_spec_ptr_start) }
function $in_range_spec_ptr(#r:int) returns(bool)
  { 0 == #r || #r > $arch_spec_ptr_start }
const $arch_spec_ptr_start : int; // arch-specific; to be defined by a compiler-generated axiom

function {:inline true} $typed2(S:$state, #p:$ptr, #t:$ctype) returns(bool)
  { $is(#p, #t) && $typed(S, #p) }

axiom (forall S:$state, #r:int, #t:$ctype :: {$typed(S, $ptr(#t, #r))}
  $typed(S, $ptr(#t, #r)) && $in_range_phys_ptr(#r) ==> $in_range_phys_ptr(#r + $sizeof(#t) - 1));

function {:inline true} $typed2_phys(S:$state, #p:$ptr, #t:$ctype) returns (bool)
  { $typed2(S, #p, #t) && ($typed2(S, #p, #t) ==> $in_range_phys_ptr($ref(#p))) }

function {:inline true} $typed2_spec(S:$state, #p:$ptr, #t:$ctype) returns (bool)
  { $typed2(S, #p, #t) && ($typed2(S, #p, #t) ==> $in_range_spec_ptr($ref(#p))) }

function {:inline true} $ptr_eq(p1:$ptr,p2:$ptr) returns(bool)
  { $ref(p1) == $ref(p2) }

function {:inline true} $ptr_neq(p1:$ptr,p2:$ptr) returns(bool)
  { $ref(p1) != $ref(p2) }

//axiom (forall #p : $ptr, #f1 : $field, #f2 : $field ::
//  { $ref($dot(#p, #f1)), $ref($dot(#p, #f2)) }
//  ($ref($dot(#p, #f1)) == $ref($dot(#p, #f2))) ==> (#f1 == #f2));

// Unsound version - fast

//axiom (forall /* S: $state, */ #p1: $ptr, #p2: $ptr, #f1 : $field, #f2 : $field :: 
//  { /* $typed(S, #p1), $typed(S, #p2), */ $ref($dot(#p1, #f1)), $ref($dot(#p2, #f2)) } 
//  /* $typed(S, #p1) && $typed(S, #p2) && */ ($ref($dot(#p1, #f1)) == $ref($dot(#p2, #f2))) ==> (#p1 == #p2 && #f1 == #f2));

// Sound version - currently slow

//axiom (forall S: $state, #p1: $ptr, #p2: $ptr, #f1 : $field, #f2 : $field :: 
//  { $typed(S, #p1), $typed(S, #p2), $ref($dot(#p1, #f1)), $ref($dot(#p2, #f2)) } 
//  $typed(S, #p1) && $typed(S, #p2) && ($ref($dot(#p1, #f1)) == $ref($dot(#p2, #f2))) ==> (#p1 == #p2 && #f1 == #f2));

//axiom (forall S:$state, #p1: $ptr, #p2: $ptr, #f1: $field, #f2: $field ::
//  $typed(S, #p1) && $typed(S, #p2) && $typ(#p1) != $typ(#p2) ==> $ref($dot(#p1, #f1)) != $ref($dot(#p2, #f2)))

//function $any_nonmutable(#m1:$state, #m2:$state, #p:$ptr) returns(bool)
//  { $closed(#m1, #p) || $closed(#m2, #p) }

function {:inline true} $is_primitive_field_of(S:$state, #f:$ptr, #o:$ptr) returns(bool)
  { $is_primitive_ch($typ(#f)) && $emb(S, #f) == #o }


// ----------------------------------------------------------------------------
// thread locality
// ----------------------------------------------------------------------------

/*
// an owner that is itself owned by a thread
function $top_owner(S:$state, p:$ptr) returns($ptr);

function $fetch_top_owner(v:$version, q:$ptr) returns($ptr);

axiom (forall S:$state, p:$ptr ::
$top_owner(S, p) == $fetch_top_owner($read_version(S, $top_owner(S, p)), p));
*/

/*
function {:inline true} $thread_owner(S:$state, obj:$ptr) returns($ptr)
  { $st_thread_owner($statusmap(S), obj) }
function $st_thread_owner(S:$statusmap_t, obj:$ptr) returns($ptr);

axiom (forall S:$state, p:$ptr :: {$owner(S, p)}
   $owner(S, p) == $me() ==> $thread_owner(S, p) == $me());
axiom (forall S:$state, p:$ptr :: {$owner(S, p)}
   $thread_owner(S, p) == $thread_owner(S, $owner(S, p)));
*/

function $instantiate_st(s:$status) returns(bool);
axiom (forall S1:$state, S2:$state, p:$ptr :: {$st(S2, p), $call_transition(S1, S2)}
  $call_transition(S1, S2) ==>
  $instantiate_st($st(S1, p)));

axiom (forall S1:$state, S2:$state, p:$ptr :: {$mem(S2, p), $call_transition(S1, S2)}
  $call_transition(S1, S2) ==>
  $instantiate_int($mem(S1, p)));

/*
axiom (forall S:$state, p:$ptr :: {$thread_owner(S, p), $is_primitive($typ(p))}
  $instantiate_st($st(S, $emb(S, p))));
axiom (forall S:$state, p:$ptr :: {$thread_owner(S, p)}
  $instantiate_st($st(S, p)));
*/

/*
type $rootmap;
function $select.root($rootmap, $ptr) returns($ptr);
function $store.root($rootmap, $ptr, $ptr) returns($rootmap);
axiom (forall M:$rootmap, p:$ptr, v:$ptr :: {:weight 0}
  $select.root($store.root(M, p, v), p) == v);
axiom (forall M:$rootmap, p:$ptr, q:$ptr, v:$ptr :: {:weight 0}
  p != q ==> $select.root($store.root(M, p, v), q) == $select.root(M, q));

function $get_root(S:$state) returns($rootmap);
function {:inline true} $root(S:$state, p:$ptr) returns($ptr)
  { $select.root($get_root(S), p) }
*/

// for model reading
function $is_domain_root(S:$state, p:$ptr) returns(bool)
  { true }

function $in_wrapped_domain(S:$state, p:$ptr) returns(bool)
  { (exists q:$ptr :: {$set_in2(p, $ver_domain($read_version(S, q)))} 
            $set_in(p, $ver_domain($read_version(S, q)))
         && $wrapped(S, q, $typ(q)) 
         && $is_domain_root(S, q)
         ) }

function {:inline true} $thread_local_np(S:$state, p:$ptr) returns(bool)
  { !$is_primitive_ch($typ(p)) && 
    ($owner(S, p) == $me() || $in_wrapped_domain(S, p)) 
//     ($wrapped(S, $root(S, p), $typ($root(S, p))) && $set_in(p, $domain(S, $root(S, p)))))
  }

// required for reading
function $thread_local(S:$state, p:$ptr) returns(bool)
  { $typed(S, p) &&
    (($is_primitive_ch($typ(p)) && (!$is_volatile(S, p) || !$closed(S, $emb(S, p))) && $thread_local_np(S, $emb(S, p))) ||
     $thread_local_np(S, p)) }

function {:inline true} $thread_local2(S:$state, #p:$ptr, #t:$ctype) returns(bool)
  { $is(#p, #t) && $thread_local(S, #p) }

 

// ----------------------------------------------------------------------------
// Boogie/Z3 hacks
// ----------------------------------------------------------------------------

// Used as a trigger when we don't want the quantifier to be instantiated at all
//   (for example we just assert it or have it as a precondition)
// It could be any symbol that is not used anywhere else.
function $dont_instantiate($ptr) returns(bool);
function $dont_instantiate_int(int) returns(bool);
function $dont_instantiate_state($state) returns(bool);

// Voodoo, don't read it.
function $instantiate_int(int) returns(bool);
function $instantiate_bool(bool) returns(bool);
function $instantiate_ptr($ptr) returns(bool);
function $instantiate_ptrset($ptrset) returns(bool);
// Voodoo end.

// ----------------------------------------------------------------------------
// ownership protocol
// ----------------------------------------------------------------------------
function {:inline true} $inv(#s1:$state, #p:$ptr, typ:$ctype) returns (bool)
  { $inv2(#s1, #s1, #p, typ) }

function {:inline true} $inv2nt(S1:$state, S2:$state, p:$ptr) returns (bool)
  { $inv2(S1, S2, p, $typ(p)) }

function $imply_inv(#s1:$state, #p:$ptr, typ:$ctype) returns (bool);
axiom (forall #s1:$state, #p:$ptr, typ:$ctype :: {$inv(#s1, #p, typ)}
  $imply_inv(#s1, #p, typ) ==> $inv(#s1, #p, typ));

// We generate axioms like:
//   inv2(S1,S2,p,T) <==> invariant of T
// for each struct/union T.
function $inv2(#s1:$state, #s2:$state, #p:$ptr, typ:$ctype) returns (bool);

// used in admissibility check
function {:inline true} $inv2_when_closed(#s1:$state, #s2:$state, #p:$ptr, typ:$ctype) returns (bool)
  { (!$closed(#s1, #p) && !$closed(#s2, #p)) || ($inv2(#s1, #s2, #p, typ) && $nonvolatile_spans_the_same(#s1, #s2, #p, typ)) }

function {:weight 0} $sequential(#s1:$state, #s2:$state, #p:$ptr, #t:$ctype) returns (bool)
  { $closed(#s1, #p) && $closed(#s2, #p) ==> $spans_the_same(#s1, #s2, #p, #t) }

function {:weight 0} $depends(#s1:$state, #s2:$state, #dependant:$ptr, #this:$ptr) returns (bool)
  { $spans_the_same(#s1, #s2, #this, $typ(#this)) || 
    $inv2_when_closed(#s1, #s2, #dependant, $typ(#dependant)) ||
    $is_threadtype($typ(#dependant)) }

function {:weight 0} $spans_the_same(#s1:$state, #s2:$state, #p:$ptr, #t:$ctype) returns (bool)
  {    $read_version(#s1, #p) == $read_version(#s2, #p)
    && $owns(#s1, #p) == $owns(#s2, #p)
    && $ts(#s1, #p) == $ts(#s2, #p)
    && $state_spans_the_same(#s1, #s2, #p, #t) }

// excludes any meta state, includes only primitive fields, not embedded structs
function $state_spans_the_same(#s1:$state, #s2:$state, #p:$ptr, #t:$ctype) returns (bool);

function {:weight 0} $nonvolatile_spans_the_same(#s1:$state, #s2:$state, #p:$ptr, #t:$ctype) returns (bool)
  {    $read_version(#s1, #p) == $read_version(#s2, #p)
    && $ts(#s1, #p) == $ts(#s2, #p)
    && $state_nonvolatile_spans_the_same(#s1, #s2, #p, #t) }

// excludes any meta state, includes only non-volatile primitive fields, not embedded structs
function $state_nonvolatile_spans_the_same(#s1:$state, #s2:$state, #p:$ptr, #t:$ctype) returns (bool);

// $in_extent_of(S, p1, p2) means that p1 is a pointer nested (at any level, including 0!) in p2
// $in_full_extent_of(...) assumes it can be any of the union fields, not only the selected one
function {:inline true} $in_extent_of(S:$state, #p1:$ptr, #p2:$ptr) returns(bool)
  { $set_in(#p1, $extent(S, #p2)) }
function {:inline true} $in_full_extent_of(#p1:$ptr, #p2:$ptr) returns(bool)
  { $set_in(#p1, $full_extent(#p2)) }

function $extent_mutable(S:$state, p:$ptr) returns(bool);
function $extent_is_fresh(S1:$state, S2:$state, p:$ptr) returns(bool);
function $extent_zero(S:$state, p:$ptr) returns(bool);

axiom (forall T:$ctype :: {$is_primitive(T)}
  $is_primitive(T) ==> 
    (forall r:int, p:$ptr :: {$in_full_extent_of(p, $ptr(T, r))}
      $in_full_extent_of(p, $ptr(T, r)) <==> p == $ptr(T, r)) &&
    (forall r:int, S:$state :: {$extent_mutable(S, $ptr(T, r))}
      $extent_mutable(S, $ptr(T, r)) <==> $mutable(S, $ptr(T, r))));

axiom (forall T:$ctype :: {$is_primitive(T)}
  $is_primitive(T) ==> 
    (forall S:$state, r:int, p:$ptr :: {$in_extent_of(S, p, $ptr(T, r))}
      $in_extent_of(S, p, $ptr(T, r)) <==> p == $ptr(T, r)));
      
axiom (forall S:$state, T:$ctype, sz:int, r:int :: {$extent_mutable(S, $ptr($array(T, sz), r))}
  $extent_mutable(S, $ptr($array(T, sz), r)) <==>
    $mutable(S, $ptr($array(T, sz), r)) &&
    (forall i:int :: {$extent_mutable(S, $idx($ptr(T, r), i, T))}
       0 <= i && i < sz ==> $extent_mutable(S, $idx($ptr(T, r), i, T)))
);

axiom (forall T:$ctype :: {$is_primitive(T)}
  $is_primitive(T) ==>
      (forall S:$state, r:int :: {$extent_zero(S, $ptr(T,r))}
       $extent_zero(S, $ptr(T,r)) <==> $mem(S, $ptr(T,r)) == 0 ));

axiom (forall S:$state, T:$ctype, sz:int, r:int :: {$extent_zero(S, $ptr($array(T, sz), r))}
  $extent_zero(S, $ptr($array(T, sz), r)) <==>
    (forall i:int :: {$idx($ptr(T, r), i, T)}
       0 <= i && i < sz ==> $extent_zero(S, $idx($ptr(T, r), i, T)))
);


function {:inline true} $forall_inv2_when_closed(#s1:$state, #s2:$state) returns (bool)
 { (forall #p:$ptr :: {$closed(#s1,#p)} {$closed(#s2,#p)} $inv2_when_closed(#s1,#s2,#p,$typ(#p)))
 }

function $function_entry($state) returns(bool);

function $full_stop($state) returns(bool);
function {:inline true} $full_stop_ext(t:$token, S:$state) returns(bool)
  { $good_state_ext(t, S) && $full_stop(S) }

function $file_name_is(id:int, tok:$token) returns(bool);

axiom (forall S:$state :: {$function_entry(S)}
  $function_entry(S) ==> $full_stop(S) && $current_timestamp(S) >= 0);

axiom (forall S:$state :: {$full_stop(S)}
  $full_stop(S) ==> $good_state(S) && $invok_state(S));

axiom (forall S:$state :: {$invok_state(S)}
  $invok_state(S) ==> $good_state(S));

function {:inline true} $closed_is_transitive(S:$state) returns (bool)
  { 
    (forall #p:$ptr,#q:$ptr :: {$set_in(#p, $owns(S, #q))}
      $good_state(S) &&
      $set_in(#p, $owns(S, #q)) && $closed(S, #q) ==> $closed(S, #p)  && $ref(#p) != 0)
 } 
        
// ----------------------------------------------------------------------------
// 
// ----------------------------------------------------------------------------

function $call_transition(S1:$state, S2:$state) returns(bool);

// Assumed after each meta/state update, means that the meta corresponds to the state
// and where in the source did the update happen.
function $good_state_ext(id:$token, S:$state) returns(bool);
axiom (forall id:$token, S:$state :: {$good_state_ext(id, S)}
  $good_state_ext(id, S) ==> $good_state(S));

// ----------------------------------------------------------------------------
// model-viewer support
// ----------------------------------------------------------------------------

function $local_value_is(S1:$state, pos:$token, local_name:$token, val:int, t:$ctype) returns(bool);
function $local_value_is_ptr(S1:$state, pos:$token, local_name:$token, val:$ptr, t:$ctype) returns(bool);
function $read_ptr_m(S:$state, p:$ptr, t:$ctype) returns($ptr);

// for easier model viewing
axiom (forall S:$state, r:int, t:$ctype :: {$ptr(t, $mem(S, $ptr($ptr_to(t), r)))}
  $ptr(t, $mem(S, $ptr($ptr_to(t), r))) == $read_ptr_m(S, $ptr($ptr_to(t), r), t));

axiom (forall S:$state, r:int, t:$ctype :: {$ptr(t, $mem(S, $ptr($spec_ptr_to(t), r)))}
  $ptr(t, $mem(S, $ptr($spec_ptr_to(t), r))) == $read_ptr_m(S, $ptr($spec_ptr_to(t), r), t));

function $type_code_is(x:int, tp:$ctype) returns(bool);
// idx==0 - return type
function $function_arg_type(fnname:$pure_function, idx:int, tp:$ctype) returns(bool);

// -------------------------------------------------------------------------------------
// the domain thing
// -------------------------------------------------------------------------------------

type $version;
function $ver_domain($version) returns($ptrset);

function {:weight 0} $read_version(S:$state, p:$ptr) returns($version)
  { $int_to_version($mem(S, p)) }

function {:weight 0} $domain(S:$state, p:$ptr) returns($ptrset)
  { $ver_domain($read_version(S, p)) }

function $in_domain(S:$state, p:$ptr, q:$ptr) returns(bool);
function $in_vdomain(S:$state, p:$ptr, q:$ptr) returns(bool);

function $in_domain_lab(S:$state, p:$ptr, q:$ptr, l:$label) returns(bool);
function $in_vdomain_lab(S:$state, p:$ptr, q:$ptr, l:$label) returns(bool);
function $inv_lab(S:$state, p:$ptr, l:$label) returns(bool);

axiom (forall S:$state, p:$ptr, q:$ptr, l:$label :: {:weight 0} {$in_domain_lab(S, p, q, l)}
  $in_domain_lab(S, p, q, l) ==> $inv_lab(S, p, l));

axiom (forall S:$state, p:$ptr, q:$ptr, l:$label :: {:weight 0} {$in_domain_lab(S, p, q, l)}
  $in_domain_lab(S, p, q, l) <==> $in_domain(S, p, q));

axiom (forall S:$state, p:$ptr, q:$ptr, l:$label :: {:weight 0} {$in_vdomain_lab(S, p, q, l)}
  $in_vdomain_lab(S, p, q, l) ==> $inv_lab(S, p, l));

axiom (forall S:$state, p:$ptr, q:$ptr, l:$label :: {:weight 0} {$in_vdomain_lab(S, p, q, l)}
  $in_vdomain_lab(S, p, q, l) <==> $in_vdomain(S, p, q));

function {:inline true} $dom_thread_local(S:$state, #p:$ptr) returns(bool)
  { $typed(S, #p) && !$is_volatile(S, #p) }

axiom (forall S:$state, p:$ptr, q:$ptr :: {:weight 0} {$in_domain(S, p, q)}
  $in_domain(S, p, q) ==> 
       $set_in(p, $domain(S, q)) 
    && $closed(S, p) 
    && (forall r:$ptr :: {$set_in(r, $owns(S, p))} 
             !$has_volatile_owns_set($typ(p)) && $set_in(r, $owns(S, p)) ==> 
                        $set_in2(r, $ver_domain($read_version(S, q))))
  );

axiom (forall S:$state, p:$ptr :: {$in_domain(S, p, p)}
  $full_stop(S) && $wrapped(S, p, $typ(p)) ==> $in_domain(S, p, p));

/*
axiom (forall S:$state, p:$ptr, q:$ptr, r:$ptr ::
  { $in_domain(S, q, p), $in_domain(S, r, p) }
  $in_domain(S, q, p) && $set_in0(r, $owns(S, q)) ==> $in_domain(S, r, p) && $set_in0(r, $owns(S, q)));
*/

axiom (forall S:$state, p:$ptr, q:$ptr :: 
  {:weight 0} { $in_domain(S, q, p) }
  $full_stop(S) && $set_in(q, $domain(S, p)) ==> $in_domain(S, q, p));

axiom (forall S:$state, p:$ptr, q:$ptr, r:$ptr :: 
  {:weight 0} { $set_in(q, $domain(S, p)), $in_domain(S, r, p) }
  !$has_volatile_owns_set($typ(q)) &&
  $set_in(q, $domain(S, p)) && $set_in0(r, $owns(S, q)) ==> $in_domain(S, r, p) && $set_in0(r, $owns(S, q)));

axiom (forall S:$state, p:$ptr, q:$ptr, r:$ptr :: 
  {:weight 0} { $set_in(q, $domain(S, p)), $in_vdomain(S, r, p) }
  $has_volatile_owns_set($typ(q)) && 
  $set_in(q, $domain(S, p)) &&
  (forall S1:$state :: 
      $inv(S1, q, $typ(q)) && 
      $read_version(S1, p) == $read_version(S, p) &&
      $domain(S1, p) == $domain(S, p)
      ==> $set_in0(r, $owns(S1, q)))
    ==> $in_vdomain(S, r, p) && $set_in0(r, $owns(S, q)));

axiom (forall S:$state, p:$ptr, q:$ptr :: 
  {:weight 0} { $in_vdomain(S, p, q) } $in_vdomain(S, p, q) ==> $in_domain(S, p, q));

function $fetch_from_domain(v:$version, p:$ptr) returns(int);

axiom (forall S:$state, p:$ptr, d:$ptr, f:$field ::
  { $set_in(p, $domain(S, d)), $is_primitive_non_volatile_field(f), $mem(S, $dot(p, f)) }
  $set_in(p, $domain(S, d)) && $is_primitive_non_volatile_field(f) ==> 
    $mem(S, $dot(p, f)) == $fetch_from_domain($read_version(S, d), $dot(p, f)));

axiom (forall S:$state, p:$ptr, d:$ptr :: 
  { $full_stop(S), $set_in(p, $domain(S, d)), $st(S, p) }
  { $full_stop(S), $set_in(p, $domain(S, d)), $ts(S, p) }
  $full_stop(S) && $set_in(p, $domain(S, d)) ==> 
    $dom_thread_local(S, p));

axiom (forall S:$state, p:$ptr, d:$ptr, f:$field :: 
  { $set_in(p, $domain(S, d)), $is_primitive_non_volatile_field(f), $owner(S, $dot(p, f)) }
  { $set_in(p, $domain(S, d)), $is_primitive_non_volatile_field(f), $ts(S, $dot(p, f)) }
  $full_stop(S) && $set_in(p, $domain(S, d)) && $is_primitive_non_volatile_field(f) ==> 
    $dom_thread_local(S, $dot(p, f)));

axiom (forall S:$state, p:$ptr, d:$ptr, f:$field, sz:int, i:int, t:$ctype :: 
  { $set_in(p, $domain(S, d)), $is_primitive_embedded_array(f, sz), $mem(S, $idx($dot(p, f), i, t)) }
  $full_stop(S) && $set_in(p, $domain(S, d)) && $is_primitive_embedded_array(f, sz) && 0 <= i && i < sz ==> 
    $mem(S, $idx($dot(p, f), i, t)) == $fetch_from_domain($read_version(S, d), $idx($dot(p, f), i, t)));

axiom (forall S:$state, p:$ptr, d:$ptr, f:$field, sz:int, i:int, t:$ctype :: 
  { $set_in(p, $domain(S, d)), $is_primitive_embedded_array(f, sz), $ts(S, $idx($dot(p, f), i, t)) }
  { $set_in(p, $domain(S, d)), $is_primitive_embedded_array(f, sz), $owner(S, $idx($dot(p, f), i, t)) }
  $full_stop(S) && $set_in(p, $domain(S, d)) && $is_primitive_embedded_array(f, sz) && 0 <= i && i < sz ==> 
    $dom_thread_local(S, $idx($dot(p, f), i, t)));

axiom (forall S:$state, r:int, d:$ptr, sz:int, i:int, t:$ctype :: 
  { $set_in($ptr($array(t,sz), r), $domain(S, d)), $ts(S, $idx($ptr(t,r), i, t)), $is_primitive(t) }
  { $set_in($ptr($array(t,sz), r), $domain(S, d)), $owner(S, $idx($ptr(t,r), i, t)), $is_primitive(t) }
  $full_stop(S) && 
  $is_primitive(t) &&
  $set_in($ptr($array(t,sz), r), $domain(S, d)) &&
  0 <= i && i < sz ==> 
    $dom_thread_local(S, $idx($ptr(t,r), i, t)));

axiom (forall S:$state, r:int, d:$ptr, sz:int, i:int, t:$ctype :: 
  { $set_in($ptr($array(t,sz), r), $domain(S, d)), $mem(S, $idx($ptr(t,r), i, t)), $is_primitive(t) }
  $full_stop(S) && 
  $is_primitive(t) &&
  $set_in($ptr($array(t,sz), r), $domain(S, d)) &&
  0 <= i && i < sz ==> 
    $mem(S, $idx($ptr(t,r), i, t)) == $fetch_from_domain($read_version(S, d), $idx($ptr(t,r), i, t)));

axiom (forall S:$state, p:$ptr, f:$field, sz:int, i:int, t:$ctype ::
  {$is_primitive_embedded_volatile_array(f, sz, t), $is_volatile(S, $idx($dot(p, f), i, t))}
  $good_state(S) && $is_primitive_embedded_volatile_array(f, sz, t) && 0 <= i && i < sz ==>
    $is_volatile(S, $idx($dot(p, f), i, t)));

/*
axiom (forall S1:$state, S2:$state, p:$ptr :: 
  {$domain(S1, p), $full_stop(S2)}
    $instantiate_ptrset($domain(S1, p)) && $instantiate_ptrset($domain(S2, p)));
*/

axiom (forall p:$ptr, S1:$state, S2:$state, q:$ptr :: 
  {:weight 0} {$set_in(q, $domain(S1, p)), $call_transition(S1, S2)}
    $instantiate_bool($set_in(q, $domain(S2, p))));
    
axiom (forall p:$ptr, S1:$state, S2:$state, q:$ptr :: 
  {:weight 0} {$set_in(q, $ver_domain($read_version(S1, p))), $call_transition(S1, S2)}
    $instantiate_bool($set_in(q, $ver_domain($read_version(S2, p)))));

function $in_claim_domain(p:$ptr, c:$ptr) returns(bool);
axiom (forall p:$ptr, c:$ptr :: {$in_claim_domain(p, c)}
  (forall s:$state :: {$dont_instantiate_state(s)} $valid_claim(s, c) ==> $closed(s, p)) ==>
    $in_claim_domain(p, c));

function {:weight 0} $by_claim(S:$state, c:$ptr, obj:$ptr, ptr:$ptr) returns($ptr)
  { ptr }

function $claim_version($ptr) returns($version);

axiom (forall S:$state, p:$ptr, c:$ptr, f:$field :: 
  {$in_claim_domain(p, c), $mem(S, $dot(p, f))}
  {$by_claim(S, c, p, $dot(p, f))}
  $good_state(S) &&
  $closed(S, c) && $in_claim_domain(p, c) && $is_primitive_non_volatile_field(f) ==> 
    $in_claim_domain(p, c) &&
    $mem(S, $dot(p, f)) == $fetch_from_domain($claim_version(c), $dot(p, f))
    );

axiom (forall S:$state, p:$ptr, c:$ptr, f:$field, i:int, sz:int, t:$ctype :: 
  {$valid_claim(S, c), $in_claim_domain(p, c), $mem(S, $idx($dot(p, f), i, t)), $is_primitive_embedded_array(f, sz)}
  {$by_claim(S, c, p, $idx($dot(p, f), i, t)), $is_primitive_embedded_array(f, sz)}
  $good_state(S) &&
  $closed(S, c) && $in_claim_domain(p, c) && $is_primitive_embedded_array(f, sz) && 0 <= i && i < sz ==> 
    $mem(S, $idx($dot(p, f), i, t)) == $fetch_from_domain($claim_version(c), $idx($dot(p, f), i, t))
    );

axiom (forall S:$state, p:$ptr, c:$ptr, i:int, sz:int, t:$ctype :: 
  {$valid_claim(S, c), $in_claim_domain($as_array(p, t, sz), c), $mem(S, $idx(p, i, t)), $is_primitive(t) }
  {$by_claim(S, c, p, $idx(p, i, t)), $is_primitive(t), $is_array(S,p,t,sz) }
  $good_state(S) &&
  $closed(S, c) && $in_claim_domain($as_array(p, t, sz), c) && $is_primitive(t) && 0 <= i && i < sz ==> 
    $mem(S, $idx(p, i, t)) == $fetch_from_domain($claim_version(c), $idx(p, i, t))
    );

procedure $write_ref_cnt(p:$ptr, v:int);
  modifies $s;
  ensures old($typemap($s)) == $typemap($s);
  ensures old($memory($s)) == $memory($s);
  ensures (forall q:$ptr :: {$st($s, q)} q == p || $st_eq(old($s), $s, q));
  ensures old($owner($s, p)) == $owner($s, p);
  ensures old($owns($s, p)) == $owns($s, p);
  ensures old($closed($s, p)) == $closed($s, p);
  ensures old($timestamp($s, p)) == $timestamp($s, p);
  ensures $ref_cnt($s, p) == v;
  ensures $timestamp_post_strict(old($s), $s);
  ensures $good_state($s);

// -------------------------------------------------------------------------------------
// the volatile domain
// -------------------------------------------------------------------------------------

type $vol_version;

function {:weight 0} $read_vol_version(S:$state, p:$ptr) returns($vol_version)
  { $int_to_vol_version($mem(S, p)) }

function $fetch_from_vv(v:$vol_version, p:$ptr) returns(int);

function {:inline true} $fetch_vol_field(S:$state, p:$ptr, f:$field) returns(int)
  { $fetch_from_vv($read_vol_version(S, p), $dot(p, f)) }

// the approver always needs to approve itself and be of obj_t type
function $is_approved_by(t:$ctype, approver:$field, subject:$field) returns(bool);

axiom (forall S:$state, r:int, t:$ctype, approver:$field, subject:$field ::
  { $is_approved_by(t, approver, subject), $mem(S, $dot($ptr(t, r), subject)) }
  $full_stop(S) &&
  $is_approved_by(t, approver, subject) &&
  $closed(S, $ptr(t, r)) &&
  ($int_to_ptr($mem(S, $dot($ptr(t, r), approver))) == $me() ||
   $int_to_ptr($fetch_vol_field(S, $ptr(t, r), approver)) == $me()) ==>
    $mem(S, $dot($ptr(t, r), subject)) == $fetch_vol_field(S, $ptr(t, r), subject)
    );

function {:inline true} $inv_is_approved_by_ptr(S1:$state, S2:$state, this:$ptr, approver:$ptr, subject:$field) returns(bool)
{
  $mem_eq(S1, S2, $dot(this, subject)) || 
  $ref(approver) == 0 ||
  (!$is_threadtype($typ(approver)) && $inv2nt(S1, S2, approver) ) ||
  ($is_threadtype($typ(approver)) && $read_vol_version(S1, this) != $read_vol_version(S2, this) )
}

function {:inline true} $inv_is_approved_by(S1:$state, S2:$state, this:$ptr, approver:$field, subject:$field) returns(bool)
{
  $inv_is_approved_by_ptr(S1, S2, this, $int_to_ptr($mem(S1, $dot(this, approver))), subject)
}

function $is_owner_approved(t:$ctype, subject:$field) returns(bool);

axiom (forall S:$state, r:int, t:$ctype, subject:$field ::
  { $is_owner_approved(t, subject), $mem(S, $dot($ptr(t, r), subject)) }
  $full_stop(S) &&
  $closed(S, $ptr(t, r)) &&
  $is_owner_approved(t, subject) &&
  $owner(S, $ptr(t, r)) == $me() ==>
    $mem(S, $dot($ptr(t, r), subject)) == $fetch_vol_field(S, $ptr(t, r), subject));

axiom (forall S1:$state, S2:$state, r:int, t:$ctype, subject:$field ::
  { $is_owner_approved(t, subject), $post_unwrap(S1, S2), $mem(S1, $dot($ptr(t, r), subject)) }
  $instantiate_int($mem(S2, $dot($ptr(t, r), subject))));

function {:inline true} $inv_is_owner_approved(S1:$state, S2:$state, this:$ptr, subject:$field) returns(bool)
{
  $inv_is_approved_by_ptr(S1, S2, this, $owner(S1, this), subject)
}

procedure $bump_volatile_version(p:$ptr);
  modifies $s;
  ensures $typemap($s) == $typemap(old($s));
  ensures $statusmap($s) == $statusmap(old($s));
  ensures (forall q:$ptr :: {$mem($s, q)} q == p || $mem_eq(old($s), $s, q));
  ensures $read_version(old($s), p) == $read_version($s, p);
  ensures $read_vol_version(old($s), p) != $read_vol_version($s, p);
  ensures $timestamp_post_strict(old($s), $s);

// ----------------------------------------------------------------------------
// System invariants
// ----------------------------------------------------------------------------

axiom (forall S:$state, p:$ptr, q:$ptr :: {$set_in(p, $owns(S, q)), $is_non_primitive($typ(p))}
  $good_state(S) &&
  $closed(S, q) && $is_non_primitive($typ(p)) ==>
      ($set_in(p, $owns(S, q)) <==> $owner(S, p) == q));

// TODO
// this one is iffy
axiom (forall #s1:$state, #s2:$state, #p:$ptr, #t:$ctype :: 
  {$is_arraytype(#t), $inv2(#s1, #s2, #p, #t)}
  $is_arraytype(#t) && $typ(#p) == #t ==> 
    ($inv2(#s1, #s2, #p, #t) == $typed(#s2, #p) && $sequential(#s1, #s2, #p, #t)));

axiom (forall S:$state, #r:int, #t:$ctype :: {$owns(S, $ptr(#t, #r)), $is_arraytype(#t)}
  $good_state(S) ==>
    $is_arraytype(#t) ==> $owns(S, $ptr(#t, #r)) == $set_empty());

axiom (forall S:$state, #p:$ptr, #t:$ctype :: {$inv(S, #p, #t)}
  $invok_state(S) && $closed(S, #p) ==> $inv(S, #p, #t));

axiom (forall S:$state :: {$good_state(S)}
  $good_state(S) ==> $closed_is_transitive(S));

axiom (forall S:$state, #p:$ptr :: {$closed(S,#p)}
  $closed(S, #p) ==> $typed(S,#p));

// ----------------------------------------------------------------------------
// Custom admissibility checks
// ----------------------------------------------------------------------------

function $good_for_admissibility(S:$state) returns(bool);
function $good_for_post_admissibility(S:$state) returns(bool);

function {:inline true} $stuttering_pre(S:$state, p:$ptr) returns(bool)
  { (forall #q: $ptr :: {$st(S, #q)} $closed(S, #q) ==> $inv(S, #q, $typ(#q))) &&
    $good_for_admissibility(S)
  }

function {:inline true} $admissibility_pre(S:$state, p:$ptr) returns(bool)
  { $closed(S, p) && $inv(S, p, $typ(p)) && $stuttering_pre(S, p) }

procedure $havoc_others(p:$ptr, t:$ctype);
  modifies $s;
  // TOKEN: the state was not modified
  requires $good_for_admissibility($s);
  ensures $is_stuttering_check() || $spans_the_same(old($s), $s, p, t);
  ensures $nonvolatile_spans_the_same(old($s), $s, p, t);
  ensures $closed($s, p);
  ensures $typed($s, p);
  ensures $closed_is_transitive($s);
  ensures $good_state($s);
  ensures $good_for_post_admissibility($s);
  ensures (forall #q: $ptr :: {$st(old($s), #q)} {$st($s, #q)} 
    ($closed(old($s), #q) || $closed($s, #q)) && 
    (!$spans_the_same(old($s), $s, #q, $typ(#q)) || $closed(old($s), #q) != $closed($s, #q)) 
      ==> ($inv2(old($s), $s, #q, $typ(#q)) && $nonvolatile_spans_the_same(old($s), $s, #q, $typ(#q))));
  ensures (forall #q:$ptr :: {$set_in(#q, $owns(old($s), p))}
            $set_in(#q, $owns(old($s), p)) ==>
              $ref_cnt(old($s), #q) == $ref_cnt($s, #q));
  ensures $timestamp_post(old($s), $s);

// inferred as free invariant for loops that call only functions that don't write anything
function {:inline true} $mutable_increases(s1:$state, s2:$state) returns(bool)
  { (forall p:$ptr :: {$st(s2, p)} {$ts(s2, p)}
       $mutable(s1, p) ==> $mutable(s2, p)) }
function {:inline true} $meta_eq(s1:$state, s2:$state) returns(bool)
  { $typemap(s1) == $typemap(s2) && $statusmap(s1) == $statusmap(s2) }
    

// ----------------------------------------------------------------------------
// Can-unwrap checks
// ----------------------------------------------------------------------------

function $is_stuttering_check() returns(bool);
function $is_unwrap_check() returns(bool);
function {:inline true} $is_admissibility_check() returns(bool)
  { !$is_stuttering_check() && !$is_unwrap_check() }

function $good_for_pre_can_unwrap(S:$state) returns(bool);
function $good_for_post_can_unwrap(S:$state) returns(bool);

function {:inline true} $unwrap_check_pre(S:$state, p:$ptr) returns(bool)
  { $wrapped(S, p, $typ(p)) && 
    (! $is_claimable($typ(p)) || $ref_cnt(S, p) == 0) &&
    $inv(S, p, $typ(p)) &&
    (forall #q: $ptr :: {$st(S, #q)} $closed(S, #q) ==> $inv(S, #q, $typ(#q))) &&
    $good_for_pre_can_unwrap(S)
  }

procedure $unwrap_check(#l:$ptr);
  modifies $s;
  // TOKEN: the state was not modified
  requires $good_for_pre_can_unwrap($s);
  ensures $good_state($s);
  ensures $good_for_post_can_unwrap($s);

  // from $unwrap(...):
  ensures $mutable($s, #l);
  ensures $spans_the_same(old($s), $s, #l, $typ(#l));
  ensures (forall #p:$ptr :: {$set_in(#p, $owns(old($s), #l))}
    $set_in(#p, $owns(old($s), #l)) ==> 
      $typed(old($s), #p) &&
      $wrapped($s, #p, $typ(#p)) && $timestamp_is_now($s, #p) && $is_non_primitive($typ(#p)));
  ensures (forall #p:$ptr :: {$set_in(#p, $owns(old($s), #l)), $is_claimable($typ(#p))}
    $set_in(#p, $owns(old($s), #l)) ==> 
      ($is_claimable($typ(#p)) ==> 
         old($ref_cnt($s, #p)) == $ref_cnt($s, #p) ));
  ensures $timestamp_is_now($s, #l);
  ensures $typemap(old($s)) == $typemap($s);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    #p == #l || 
    ($nested(old($s), #p) && $set_in(#p, $owns(old($s), #l))) || 
    $st($s, #p) == $st(old($s), #p));
  ensures (exists #x:int :: $memory($s) == $store.mem($memory(old($s)), #l, #x));
  ensures $timestamp_post_strict(old($s), $s);


// ----------------------------------------------------------------------------
// Procedures
// ----------------------------------------------------------------------------


procedure $write_int(p:$ptr, v:int);
  modifies $s;
  ensures $typemap($s) == $typemap(old($s));
  ensures $statusmap($s) == $statusmap(old($s));
  ensures $memory($s) == $store.mem($memory(old($s)), p, v);
  ensures $timestamp_post_strict(old($s), $s);

function $update_int(S:$state, p:$ptr, v:int) returns ($state);
axiom (forall S:$state, p:$ptr, v:int :: {$update_int(S, p, v)}
  $typemap($update_int(S, p, v)) == $typemap(S) &&
  $statusmap($update_int(S, p, v)) == $statusmap(S) &&
  $memory($update_int(S, p, v)) == $store.mem($memory(S), p, v) &&
  $timestamp_post_strict(S, $update_int(S, p, v)));

function {:inline true} $timestamp_is_now(S:$state, p:$ptr) returns(bool)
  { $timestamp(S, p) == $current_timestamp(S) }

function {:inline true} $now_writable(S:$state, p:$ptr) returns(bool)
  { $timestamp_is_now(S, p) && $mutable(S, p) }

function {:inline true} $timestamp_post(M1:$state, M2:$state) returns(bool)
  { $current_timestamp(M1) <= $current_timestamp(M2) &&
    (forall p:$ptr :: {:weight 0} {$timestamp(M2, p)} $timestamp(M1, p) <= $timestamp(M2, p)) &&
    $call_transition(M1, M2)
  }

function {:inline true} $timestamp_post_strict(M1:$state, M2:$state) returns(bool)
  { $current_timestamp(M1) < $current_timestamp(M2) &&
    (forall p:$ptr :: {:weight 0} {$timestamp(M2, p)} $timestamp(M1, p) <= $timestamp(M2, p)) &&
    $call_transition(M1, M2)
  }

function $pre_wrap($state) returns(bool);
function $pre_unwrap($state) returns(bool);
function $pre_static_wrap($state) returns(bool);
function $pre_static_unwrap($state) returns(bool);

function {:inline true} $unwrap_post(S0:$state, S:$state, #l:$ptr, #p:$ptr) returns(bool)
  { $typed(S0, #p) &&
    $wrapped(S, #p, $typ(#p)) && 
    $timestamp_is_now(S, #p) && 
    $is_non_primitive($typ(#p)) &&
    $set_in(#p, $owns(S0, #l)) &&
    $nested_in(S0, #p, #l)
    }

function {:inline true} $unwrap_post_claimable(S0:$state, S:$state, #l:$ptr, #p:$ptr) returns(bool)
  { $unwrap_post(S0, S, #l, #p) && 
    ($is_claimable($typ(#p)) ==> $ref_cnt(S0, #p) == $ref_cnt(S, #p)) }

function {:inline true} {:expand true} $keeps(S:$state, #l:$ptr, #p:$ptr) returns(bool)
  { $set_in(#p, $owns(S, #l)) }

function $expect_unreachable() returns(bool);

function $taken_over(S:$state, #l:$ptr, #p:$ptr) returns($status);
function $take_over(S:$state, #l:$ptr, #p:$ptr) returns($state);
axiom (forall S:$state, l:$ptr, p:$ptr :: {$take_over(S, l, p)}
  $is_non_primitive_ch($typ(l)) ==>
// Breaking ties on memory and typemap prevents creation of additional states
// where the prover could trigger.
//  $memory($take_over(S, l, p)) == $memory(S) &&
//  $typemap($take_over(S, l, p)) == $typemap(S) &&
  $statusmap($take_over(S, l, p)) == $store.sm($statusmap(S), p, $taken_over(S, l, p)) &&
  $closed($take_over(S, l, p), p) &&
  $owner($take_over(S, l, p), p) == l &&
  $ref_cnt($take_over(S, l, p), p) == $ref_cnt(S, p) &&
  true
  );


function $released(S:$state, #l:$ptr, #p:$ptr) returns($status);
function $release(S0:$state, S:$state, #l:$ptr, #p:$ptr) returns($state);
axiom (forall S0:$state, S:$state, l:$ptr, p:$ptr :: {$release(S0, S, l, p)}
// Likewise.
//  $memory($release(S0, S, l, p)) == $memory(S) &&
//  $typemap($release(S0, S, l, p)) == $typemap(S) &&
  $statusmap($release(S0, S, l, p)) == $store.sm($statusmap(S), p, $released(S, l, p)) &&
  $closed($release(S0, S, l, p), p) &&
  $owner($release(S0, S, l, p), p) == $me() &&
  $ref_cnt($release(S0, S, l, p), p) == $ref_cnt(S, p) &&
  $timestamp($release(S0, S, l, p), p) == $current_timestamp(S0) &&
  true
  );

function $post_unwrap(S1:$state, S2:$state) returns(bool);

procedure $static_unwrap(#l:$ptr, S:$state);
  // writes #l
  modifies $s;
  // TOKEN: the object has no outstanding claims
  requires ! $is_claimable($typ(#l)) || $ref_cnt($s, #l) == 0;
  // TOKEN: OOPS: pre_static_unwrap holds
  requires $pre_static_unwrap($s);
  ensures $mutable($s, #l);
  ensures $owns(old($s), #l) == $owns($s, #l);
  ensures $timestamp_is_now($s, #l);
  ensures $typemap(old($s)) == $typemap($s);
  ensures (exists #x:int :: $memory($s) == $store.mem($memory(old($s)), #l, #x));
  ensures (exists #st:$status :: $statusmap($s) == $store.sm($statusmap(S), #l, #st));
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));

  ensures $timestamp_post_strict(old($s), $s);
  ensures $post_unwrap(old($s), $s);

procedure $static_wrap(#l:$ptr, S:$state, owns:$ptrset);
  // writes #l, $owns($s, #l)
  modifies $s;
  // TOKEN: OOPS: pre_static_wrap must hold
  requires $pre_static_wrap($s);
  // TOKEN: the wrapped type must not be primitive
  requires $kind_of($typ(#l)) != $kind_primitive;
  // TOKEN: the object being wrapped must be typed
  requires $typed($s, #l);
  // TOKEN: the object being wrapped must not be closed
  requires !$closed($s, #l);
  // TOKEN: the object being wrapped must be owned by the current thread
  requires $owner($s, #l) == $me();
  ensures $wrapped($s, #l, $typ(#l));
  // ensures $set_in(#l, $domain($s, #l));
  ensures $is_claimable($typ(#l)) ==> old($ref_cnt($s, #l)) == 0 && $ref_cnt($s, #l) == 0;

  ensures $typemap(old($s)) == $typemap($s);
  ensures (exists #st:$status :: $statusmap($s) == $store.sm($statusmap(S), #l, #st));
  ensures (exists #x:int :: $memory($s) == $store.mem($store.mem($memory(old($s)), #l, #x), $dot(#l, $owns_set_field($typ(#l))), $ptrset_to_int(owns)));
  //ensures (forall #p:$ptr :: {$thread_local($s, #p)} $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_post_strict(old($s), $s);

  /*
  ensures (forall #p:$ptr :: {$st($s, #p)}
    #p == #l || 
    ($wrapped(old($s), #p, $typ(#p)) && $set_in(#p, $owns(old($s), #l))) || 
    $st($s, #p) == $st(old($s), #p));
  */



procedure $static_wrap_non_owns(#l:$ptr, S:$state);
  // writes #l, $owns($s, #l)
  modifies $s;
  // TOKEN: OOPS: pre_static_wrap holds
  requires $pre_static_wrap($s);
  // TOKEN: the wrapped type is non primitive
  requires $kind_of($typ(#l)) != $kind_primitive;
  // TOKEN: the object being wrapped is typed
  requires $typed($s, #l);
  // TOKEN: the object being wrapped is not closed
  requires !$closed($s, #l);
  // TOKEN: the object being wrapped is owned by the current thread
  requires $owner($s, #l) == $me();

  ensures $wrapped($s, #l, $typ(#l));
  // ensures $set_in(#l, $domain($s, #l));
  ensures $is_claimable($typ(#l)) ==> old($ref_cnt($s, #l)) == 0 && $ref_cnt($s, #l) == 0;

  ensures $typemap(old($s)) == $typemap($s);
  ensures (exists #st:$status :: $statusmap($s) == $store.sm($statusmap(S), #l, #st));
  ensures (exists #x:int :: $memory($s) == $store.mem($memory(old($s)), #l, #x));
  //ensures (forall #p:$ptr :: {$thread_local($s, #p)} $thread_local(old($s), #p) ==> $thread_local($s, #p));

  ensures $timestamp_post_strict(old($s), $s);


procedure $unwrap(#l:$ptr, T:$ctype);
  // writes #l
  modifies $s;
  // TOKEN: the object has no outstanding claims
  requires ! $is_claimable(T) || $ref_cnt($s, #l) == 0;
  // TOKEN: OOPS: pre_unwrap holds
  requires $pre_unwrap($s);
  // we can ensure that for everything we own, as it should be program invariant
  // that when we're consistent then all our children are nested
  // we can even ensure they used to be commited!
  // otherwise we're unable to prove $s frame condition
  ensures $mutable($s, #l);
  ensures $owns(old($s), #l) == $owns($s, #l);
  ensures (forall #p:$ptr :: 
    {$st($s, #p)} {$ts($s, #p)}
    {$set_in(#p, $owns(old($s), #l))}
    //{$st(old($s), #p)} {$st($s, #p)} {$ts(meta, #p)}
    $set_in(#p, $owns(old($s), #l)) ==> 
      $typed(old($s), #p) &&
      $wrapped($s, #p, $typ(#p)) && $timestamp_is_now($s, #p) && $is_non_primitive($typ(#p)));
  ensures (forall #p:$ptr :: {$set_in(#p, $owns(old($s), #l)), $is_claimable($typ(#p))}
    $set_in(#p, $owns(old($s), #l)) ==> 
      ($is_claimable($typ(#p)) ==> 
         old($ref_cnt($s, #p)) == $ref_cnt($s, #p) ));     
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_is_now($s, #l);

  ensures $typemap(old($s)) == $typemap($s);
  ensures (forall #p:$ptr :: {:weight 0} {$st($s, #p)}
    $st($s, #p) == $st(old($s), #p) ||
    ($nested(old($s), #p) && $set_in(#p, $owns(old($s), #l))) || 
    #p == #l);
  ensures (exists #x:int :: $memory($s) == $store.mem($memory(old($s)), #l, #x));
  ensures $timestamp_post_strict(old($s), $s);
  ensures $post_unwrap(old($s), $s);

procedure $wrap(#l:$ptr, T:$ctype);
  // writes #l, $owns($s, #l)
  modifies $s;
  // TOKEN: OOPS: pre_wrap holds
  requires $pre_wrap($s);
  // TOKEN: the wrapped type is non primitive
  requires $kind_of($typ(#l)) != $kind_primitive;
  // TOKEN: the object being wrapped is typed
  requires $typed2($s, #l, T);
  // TOKEN: the object being wrapped is not closed
  requires !$closed($s, #l);
  // TOKEN: the object being wrapped is owned by the current thread
  requires $owner($s, #l) == $me();
  // TOKEN: everything in the owns set is wrapped
  requires (forall #p:$ptr :: {$dont_instantiate(#p)} $set_in0(#p, $owns($s, #l)) ==> $wrapped($s, #p, $typ(#p)));
  ensures $owns(old($s), #l) == $owns($s, #l);
  ensures (forall #p:$ptr :: {$set_in(#p, $owns($s, #l))}
    $set_in(#p, $owns($s, #l)) ==> $is_non_primitive($typ(#p)) && $nested_in($s, #p, #l));
  ensures $wrapped($s, #l, $typ(#l));
  // ensures $set_in(#l, $domain($s, #l));
  ensures $is_claimable(T) ==> old($ref_cnt($s, #l)) == 0 && $ref_cnt($s, #l) == 0;
  ensures (forall #p:$ptr :: {$set_in(#p, $owns(old($s), #l)), $is_claimable($typ(#p))}
    $set_in(#p, $owns(old($s), #l)) ==> 
      ($is_claimable($typ(#p)) ==> 
         old($ref_cnt($s, #p)) == $ref_cnt($s, #p) ));
  //ensures (forall #p:$ptr :: {$thread_local($s, #p)}
  //  $thread_local(old($s), #p) ==> $thread_local($s, #p));

  ensures $typemap(old($s)) == $typemap($s);
  ensures (forall #p:$ptr :: {:weight 0} {$st($s, #p)}
    $st($s, #p) == $st(old($s), #p) ||
    ($wrapped(old($s), #p, $typ(#p)) && $set_in(#p, $owns(old($s), #l))) || 
    #p == #l );
  ensures (exists #x:int :: $memory($s) == $store.mem($memory(old($s)), #l, #x));
  ensures $timestamp_post_strict(old($s), $s);

procedure $bump_timestamp();
  modifies $s;
  ensures $memory($s) == $memory(old($s));
  ensures $typemap($s) == $typemap(old($s));
  ensures (exists x:$status :: $statusmap($s) == $store.sm($statusmap(old($s)), $null, x));
  ensures $current_timestamp(old($s)) < $current_timestamp($s);

// we should get rid of it
procedure $deep_unwrap(#l:$ptr, T:$ctype);
  // writes #l
  modifies $s;
  requires $wrapped($s, #l, T);
  requires $inv($s, #l, T) ==> $set_eq($owns($s, #l), $set_empty());
  ensures $inv($s,#l,T); // do we need it?
  ensures !$closed($s, #l);
  ensures (forall #p:$ptr :: {$st($s, #p)}// {$st(old($s), #p)}
    $in_full_extent_of(#p, #l) ==>
      $timestamp_is_now($s, #p) &&
     // we imagine that all untyped memory is nested in some global object
     !$closed($s, #p) && (#p == #l || $nested(old($s), #p)));
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $in_extent_of($s, #p, #l) ==> $owner($s, #p) == $me());
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));


  ensures $typemap($s) == $typemap(old($s));
  ensures (forall #p:$ptr :: {$st($s, #p)}
    !$typed(old($s), #p) || 
    $in_full_extent_of(#p, #l) ||
    $st_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$mem($s, #p)}
    $in_full_extent_of(#p, #l) ||
    $mem_eq(old($s), $s, #p));
  ensures $timestamp_post_strict(old($s), $s);
  ensures $post_unwrap(old($s), $s);


procedure $set_owns(#p:$ptr, owns:$ptrset);
  // writes #p
  modifies $s;
  // TOKEN: the owner is non-primitive
  requires $is_composite_ch($typ(#p));
  // TOKEN: the owner is mutable
  requires $mutable($s, #p);
  ensures $statusmap(old($s)) == $statusmap($s);
  ensures $typemap(old($s)) == $typemap($s);
  ensures $memory($s) == $store.mem(old($memory($s)), $dot(#p, $owns_set_field($typ(#p))), $ptrset_to_int(owns));
  ensures $timestamp_post_strict(old($s), $s);

procedure $set_closed_owner(#p:$ptr, owner:$ptr);
  // writes #p, owner
  modifies $s;
  // TOKEN: the owner is composite
  requires $is_composite_ch($typ(owner));
  // TOKEN: the object is non-primitive
  requires $kind_of($typ(#p)) != $kind_primitive;
  // TOKEN: the object is owned by the current thread
  requires $owner($s, #p) == $me();
  // TOKEN: the object is closed
  requires $closed($s, #p);
  // TOKEN: the owner is closed
  requires $closed($s, owner);
  // TOKEN: the owner has volatile owns set
  requires $has_volatile_owns_set($typ(owner));
  ensures $typemap(old($s)) == $typemap($s);
  ensures (exists st:$status :: $statusmap($s) == $store.sm(old($statusmap($s)), #p, st) && $st_owner(st) == owner && $st_closed(st));
  ensures $ref_cnt(old($s), #p) == $ref_cnt($s, #p);
  ensures $memory($s) == $store.mem(old($memory($s)), $dot(owner, $owns_set_field($typ(owner))), 
                                $ptrset_to_int($set_union($set_singleton(#p), $owns(old($s), owner))));
  ensures $timestamp_post_strict(old($s), $s);
  ensures $set_in(#p, $owns($s, owner));

function {:inline true} $new_ownees(S:$state, o:$ptr, owns:$ptrset) returns($ptrset)
  { $set_difference(owns, $owns(S, o)) }

procedure $set_closed_owns(owner:$ptr, owns:$ptrset);
  // writes owner, $new_ownees(owner, owns)
  modifies $s;
  // TOKEN: the owner is composite
  requires $is_composite_ch($typ(owner));
  // TOKEN: all newly owned objects are wrapped
  requires (forall p:$ptr :: {$dont_instantiate(p)} {sk_hack($set_in0(p, $owns($s, owner)))}
    $set_in(p, $new_ownees($s, owner, owns)) ==> $wrapped($s, p, $typ(p)));
  // TOKEN: the owner is closed
  requires $closed($s, owner);
  // TOKEN: the owner has volatile owns set
  requires $has_volatile_owns_set($typ(owner));
  ensures $typemap(old($s)) == $typemap($s);
  ensures (forall #p:$ptr :: {$set_in(#p, $owns(old($s), owner))} $set_in(#p, $owns(old($s), owner)) ==> $is_non_primitive($typ(#p)));
  ensures (forall #p:$ptr :: {$st($s, #p)} {$ts($s, #p)}
    $ref_cnt(old($s), #p) == $ref_cnt($s, #p) &&
      if $set_in(#p, $owns(old($s), owner)) then
        if $set_in(#p, owns) then
          $st_eq(old($s), $s, #p) 
        else 
          $wrapped($s, #p, $typ(#p)) && $timestamp_is_now($s, #p)
      else
        if $set_in(#p, owns) then
          $owner($s, #p) == owner && $closed($s, #p)
        else
          $st_eq(old($s), $s, #p));
  ensures $memory($s) == $store.mem(old($memory($s)), $dot(owner, $owns_set_field($typ(owner))), $ptrset_to_int(owns));
  ensures $timestamp_post_strict(old($s), $s);


procedure $giveup_closed_owner(#p:$ptr, owner:$ptr);
  // writes owner
  modifies $s;
  // TOKEN: the owner is composite
  requires $is_composite_ch($typ(owner));
  // TOKEN: the object is owned by the owner
  requires $set_in(#p, $owns($s, owner));
  // TOKEN: the owner is closed
  requires $closed($s, owner);
  // TOKEN: the owner has volatile owns set
  requires $has_volatile_owns_set($typ(owner));
  ensures $typed($s, #p);
  ensures $typemap(old($s)) == $typemap($s);
  ensures (exists st:$status :: $statusmap($s) == $store.sm($statusmap(old($s)), #p, st));
  ensures $wrapped($s, #p, $typ(#p));
  ensures $timestamp_is_now($s, #p);
  ensures $ref_cnt(old($s), #p) == $ref_cnt($s, #p);
  ensures $memory($s) == $store.mem(old($memory($s)), $dot(owner, $owns_set_field($typ(owner))),
                                                $ptrset_to_int($set_difference($owns(old($s), owner), $set_singleton(#p))));
  ensures $timestamp_post_strict(old($s), $s);


// -----------------------------------------------------------------------
// Allocation
// -----------------------------------------------------------------------

function $get_memory_allocator() returns($ptr);
function $is_in_stackframe(#sf:int, p:$ptr) returns(bool);
const unique $memory_allocator_type : $ctype;
const $memory_allocator_ref : int;
axiom $get_memory_allocator() == $ptr($memory_allocator_type, $memory_allocator_ref);
axiom $ptr_level($memory_allocator_type) == 0;

procedure $stack_alloc(#t:$ctype, #sf:int, #spec:bool) returns (#r:$ptr);
  modifies $s;
  ensures $typed2($s, #r, #t);
  ensures $extent_mutable($s, #r);
  ensures $extent_is_fresh(old($s), $s, #r);
  ensures $mutable($s, $emb($s, #r));

  ensures (forall #p:$ptr :: {$ts($s, #p)} {$st($s, #p)} // {$st(old($s), #p)} 
    $in_extent_of($s, #p, #r) ==> $mutable($s, #p) 
      && $nested(old($s), #p)
      && $owns($s, #p) == $set_empty()
      && $timestamp_is_now($s, #p)
    );

  ensures (forall #p:$ptr :: {$st($s, #p)} 
    #p == $emb($s, #r) || $in_full_extent_of(#p, #r) ==> $timestamp_is_now($s, #p));

  ensures $memory(old($s)) == $memory($s);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $st_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $ts_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_post_strict(old($s), $s);

  ensures !$typed(old($s), #r);
  ensures $is_in_stackframe(#sf, #r);
  ensures $is_object_root($s, #r);
  ensures $first_option_typed($s, #r);
  ensures #spec ==> $in_range_spec_ptr($ref(#r));
  ensures !#spec ==> $in_range_phys_ptr($ref(#r)) && $in_range_phys_ptr($ref(#r) + $sizeof(#t) - 1);


procedure $stack_free(#sf:int, #x:$ptr);
  // writes extent(#x)
  modifies $s;
  // TOKEN: the extent of the object being reclaimed is mutable
  requires $extent_mutable($s, #x);
  // TOKEN: the pointer being reclaimed was returned by stack_alloc()
  requires $is_in_stackframe(#sf, #x);

  ensures (forall #p:$ptr :: {$st($s, #p)}
    $in_full_extent_of(#p, #x) || $st($s, #p) == $st(old($s), #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $in_full_extent_of(#p, #x) || $ts($s, #p) == $ts(old($s), #p));
  ensures $memory($s) == $memory(old($s));
  ensures $timestamp_post(old($s), $s);

procedure $spec_alloc(#t:$ctype) returns(#r:$ptr);
  modifies $s;
  ensures $typed2($s, #r, #t);
  ensures $extent_mutable($s, #r);
  ensures $extent_is_fresh(old($s), $s, #r);
  ensures $mutable($s, $emb($s, #r));

  ensures (forall #p:$ptr :: {$ts($s, #p)} {$st($s, #p)} // {$st(old($s), #p)} 
    $in_extent_of($s, #p, #r) ==> $mutable($s, #p) 
      && $nested(old($s), #p)
      && $owns($s, #p) == $set_empty()
      && $timestamp_is_now($s, #p)
    );

  ensures (forall #p:$ptr :: {$st($s, #p)} 
    #p == $emb($s, #r) || $in_full_extent_of(#p, #r) ==> $timestamp_is_now($s, #p));

  ensures $memory(old($s)) == $memory($s);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $st_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $ts_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_post_strict(old($s), $s);

  ensures !$typed(old($s), #r);
  ensures $is_malloc_root($s, #r);
  ensures $is_object_root($s, #r);
  ensures $first_option_typed($s, #r);
  ensures $in_range_spec_ptr($ref(#r));

procedure $spec_alloc_array(#t:$ctype, sz:int) returns(#r:$ptr);
  modifies $s;
  ensures $typed2($s, #r, $array(#t, sz));
  ensures $extent_mutable($s, #r);
  ensures $extent_is_fresh(old($s), $s, #r);
  ensures $mutable($s, $emb($s, #r));

  ensures (forall #p:$ptr :: {$ts($s, #p)} {$st($s, #p)} // {$st(old($s), #p)} 
    $in_extent_of($s, #p, #r) ==> $mutable($s, #p) 
      && $nested(old($s), #p)
      && $owns($s, #p) == $set_empty()
      && $timestamp_is_now($s, #p)
    );

  ensures (forall #p:$ptr :: {$st($s, #p)} 
    #p == $emb($s, #r) || $in_full_extent_of(#p, #r) ==> $timestamp_is_now($s, #p));

  ensures $memory(old($s)) == $memory($s);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $st_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $ts_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_post_strict(old($s), $s);

  ensures !$typed(old($s), #r);
  ensures $is_malloc_root($s, #r);
  ensures $is_object_root($s, #r);
  ensures $first_option_typed($s, #r);
  ensures $in_range_spec_ptr($ref(#r));


procedure $alloc(#t:$ctype) returns(#r:$ptr);
  modifies $s;
  ensures $ref(#r) == 0 || $typed2($s, #r, #t);
  ensures $ref(#r) == 0 || $extent_mutable($s, #r);
  ensures $ref(#r) == 0 || $extent_is_fresh(old($s), $s, #r);
  ensures $ref(#r) == 0 || $mutable($s, $emb($s, #r));

  ensures (forall #p:$ptr :: {$ts($s, #p)} {$st($s, #p)} // {$st(old($s), #p)} 
    $in_extent_of($s, #p, #r) ==> $mutable($s, #p) 
      && $nested(old($s), #p)
      && $owns($s, #p) == $set_empty()
      && $timestamp_is_now($s, #p)
    );

  ensures (forall #p:$ptr :: {$st($s, #p)} 
    #p == $emb($s, #r) || $in_full_extent_of(#p, #r) ==> $timestamp_is_now($s, #p));

  ensures $memory(old($s)) == $memory($s);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $st_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $typed(old($s), #p) || !$nested(old($s), #p) ==> $ts_eq(old($s), $s, #p));
  ensures (forall #p:$ptr :: {$thread_local($s, #p)}
    $thread_local(old($s), #p) ==> $thread_local($s, #p));
  ensures $timestamp_post_strict(old($s), $s);

  ensures !$typed(old($s), #r);
  ensures $ref(#r) == 0 || $is_malloc_root($s, #r);
  ensures $ref(#r) == 0 || $is_object_root($s, #r);
  ensures $ref(#r) == 0 || $first_option_typed($s, #r);
  ensures $in_range_phys_ptr($ref(#r)) && $in_range_phys_ptr($ref(#r) + $sizeof(#t) - 1);


procedure $free(#x:$ptr);
  // writes extent(#x)
  modifies $s;
  // TOKEN: the object being reclaimed is typed
  requires $typed($s, #x);
  // TOKEN: the pointer being reclaimed was returned by malloc()
  requires $is_malloc_root($s, #x);

  ensures (forall #p:$ptr :: {$st($s, #p)}
    $in_full_extent_of(#p, #x) || $st($s, #p) == $st(old($s), #p));
  ensures (forall #p:$ptr :: {$ts($s, #p)}
    $in_full_extent_of(#p, #x) || $ts($s, #p) == $ts(old($s), #p));
  ensures $memory($s) == $memory(old($s));
  ensures $timestamp_post(old($s), $s);


function $program_entry_point(s:$state) returns(bool);
function $program_entry_point_ch(s:$state) returns(bool);

axiom (forall S:$state :: {$program_entry_point(S)} $program_entry_point(S) ==> $program_entry_point_ch(S));

function {:inline true} $is_global(p:$ptr, t:$ctype) returns(bool)
  { (forall S:$state :: {$ts(S, p)} $good_state(S) ==> $typed(S, p) && $is_object_root(S, p)) &&
    (forall S:$state, f:$field :: {$ts(S, $dot(p, f))} $good_state(S) ==> $typed(S, p) && $is_object_root(S, p)) &&
    (forall S:$state, f:$field, i:int, tt:$ctype :: {$ts(S, $idx($dot(p, f), i, tt))} $good_state(S) ==> $typed(S, p) && $is_object_root(S, p)) &&
    (forall S:$state :: {$program_entry_point(S)} $program_entry_point(S) ==> $extent_mutable(S, p) && $owns(S, p) == $set_empty())
  }

function {:inline true} $is_global_array(p:$ptr, T:$ctype, sz:int) returns(bool)
  { 
    $is(p, T) && 
    (forall S:$state, i:int :: {$st(S, $idx(p, i, T))} {$ts(S, $idx(p, i, T))}
      $good_state(S) ==>
      0 <= i && i < sz ==> 
        !$is_volatile(S, $idx(p, i, T)) && 
        $typed(S, $idx(p, i, T)) &&
        ($program_entry_point_ch(S) ==> $mutable(S, $idx(p, i, T)))
        ) }

// typedness and writes check are handled by the assignment translation
procedure $havoc(o:$ptr, t:$ctype);
  modifies $s;
  requires $is(o, t);
  ensures $typemap($s) == $typemap(old($s));
  ensures $statusmap($s) == $statusmap(old($s));
  ensures (forall #p:$ptr :: {$mem($s, #p)}
    $in_extent_of(old($s), #p, o) || $mem_eq(old($s), $s, #p));

// -----------------------------------------------------------------------
// Unions
// -----------------------------------------------------------------------

function {:inline true} $active_option(S:$state, u:$ptr) returns($field)
  { $ts_active_option($ts(S, u)) }

function $ts_active_option($type_state) returns($field);

function {:inline true} $union_active(S:$state, u:$ptr, f:$field) returns(bool)
  { $active_option(S, u) == f }

procedure $union_reinterpret(#x:$ptr, #off:$field);
  // writes extent(#x)
  modifies $s;
  // TOKEN: the reinterpretation target field comes from a proper union
  requires $is_union_field($typ(#x), #off);
  // TOKEN: the reinterpretation target union is typed
  requires $typed($s, #x);
  ensures $active_option($s, #x) == #off;
  ensures $typed($s, #x);
  ensures (forall #p:$ptr :: {$st($s, #p)}
    $in_extent_of($s, #p, #x) ==> $now_writable($s, #p));
  ensures $union_havoced(old($s), $s, #x);
  ensures $is_object_root(old($s), #x) <==> $is_object_root($s, #x);

  ensures (forall #p:$ptr :: {$ts($s, #p)}
      $in_full_extent_of(#p, #x) || $ts($s, #p) == $ts(old($s), #p));
  ensures (forall #p:$ptr :: {$st($s, #p)}
      $in_full_extent_of(#p, #x) || $st($s, #p) == $st(old($s), #p));
  ensures $timestamp_post_strict(old($s), $s);

function $is_union_field($ctype, $field) returns(bool); // generated by the translation
function {:inline true} $union_havoced(#s1:$state, #s2:$state, #x:$ptr) returns(bool)
  {
      (forall #p:$ptr :: {$mem(#s2, #p)}
        #p == #x ||
        ($in_full_extent_of(#p, #x) && (!$typed(#s1, #p) || !$typed(#s2, #p))) ||
        $mem_eq(#s1, #s2, #p))
  }

function $full_extent(#p:$ptr) returns($ptrset);
function $extent(S:$state, #p:$ptr) returns($ptrset);
function $span(#p:$ptr) returns($ptrset);
function {:inline true} $in_span_of(#p:$ptr, #l:$ptr) returns(bool)
  { $set_in(#p, $span(#l)) }
function $first_option_typed(S:$state, #p:$ptr) returns(bool);

function {:inline true} $struct_extent(#p:$ptr) returns($ptrset)
  { $full_extent(#p) }
function {:inline true} $in_struct_extent_of(#p:$ptr, #l:$ptr) returns(bool)
  { $set_in(#p, $struct_extent(#l)) }

function $volatile_span(S:$state, #p:$ptr) returns($ptrset);
axiom (forall S:$state, p:$ptr, q:$ptr :: {$set_in(p, $volatile_span(S, q))}
  $set_in(p, $volatile_span(S, q)) <==> p == q || ($is_volatile(S, p) && $set_in(p, $span(q))));

// -----------------------------------------------------------------------
// Memory reinterpretation
// -----------------------------------------------------------------------

function $left_split(a:$ptr, i:int) returns($ptr)
  { $as_array(a, $element_type($typ(a)), i) }
function $right_split(a:$ptr, i:int) returns($ptr)
  { $as_array($idx($ptr($element_type($typ(a)), $ref(a)), i, $element_type($typ(a))), $element_type($typ(a)), $array_length($typ(a)) - i) }

function $joined_array(a1:$ptr, a2:$ptr) returns($ptr)
  { $ptr($array($element_type($typ(a1)), $array_length($typ(a1))+$array_length($typ(a2))), $ref(a1)) }

function {:inline true} $mutable_root(S:$state, p:$ptr) returns(bool)
  { $extent_mutable(S, p) && $is_object_root(S, p) && $timestamp_is_now(S, p) }

procedure $split_array(a:$ptr, i:int);
  // writes extent(a)
  modifies $s;
  // TOKEN: the array is split at positive index
  requires 0 < i;
  // TOKEN: the split-point is within the array
  requires i < $array_length($typ(a));
  // TOKEN: the array to split is not embedded inside of another object
  requires $is_object_root($s, a);
  ensures $memory(old($s)) == $memory($s);
  ensures (forall p:$ptr :: {$st($s, p)}
    p == a || p == $left_split(a, i) || p == $right_split(a, i) ||
    $st_eq(old($s), $s, p));
  ensures (forall p:$ptr :: {$ts($s, p)}
    p == a || p == $left_split(a, i) || p == $right_split(a, i) ||
    $emb(old($s), p) == a ||
    $ts_eq(old($s), $s, p));
  ensures $mutable_root($s, $left_split(a, i)) && $mutable_root($s, $right_split(a, i));
  ensures $memory($s) == $memory(old($s));
  ensures $timestamp_post_strict(old($s), $s);

procedure $join_arrays(a1:$ptr, a2:$ptr);
  // writes extent(a1,a2)
  modifies $s;
  // TOKEN: the first array to join is not embedded inside of another object
  requires $is_object_root($s, a1);
  // TOKEN: the second array to join is not embedded inside of another object
  requires $is_object_root($s, a2);
  // TOKEN: types of arrays to join agree
  requires $element_type($typ(a1)) == $element_type($typ(a2));
  // TOKEN: the first array ends, where the second array starts
  requires $ref($idx(a1, $array_length($typ(a1)), $element_type($typ(a1)))) == $ref(a2);
  ensures $memory(old($s)) == $memory($s);
  ensures (forall p:$ptr :: {$st($s, p)}
    p == $joined_array(a1, a2) || p == a1 || p == a2 ||
    $st_eq(old($s), $s, p));
  ensures (forall p:$ptr :: {$ts($s, p)}
    p == $joined_array(a1, a2) || p == a1 || p == a2 ||
    $emb(old($s), p) == a1 || $emb(old($s), p) == a2 ||
    $ts_eq(old($s), $s, p));
  ensures $mutable_root($s, $joined_array(a1, a2));
  ensures $memory($s) == $memory(old($s));
  ensures $timestamp_post_strict(old($s), $s);

procedure $to_bytes(a:$ptr);
  // writes extent(a)
  modifies $s;
  // TOKEN: the reinterpreted object is not embedded inside of another object
  requires $is_object_root($s, a);
  ensures $mutable_root($s, $as_array(a, ^^u1, $sizeof($typ(a))));
  ensures (forall p:$ptr :: {$st($s, p)} {$st($s, p)}
    ($set_in(p, $extent($s, $as_array(a, ^^u1, $sizeof($typ(a))))) ==> $now_writable($s, p)) &&
    ($set_in(p, $full_extent(a)) ||
     $set_in(p, $extent($s, $as_array(a, ^^u1, $sizeof($typ(a))))) ||
     ($st_eq(old($s), $s, p) && $ts_eq(old($s), $s, p))));
  ensures (forall p:$ptr :: {$mem($s, p)}
    $set_in(p, $full_extent(a)) ||
    $set_in(p, $full_extent($as_array(a, ^^u1, $sizeof($typ(a))))) ||
    ($st_eq(old($s), $s, p) && $ts_eq(old($s), $s, p) && $mem_eq(old($s), $s, p)));
  ensures $timestamp_post_strict(old($s), $s);

procedure $from_bytes(a:$ptr, t:$ctype, preserve_zero:bool);
  // writes extent(a)
  modifies $s;
  // TOKEN: the reinterpreted array is not embedded inside of another object
  requires $is_object_root($s, a);
  // TOKEN: the reinterpreted array is array of bytes
  requires $element_type($typ(a)) == ^^u1;
  // TOKEN: the reinterpreted array is large enough
  requires $sizeof(t) <= $array_length($typ(a));
  // TOKEN: extent_zero holds for the reinterpreted array
  requires preserve_zero ==> $extent_zero($s, a);
  ensures $mutable_root($s, $ptr(t, $ref(a)));
  ensures (forall p:$ptr :: {$st($s, p)} {$ts($s, p)}
    ($set_in(p, $extent($s, $ptr(t, $ref(a)))) ==> $now_writable($s, p)) &&
    ($set_in(p, $full_extent(a)) ||
     $set_in(p, $extent($s, $ptr(t, $ref(a)))) ||
     ($st_eq(old($s), $s, p) && $ts_eq(old($s), $s, p))));
  ensures (forall p:$ptr :: {$mem($s, p)}
    $set_in(p, $full_extent(a)) ||
    $set_in(p, $full_extent($ptr(t, $ref(a)))) ||
    ($st_eq(old($s), $s, p) && $ts_eq(old($s), $s, p) && $mem_eq(old($s), $s, p)));
  ensures $timestamp_post_strict(old($s), $s);
  ensures preserve_zero ==> $extent_zero($s, $ptr(t, $ref(a)));

// -----------------------------------------------------------------------
// Sets of pointers
// -----------------------------------------------------------------------

type $ptrset;

function $set_in($ptr,$ptrset) returns(bool);

function $set_empty() returns($ptrset);
axiom (forall #o: $ptr :: {:weight 0} {$set_in(#o, $set_empty())} !$set_in(#o, $set_empty()));

function $set_singleton($ptr) returns ($ptrset);
axiom (forall #r: $ptr, #o: $ptr :: {:weight 0} {$set_in(#o, $set_singleton(#r))} $set_in(#o, $set_singleton(#r)) <==> #r == #o);

function $non_null_set_singleton($ptr) returns ($ptrset);
axiom (forall #r: $ptr, #o: $ptr :: {:weight 0} {$set_in(#o, $non_null_set_singleton(#r))} $set_in(#o, $non_null_set_singleton(#r)) <==> (#r == #o && $ptr_neq(#r, $null)));

function $set_union($ptrset, $ptrset) returns ($ptrset);
axiom (forall #a: $ptrset, #b: $ptrset, #o: $ptr :: {:weight 0} {$set_in(#o, $set_union(#a,#b))}
  $set_in(#o, $set_union(#a,#b)) <==> $set_in(#o, #a) || $set_in(#o, #b));

function $set_difference($ptrset, $ptrset) returns ($ptrset);
axiom (forall #a: $ptrset, #b: $ptrset, #o: $ptr :: {:weight 0} {$set_in(#o, $set_difference(#a,#b))}
  $set_in(#o, $set_difference(#a,#b)) <==> $set_in(#o, #a) && !$set_in(#o, #b));

function $set_intersection($ptrset, $ptrset) returns ($ptrset);
axiom (forall #a: $ptrset, #b: $ptrset, #o: $ptr :: {:weight 0} {$set_in(#o, $set_intersection(#a,#b))}
  $set_in(#o, $set_intersection(#a,#b)) <==> $set_in(#o, #a) && $set_in(#o, #b));
  
function $set_subset($ptrset, $ptrset) returns (bool);
axiom(forall #a: $ptrset, #b: $ptrset :: {:weight 0} {$set_subset(#a,#b)}
  $set_subset(#a,#b) <==> (forall #o: $ptr :: {:weight 0} {$set_in(#o, #a)} {$set_in(#o, #b)} $set_in(#o, #a) ==> $set_in(#o, #b)));

// to be used only positively
function $set_eq($ptrset, $ptrset) returns (bool);
axiom (forall #a: $ptrset, #b: $ptrset :: {:weight 0} {$set_eq(#a,#b)}
  (forall #o: $ptr :: {:weight 0} {$dont_instantiate(#o)} $set_in(#o, #a) <==> $set_in(#o, #b)) ==> $set_eq(#a, #b));
axiom (forall #a: $ptrset, #b: $ptrset :: {:weight 0} {$set_eq(#a,#b)}
  $set_eq(#a, #b) ==> #a == #b);

function $set_cardinality($ptrset) returns(int);

axiom ($set_cardinality($set_empty()) == 0);
axiom (forall p:$ptr :: {:weight 0} $set_cardinality($set_singleton(p)) == 1);

function $set_universe() returns($ptrset);
axiom (forall #o: $ptr :: {:weight 0} {$set_in(#o, $set_universe())} $set_in(#o, $set_universe()));

function $set_disjoint(s1:$ptrset, s2:$ptrset) returns(bool);
function $id_set_disjoint(p:$ptr, s1:$ptrset, s2:$ptrset) returns(int);

axiom (forall p:$ptr, s1:$ptrset, s2:$ptrset :: {:weight 0} {$set_disjoint(s1, s2), $set_in(p, s1)}
  $set_disjoint(s1, s2) && $set_in(p, s1) ==> 
    $id_set_disjoint(p, s1, s2) == 1);
axiom (forall p:$ptr, s1:$ptrset, s2:$ptrset :: {:weight 0} {$set_disjoint(s1, s2), $set_in(p, s2)}
  $set_disjoint(s1, s2) && $set_in(p, s2) ==> 
    $id_set_disjoint(p, s1, s2) == 2);

axiom (forall s1:$ptrset, s2:$ptrset :: {:weight 0} {$set_disjoint(s1, s2)}
  (forall p:$ptr :: {$dont_instantiate(p)}
     ($set_in(p, s1) ==> !$set_in(p, s2)) && ($set_in(p, s2) ==> !$set_in(p, s1))) 
  ==> $set_disjoint(s1, s2));


function $set_in3($ptr, $ptrset) returns(bool);
function $set_in2($ptr, $ptrset) returns(bool);

function $in_some_owns($ptr) returns(bool);

axiom (forall p:$ptr, S1:$state, p1:$ptr :: 
  {:weight 0} {$set_in(p, $owns(S1, p1))}
  $set_in(p, $owns(S1, p1)) ==> $in_some_owns(p));

axiom (forall p:$ptr, S1:$state, p1:$ptr :: 
  {:weight 0} {$set_in2(p, $owns(S1, p1)), $in_some_owns(p)}
  $set_in(p, $owns(S1, p1)) <==> $set_in2(p, $owns(S1, p1)));

axiom (forall p:$ptr, s:$ptrset :: {:weight 0} {$set_in(p, s)}
  $set_in(p, s) <==> $set_in2(p, s));
axiom (forall p:$ptr, s:$ptrset :: {:weight 0} {$set_in(p, s)}
  $set_in(p, s) <==> $set_in3(p, s));

function $set_in0($ptr, $ptrset) returns(bool);
axiom (forall p:$ptr, s:$ptrset :: {:weight 0} {$set_in0(p, s)}
  $set_in(p, s) <==> $set_in0(p, s));

/*
// Alternative; easier to use, but seems slower, at least for the list
function $as_in0(p:$ptr) returns($ptr) { p }
function {:inline true} $set_in0(p:$ptr, s:$ptrset) returns(bool)
  { $set_in($as_in0(p), s) }
*/

/*
axiom (forall s1:$state, s2:$state, p:$ptr, q:$ptr :: 
  { $set_in0(p, cast(s1[q],$ptrset)), $set_in(p, cast(s2[q],$ptrset)) }
  $set_in(p, cast(s2[q],$ptrset)) <==> $set_in0(p, cast(s2[q],$ptrset)));
*/

function sk_hack(bool) returns(bool);

/*
function $field_set(S:$ptrset, #t:$ctype, #f:$field) returns($ptrset);
axiom (forall S:$ptrset, #t:$ctype, #f:$field, #p:$ptr :: {$set_in(#p, $field_set(S, #t, #f))}
  $set_in(#p, $field_set(S, #t, #f)) ==> $set_in($ptr(#t, $ref(#p) - $field_offset(#f)), S));

axiom (forall S:$ptrset, #t:$ctype, #f:$field, #p:$ptr, S:$state ::
  $set_in(#p, $field_set(S, #t, #f)) ==> $set_in($emb(S, #p), s)
  $set_in($ptr(#t, $ref(#p) - $field_offset(#f)), S));
 */

/*
function $water_level($state, $ptr) returns($ptr);

axiom (forall S:$state, p:$ptr :: {$thread_local(S, p)}
  $good_state(S) ==>
    $thread_local(S, p) ==> $owner(S, $water_level(S, p)) == $me());

axiom (forall M1:$state, M2:$state, p:$ptr :: {$thread_local(M1, p), $thread_local(M2, p)}
  $thread_local(M1, p) && $st(M1, $water_level(M1, p)) == $st(M1, $water_level(M2, p)) ==>
    $thread_local(M2, p));
  */

function {:inline true} $writes_nothing(S1:$state, S2:$state) returns(bool)
  { 
    (forall p:$ptr :: {$st(S2, p)}
        $nested(S2, p) ==> $nested(S1, p)) &&
    (forall p:$ptr :: {$mem(S2, p)}
       $thread_local(S1, p) ==> $mem_eq(S1, S2, p) && $thread_local(S2, p)) &&
    (forall p:$ptr :: {$st(S2, p)}
       $thread_local(S1, p) ==> $st_eq(S1, S2, p) && $thread_local(S2, p)) &&
    (forall p:$ptr :: {$ts(S2, p)}
       $thread_local(S1, p) ==> $ts_eq(S1, S2, p) && $thread_local(S2, p)) &&
    $timestamp_post(S1, S2)
  }

// --------------------------------------------------------------------------------
// Arrays
// --------------------------------------------------------------------------------

// to be used when you allocate just the array itself
function $array($ctype, int) returns($ctype);
function $element_type($ctype) returns($ctype);
function $array_length($ctype) returns(int);
axiom (forall T:$ctype, s:int :: {$array(T, s)} $element_type($array(T, s)) == T);
axiom (forall T:$ctype, s:int :: {$array(T, s)} $array_length($array(T, s)) == s);
axiom (forall T:$ctype, s:int :: {$array(T, s)} $ptr_level($array(T, s)) == 0);
axiom (forall T:$ctype, s:int :: {$array(T, s)} $is_arraytype($array(T, s)));
axiom (forall T:$ctype, s:int :: {$array(T, s)} !$is_claimable($array(T, s)));
axiom (forall T:$ctype, s:int :: {$sizeof($array(T, s))} $sizeof($array(T, s)) == $sizeof(T) * s);

function {:weight 0} $inlined_array(p:$ptr, T:$ctype) returns ($ptr)
  { p }

function $idx($ptr,int,$ctype) returns($ptr);
axiom (forall #p:$ptr, #i:int, #t:$ctype ::
  {$idx(#p, #i, #t)} 
    $extent_hint($idx(#p, #i, #t), #p) &&
    $idx(#p, #i, #t) == $ptr(#t, $add.mul($ref(#p) , #i , $sizeof(#t))));

//function $add.mul(x:int,y:int,z:int) returns(int);


function {:inline true} {:expand true} $add.mul(x:int,y:int,z:int) returns(int)
  { x + y*z }

function {:inline true} {:expand true} $add(x:int,y:int) returns(int)
  { x + y }

axiom (forall p:$ptr, i:int, j:int, T:$ctype :: {$idx($idx(p, i, T), j, T)}
  i != 0 && j != 0 ==> // seems to prevent matching loop
    $idx($idx(p, i, T), j, T) == $idx(p, $add( i,  j ), T));

function {:weight 0} $is_array_vol_or_nonvol(S:$state, p:$ptr, T:$ctype, sz:int, vol:bool) returns(bool)
  { $is(p, T) && 
    (forall i:int :: {$st(S, $idx(p, i, T))} {$ts(S, $idx(p, i, T))} {$mem(S, $idx(p, i, T))}
      0 <= i && i < sz ==> 
        ($is_volatile(S, $idx(p, i, T)) == vol) && $typed(S, $idx(p, i, T))) }

function {:weight 0} $is_array(S:$state, p:$ptr, T:$ctype, sz:int) returns(bool)
  { $is(p, T) && 
    (forall i:int :: {$st(S, $idx(p, i, T))} {$ts(S, $idx(p, i, T))} {$mem(S, $idx(p, i, T))}
      0 <= i && i < sz ==> 
        $typed(S, $idx(p, i, T))) }

/*
axiom (forall S:$state, p:$ptr, T:$ctype, sz:int ::
    $is_array(S, p, T, sz) ==>
    (forall i:int :: {$st(S, $idx(p, i, T))} {$ts(S, $idx(p, i, T))} {$mem(S, $idx(p, i, T))}
        // TODO introduce $elements_in_biggest_emb_array(T)
      0 <= i && i < sz ==> 
        $sizeof($typ($emb(S, $idx(p, i, T)))) >= sz // * $sizeof(T)
        ));
  */        

function {:inline true} $is_thread_local_array(S:$state, p:$ptr, T:$ctype, sz:int) returns(bool)
  { (forall i:int :: {$st(S, $idx(p, i, T))}  {$ts(S, $idx(p, i, T))}
      0 <= i && i < sz ==> 
        $thread_local2(S, $idx(p, i, T), T)) }

function {:inline true} $is_mutable_array(S:$state, p:$ptr, T:$ctype, sz:int) returns(bool)
  { $is_array(S, p, T, sz) &&
    (forall i:int :: {$st(S, $idx(p, i, T))}  {$ts(S, $idx(p, i, T))}
      0 <= i && i < sz ==> $mutable(S, $idx(p, i, T))) }

function {:inline true} $is_array_emb(S:$state, p:$ptr, T:$ctype, sz:int, emb:$ptr) returns(bool)
  { $is_array_vol_or_nonvol(S, p, T, sz, false) &&
    (forall i:int :: {$ts(S, $idx(p, i, T))} 
      0 <= i && i < sz ==> $emb(S, $idx(p, i, T)) == emb) }

function {:inline true} $is_array_emb_path(S:$state, p:$ptr, T:$ctype, sz:int, emb:$ptr, f:$field, isvol:bool) returns(bool)
  { $is_array_vol_or_nonvol(S, p, T, sz, isvol) &&
    (forall i:int :: {$ts(S, $idx(p, i, T))} {$mem(S, $idx(p, i, T))}
      0 <= i && i < sz ==> $emb(S, $idx(p, i, T)) == emb && $path(S, $idx(p, i, T)) == $array_path(f, i)) }

function {:inline true} $array_field_properties(f:$field, T:$ctype, sz:int, union:bool, vol:bool) returns(bool)
  { (forall S:$state, p:$ptr, i:int ::
       {$ts(S, $idx($dot(p, f), i, T))}
       {$st(S, $idx($dot(p, f), i, T))}
       {$mem(S, $idx($dot(p, f), i, T))}
       0 <= i && i < sz &&
       (!union || $active_option(S, p) == f) &&
       $typed2(S, p, $field_parent_type(f)) ==>
         $is_volatile(S, $idx($dot(p, f), i, T)) == vol &&
         $typed(S, $idx($dot(p, f), i, T)) &&
         $emb(S, $idx($dot(p, f), i, T)) == p &&
         $path(S, $idx($dot(p, f), i, T)) == $array_path(f, i)
      ) }

function {:inline true} $no_inline_array_field_properties(f:$field, T:$ctype, sz:int, union:bool, vol:bool) returns(bool)
  { (forall S:$state, p:$ptr ::
       {$ts(S, $as_array($dot(p, f), T, sz))}
       {$st(S, $as_array($dot(p, f), T, sz))}
       {$mem(S, $as_array($dot(p, f), T, sz))}
       (!union || $active_option(S, p) == f) &&       
       $typed2(S, p, $field_parent_type(f)) ==>
         $extent_hint($as_array($dot(p, f), T, sz), p) &&
         $typed(S, $as_array($dot(p, f), T, sz)) &&
         $emb(S, $as_array($dot(p, f), T, sz)) == p &&
         $path(S, $as_array($dot(p, f), T, sz)) == f 
      )
    &&
   (forall p:$ptr, i:int :: {$idx($dot(p, f), i, T)} $instantiate_ptr($as_array($dot(p, f), T, sz)))
   }

axiom (forall p:$ptr, #r:int, T:$ctype, sz:int ::
    { $in_full_extent_of(p, $ptr($array(T, sz), #r)) }
    $in_full_extent_of(p, $ptr($array(T, sz), #r)) <==> 
      p == $ptr($array(T, sz), #r) || $in_array_full_extent_of(p, $ptr(T, #r), T, sz));

axiom (forall S:$state, p:$ptr, #r:int, T:$ctype, sz:int ::
    { $in_extent_of(S, p, $ptr($array(T, sz), #r)) }
    $in_extent_of(S, p, $ptr($array(T, sz), #r)) <==> 
      p == $ptr($array(T, sz), #r) || $in_array_extent_of(S, p, $ptr(T, #r), T, sz));

function {:inline true} $array_elt_emb(S:$state, p:$ptr, emb:$ptr) returns(bool)
    { $emb(S, p) == emb && !$is_volatile(S, p) && $typed(S, p) }

axiom (forall S:$state, #r:int, T:$ctype, sz:int, i:int :: 
      {$st(S, $idx($ptr(T, #r), i, T)), $ptr($array(T, sz), #r)} 
      {$ts(S, $idx($ptr(T, #r), i, T)), $ptr($array(T, sz), #r)} 
      $typed(S, $ptr($array(T, sz), #r)) ==> 
        0 <= i && i < sz ==> 
          $array_elt_emb(S, $idx($ptr($array(T, sz), #r), i, T), $ptr($array(T, sz), #r)));

function $array_members(p:$ptr, T:$ctype, sz:int) returns($ptrset);

axiom (forall p:$ptr, T:$ctype, sz:int, elem:$ptr ::
  { $set_in(elem, $array_members(p,T,sz)) }
  $set_in(elem, $array_members(p,T,sz)) <==> $in_array(elem, p, T, sz));

function $array_range_no_state(p:$ptr, T:$ctype, sz:int) returns($ptrset);
function $array_range(S:$state, p:$ptr, T:$ctype, sz:int) returns($ptrset)
  { $array_range_no_state(p, T, sz) }

axiom (forall S:$state, p:$ptr, #r:int, T:$ctype, sz:int ::
    { $set_in(p, $array_range(S, $ptr(T, #r), T, sz)) }
    $instantiate_bool($typed(S, p)) &&
    ($set_in(p, $array_range(S, $ptr(T, #r), T, sz)) <==> $in_array_full_extent_of(p, $ptr(T, #r), T, sz)));

axiom (forall p:$ptr, T:$ctype, sz:int, idx:int, S:$ptrset ::
    { $idx(p, idx, T), $set_disjoint($array_range_no_state(p, T, sz), S) }
    $set_disjoint($array_range_no_state(p, T, sz), S) ==>
    0 <= idx && idx < sz ==> $id_set_disjoint($idx(p, idx, T), $array_range_no_state(p, T, sz), S) == 1);

axiom (forall p:$ptr, T:$ctype, sz:int, idx:int, S:$ptrset ::
    { $idx(p, idx, T), $set_disjoint(S, $array_range_no_state(p, T, sz)) }
    $set_disjoint(S, $array_range_no_state(p, T, sz)) ==>
    0 <= idx && idx < sz ==> $id_set_disjoint($idx(p, idx, T), S, $array_range_no_state(p, T, sz)) == 2);

function $non_null_array_range(p:$ptr, T:$ctype, sz:int) returns($ptrset);
axiom (forall p:$ptr, #r:int, T:$ctype, sz:int ::
    { $set_in(p, $non_null_array_range($ptr(T, #r), T, sz)) }
    $set_in(p, $non_null_array_range($ptr(T, #r), T, sz)) <==> 
      #r != 0 &&
      $in_array_full_extent_of(p, $ptr(T, #r), T, sz));

function $non_null_extent(S:$state, p:$ptr) returns($ptrset);
axiom (forall q:$ptr, S:$state, p:$ptr ::
    { $set_in(q, $non_null_extent(S, p)) }
    $set_in(q, $non_null_extent(S, p)) <==>
      $ptr_neq(p, $null) && $set_in(q, $extent(S, p)));

function {:inline true} $as_array(p:$ptr, T:$ctype, sz:int) returns($ptr)
  { $ptr($array(T, sz), $ref(p)) }

function {:inline true} $array_eq(s1:$state, s2:$state, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { (forall #i:int :: {$idx(arr, #i, T)} 0 <= #i && #i < sz ==> $mem_eq(s1, s2, $idx(arr, #i, T))) }

// $index_within(p, arr) = ($ref(p) - $ref(arr)) / $sizeof($typ(arr))
// To avoid using division, we define a category of simple indices. 
//   $simple_index(p, arr) iff p == arr[k].f1.f2.f3...fN, where N >= 0.
// We're only interested in simple indices for verification.
function $index_within(p:$ptr, arr:$ptr) returns(int);
function $simple_index(p:$ptr, arr:$ptr) returns(bool);

axiom (forall p:$ptr, k:int :: {$idx(p, k, $typ(p))}
  $index_within($idx(p, k, $typ(p)), p) == k && $simple_index($idx(p, k, $typ(p)), p));

axiom (forall p:$ptr, q:$ptr, f:$field :: {$simple_index($dot(p, f), q)} {$index_within($dot(p, f), q)}
  $simple_index(p, q) ==> $simple_index($dot(p, f), q) && $index_within($dot(p, f), q) == $index_within(p, q));

axiom (forall p:$ptr, q:$ptr, f:$field, i:int, t:$ctype :: 
  {$simple_index($idx($dot(p, f), i, t), q)}
  {$index_within($idx($dot(p, f), i, t), q)}
  0 <= i && i < $embedded_array_size(f, t) && 
  $simple_index(p, q) ==> 
    $simple_index($idx($dot(p, f), i, t), q) && 
    $index_within($idx($dot(p, f), i, t), q) == $index_within(p, q));

function {:inline true} $in_array(q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { $in_range(0, $index_within(q, arr), sz - 1) && q == $idx(arr, $index_within(q, arr), T) }

function {:inline true} $in_array_full_extent_of(q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { $in_range(0, $index_within(q, arr), sz - 1) && $in_full_extent_of(q, $idx(arr, $index_within(q, arr), T)) }

function {:inline true} $in_array_extent_of(S:$state, q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { $in_range(0, $index_within(q, arr), sz - 1) && $in_extent_of(S, q, $idx(arr, $index_within(q, arr), T)) }

axiom (forall s1:$state, s2:$state, p:$ptr, t:$ctype, sz:int :: {$state_spans_the_same(s1, s2, p, $array(t, sz)), $is_primitive(t)}
  $is_primitive(t) ==>
    $state_spans_the_same(s1, s2, p, $array(t, sz)) ==> 
      (forall i:int :: {$mem(s2, $idx($ptr_cast(p, t), i, t))} 0 <= i && i < sz ==> 
        $mem_eq(s1, s2, $idx($ptr_cast(p, t), i, t))));

/*
function {:inline true} $in_array(q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { (exists #i:int :: { $idx(arr, #i, T) } $in_range(0, #i, sz - 1) && q == $idx(arr, #i, T)) }

function {:inline true} $in_array_full_extent_of(q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { (exists #i:int :: { $idx(arr, #i, T) } $in_range(0, #i, sz - 1) && $in_full_extent_of(q, $idx(arr, #i, T))) }

function {:inline true} $in_array_extent_of(S:$state, q:$ptr, arr:$ptr, T:$ctype, sz:int) returns(bool)
  { (exists #i:int :: { $idx(arr, #i, T) } $in_range(0, #i, sz - 1) && $in_extent_of(S, q, $idx(arr, #i, T))) }
*/

// --------------------------------------------------------------------------------
// Arithmetic
// --------------------------------------------------------------------------------

function {:inline true} $in_range(min:int, val:int, max:int) returns(bool)
  { min <= val && val <= max }

function {:inline true} $bool_to_int(v:bool) returns(int)
  { if v then 1 else 0 }

function {:inline true} $int_to_bool(x:int) returns(bool)
  { x != 0 }

function {:inline true} $read_bool(S:$state, p:$ptr) returns(bool)
  { $int_to_bool($mem(S, p)) }


// a hack, used when parameter to ITE is a quntified variable to prevent Z3 from crashing
function {:weight 0} $bool_id(x:bool) returns(bool) { x }

const $min.i1:int;
const $max.i1:int;
const $min.i2:int;
const $max.i2:int;
const $min.i4:int;
const $max.i4:int;
const $min.i8:int;
const $max.i8:int;
const $max.u1:int;
const $max.u2:int;
const $max.u4:int;
const $max.u8:int;

axiom ($min.i1 == -128);
axiom ($max.i1 ==  127);
axiom ($min.i2 == -32768);
axiom ($max.i2 ==  32767);
axiom ($min.i4 == -(65536*32768)  );
axiom ($max.i4 ==   65536*32768 -1);
axiom ($min.i8 == -(65536*65536*65536*32768)  );
axiom ($max.i8 ==   65536*65536*65536*32768 -1);
axiom ($max.u1 ==  255);
axiom ($max.u2 ==  65535);
axiom ($max.u4 ==  65536*65536-1);
axiom ($max.u8 ==  65536*65536*65536*65536-1);

function {:inline true} $in_range_i1(x:int) returns(bool) { $in_range($min.i1, x, $max.i1) }
function {:inline true} $in_range_i2(x:int) returns(bool) { $in_range($min.i2, x, $max.i2) }
function {:inline true} $in_range_i4(x:int) returns(bool) { $in_range($min.i4, x, $max.i4) }
function {:inline true} $in_range_i8(x:int) returns(bool) { $in_range($min.i8, x, $max.i8) }
function {:inline true} $in_range_u1(x:int) returns(bool) { $in_range(0, x, $max.u1) }
function {:inline true} $in_range_u2(x:int) returns(bool) { $in_range(0, x, $max.u2) }
function {:inline true} $in_range_u4(x:int) returns(bool) { $in_range(0, x, $max.u4) }
function {:inline true} $in_range_u8(x:int) returns(bool) { $in_range(0, x, $max.u8) }
function {:inline true} $in_range_ptr(p:$ptr) returns(bool) { $in_range_u8($ref(p)) }

function {:inline true} $in_range_div_i1(x:int, y:int) returns(bool) { y != -1 || x != $min.i1 }
function {:inline true} $in_range_div_i2(x:int, y:int) returns(bool) { y != -1 || x != $min.i2 }
function {:inline true} $in_range_div_i4(x:int, y:int) returns(bool) { y != -1 || x != $min.i4 }
function {:inline true} $in_range_div_i8(x:int, y:int) returns(bool) { y != -1 || x != $min.i8 }

function $ptr_to_u8($ptr) returns(int);
function $ptr_to_i8($ptr) returns(int);
function $ptr_to_u4($ptr) returns(int);
function $ptr_to_i4($ptr) returns(int);
function $ptr_to_u2($ptr) returns(int);
function $ptr_to_i2($ptr) returns(int);
function $ptr_to_u1($ptr) returns(int);
function $ptr_to_i1($ptr) returns(int);

axiom ($ptr_to_u8($null) == 0);
axiom ($ptr_to_i8($null) == 0);
axiom ($ptr_to_u4($null) == 0);
axiom ($ptr_to_i4($null) == 0);
axiom ($ptr_to_u2($null) == 0);
axiom ($ptr_to_i2($null) == 0);
axiom ($ptr_to_u1($null) == 0);
axiom ($ptr_to_i1($null) == 0);

function {:inline true} $u8_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $i8_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $u4_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $i4_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $u2_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $i2_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $u1_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }
function {:inline true} $i1_to_ptr(x : int) returns($ptr) { $ptr(^^void, x)  }

axiom (forall p:$ptr :: { $ptr_to_u8(p) } $in_range_u8($ref(p)) ==> $ptr_to_u8(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_i8(p) } $in_range_i8($ref(p)) ==> $ptr_to_i8(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_u4(p) } $in_range_u4($ref(p)) ==> $ptr_to_u4(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_i4(p) } $in_range_i4($ref(p)) ==> $ptr_to_i4(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_u2(p) } $in_range_u2($ref(p)) ==> $ptr_to_u2(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_i2(p) } $in_range_i2($ref(p)) ==> $ptr_to_i2(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_u1(p) } $in_range_u1($ref(p)) ==> $ptr_to_u1(p) == $ref(p));
axiom (forall p:$ptr :: { $ptr_to_i1(p) } $in_range_i1($ref(p)) ==> $ptr_to_i1(p) == $ref(p));

function {:weight 0} $byte_ptr_subtraction(p1:$ptr, p2:$ptr) returns(int)
  { $ref(p1) - $ref(p2) }

axiom (forall S:$state, r:int, t:$ctype :: {$mem(S, $ptr($as_in_range_t(t), r))}
  $good_state(S) ==> $in_range_t(t, $mem(S, $ptr($as_in_range_t(t), r))));

axiom (forall S:$state, r:int, t:$ctype :: {$mem(S, $ptr($ptr_to(t), r))}
  $good_state(S) ==> $in_range_phys_ptr($mem(S, $ptr($ptr_to(t), r))));

axiom (forall S:$state, r:int, t:$ctype :: {$mem(S, $ptr($spec_ptr_to(t), r))}
  $good_state(S) ==> $in_range_spec_ptr($mem(S, $ptr($spec_ptr_to(t), r))));

function $_pow2(int) returns(int);
axiom 
$_pow2(0) == 1 && $_pow2(1) == 2 && $_pow2(2) == 4 && $_pow2(3) == 8 && $_pow2(4) == 16 && $_pow2(5) == 32 &&
$_pow2(6) == 64 && $_pow2(7) == 128 && $_pow2(8) == 256 && $_pow2(9) == 512 && $_pow2(10) == 1024 && $_pow2(11) ==
 2048 && $_pow2(12) == 4096 && $_pow2(13) == 8192 && $_pow2(14) == 16384 && $_pow2(15) == 32768 && $_pow2(16) ==
65536 && $_pow2(17) == 131072 && $_pow2(18) == 262144 && $_pow2(19) == 524288 && $_pow2(20) == 1048576 && $_pow2(21)
== 2097152 && $_pow2(22) == 4194304 && $_pow2(23) == 8388608 && $_pow2(24) == 16777216 && $_pow2(25) == 33554432 &&
$_pow2(26) == 67108864 && $_pow2(27) == 134217728 && $_pow2(28) == 268435456 && $_pow2(29) == 536870912 && $_pow2(30)
== 1073741824 && $_pow2(31) == 2147483648 && $_pow2(32) == 4294967296 && $_pow2(33) == 8589934592 && $_pow2(34) ==
17179869184 && $_pow2(35) == 34359738368 && $_pow2(36) == 68719476736 && $_pow2(37) == 137438953472 && $_pow2(38) ==
274877906944 && $_pow2(39) == 549755813888 && $_pow2(40) == 1099511627776 && $_pow2(41) == 2199023255552 && $_pow2(42)
== 4398046511104 && $_pow2(43) == 8796093022208 && $_pow2(44) == 17592186044416 && $_pow2(45) == 35184372088832
&& $_pow2(46) == 70368744177664 && $_pow2(47) == 140737488355328 && $_pow2(48) == 281474976710656 && $_pow2(49) ==
562949953421312 && $_pow2(50) == 1125899906842624 && $_pow2(51) == 2251799813685248 && $_pow2(52) == 4503599627370496
&& $_pow2(53) == 9007199254740992 && $_pow2(54) == 18014398509481984 && $_pow2(55) == 36028797018963968 && $_pow2(56)
== 72057594037927936 && $_pow2(57) == 144115188075855872 && $_pow2(58) == 288230376151711744 && $_pow2(59) ==
 576460752303423488 && $_pow2(60) == 1152921504606846976 && $_pow2(61) == 2305843009213693952 && $_pow2(62) ==
4611686018427387904 && $_pow2(63) == 9223372036854775808;

function $in_range_ubits(bits:int, v:int) returns(bool)
  { $in_range(0, v, $_pow2(bits) - 1) }

function $unchecked_sbits(bits:int, v:int) returns(int);
axiom (forall bits:int, v:int :: {$unchecked_sbits(bits, v)}
  $in_range_sbits(bits, $unchecked_sbits(bits, v)) &&
  ($in_range_sbits(bits, v) ==> $unchecked_sbits(bits, v) == v));

function $in_range_sbits(bits:int, v:int) returns(bool)
  { $in_range(-$_pow2(bits-1), v, $_pow2(bits-1) - 1) }

function $unchecked_ubits(bits:int, v:int) returns(int);
axiom (forall bits:int, v:int :: {$unchecked_ubits(bits, v)}
  $in_range_ubits(bits, $unchecked_ubits(bits, v)) &&
  ($in_range_ubits(bits, v) ==> $unchecked_ubits(bits, v) == v));

function $_or(t:$ctype, x:int, y:int) returns(int);
function $_xor(t:$ctype, x:int, y:int) returns(int);
function $_and(t:$ctype, x:int, y:int) returns(int);
function $_not(t:$ctype, x:int) returns(int);

function {:weight 0} $unchk_add(t:$ctype, x:int, y:int) returns(int) { $unchecked(t, x + y) }
function {:weight 0} $unchk_sub(t:$ctype, x:int, y:int) returns(int) { $unchecked(t, x - y) }
function {:weight 0} $unchk_mul(t:$ctype, x:int, y:int) returns(int) { $unchecked(t, x * y) }
function {:weight 0} $unchk_div(t:$ctype, x:int, y:int) returns(int) { $unchecked(t, x / y) }
function {:weight 0} $unchk_mod(t:$ctype, x:int, y:int) returns(int) { $unchecked(t, x % y) }

function {:weight 0} $_shl(t:$ctype, x:int, y:int) returns(int)
  { $unchecked(t, x * $_pow2(y)) }
function {:weight 0} $_shr(x:int, y:int) returns(int)
  { x / $_pow2(y) }

function $bv_extract_signed(val:int, val_bitsize:int, from:int, to:int) returns(int);
function $bv_extract_unsigned(val:int, val_bitsize:int, from:int, to:int) returns(int);
function $bv_update(val:int, val_bitsize:int, from:int, to:int, repl:int) returns(int);

axiom (forall x:int, from:int, to:int, xs:int, val:int :: 
 { $bv_update(x, xs, from, to, val) }
 0 <= from && from < to && to <= xs ==>
 0 <= val && val < $_pow2(to - from) ==> 
   0 <= $bv_update(x, xs, from, to, val) && $bv_update(x, xs, from, to, val) < $_pow2(xs));

axiom (forall from:int, to:int, xs:int :: 
 { $bv_update(0, xs, from, to, 0) }
 0 <= from && from < to && to <= xs ==> $bv_update(0, xs, from, to, 0) == 0);

axiom (forall from:int, to:int, val:int, x:int, xs:int :: 
  {$bv_extract_signed($bv_update(x, xs, from, to, val), xs, from, to)}
  0 <= from && from < to && to <= xs ==>
  -$_pow2(to - from - 1) <= val && val < $_pow2(to - from - 1) ==> 
    $bv_extract_signed($bv_update(x, xs, from, to, val), xs, from, to) == val);

axiom (forall from:int, to:int, val:int, x:int, xs:int :: 
  {$bv_extract_unsigned($bv_update(x, xs, from, to, val), xs, from, to)}
  0 <= from && from < to && to <= xs ==>
  0 <= val && val < $_pow2(to - from) ==> 
    $bv_extract_unsigned($bv_update(x, xs, from, to, val), xs, from, to) == val);

axiom (forall from:int, to:int, x:int, xs:int :: 
  {$bv_extract_signed(x, xs, from, to)}
  0 <= from && from < to && to <= xs ==>
  $in_range(-$_pow2(to - from - 1), $bv_extract_signed(x, xs, from, to), $_pow2(to - from - 1) - 1));

axiom (forall from:int, to:int, x:int, xs:int :: 
  {$bv_extract_unsigned(x, xs, from, to)}
  0 <= from && from < to && to <= xs ==>
  $in_range(0, $bv_extract_unsigned(x, xs, from, to), $_pow2(to - from) - 1));

axiom (forall from:int, to:int, val:int, x:int, xs:int, from2:int, to2:int :: 
  {$bv_extract_signed($bv_update(x, xs, from, to, val), xs, from2, to2)}
  0 <= from && from < to && to <= xs ==>
  0 <= from2 && from2 < to2 && to2 <= xs ==>
  (to2 <= from || to <= from2) ==>
  $bv_extract_signed($bv_update(x, xs, from, to, val), xs, from2, to2) == $bv_extract_signed(x, xs, from2, to2));

axiom (forall from:int, to:int, val:int, x:int, xs:int, from2:int, to2:int :: 
  {$bv_extract_unsigned($bv_update(x, xs, from, to, val), xs, from2, to2)}
  0 <= from && from < to && to <= xs ==>
  0 <= from2 && from2 < to2 && to2 <= xs ==>
  (to2 <= from || to <= from2) ==>
  $bv_extract_unsigned($bv_update(x, xs, from, to, val), xs, from2, to2) == $bv_extract_unsigned(x, xs, from2, to2));

axiom (forall from:int, to:int, xs:int ::
  {$bv_extract_signed(0, xs, from, to)}
  0 <= from && from < to && to <= xs ==>
    $bv_extract_signed(0, xs, from, to) == 0);

axiom (forall from:int, to:int, xs:int ::
  {$bv_extract_unsigned(0, xs, from, to)}
  0 <= from && from < to && to <= xs ==>
    $bv_extract_unsigned(0, xs, from, to) == 0);

axiom (forall from:int, to:int, val:int, xs:int ::
  {$bv_extract_unsigned(val, xs, from, to)}
  0 <= from && from < to && to <= xs && 0 <= val ==>
    $bv_extract_unsigned(val, xs, from, to) == (val / $_pow2(from)) % $_pow2(to - from));

axiom (forall from:int, to:int, val:int, xs:int ::
  {$bv_extract_signed(val, xs, from, to)}
  0 <= from && from < to && to <= xs && 0 <= val && ((val / $_pow2(from)) % $_pow2(to - from) < $_pow2(to - from - 1)) ==>
    $bv_extract_signed(val, xs, from, to) == (val / $_pow2(from)) % $_pow2(to - from));

axiom (forall from:int, to:int, val:int, xs:int ::
  {$bv_extract_signed(val, xs, from, to)}
  0 <= from && from < to && to <= xs && 0 <= val && ((val / $_pow2(from)) % $_pow2(to - from) >= $_pow2(to - from - 1)) ==>
    $bv_extract_signed(val, xs, from, to) == $_pow2(to - from - 1) - (val / $_pow2(from)) % $_pow2(to - from));

/*
axiom (forall from:int, to:int, val:int :: {$sign_extend(from, to, $_bv_extract(val, to, 0, from))}
  (-$_pow2(from - 1) <= val && val < $_pow2(from - 1) ==> $sign_extend(from, to, $bv_extract(val, to, 0, from)) == val));

axiom (forall from:int, to:int, val:int :: {$sign_extend(from, to, val)}
  -$_pow2(from - 1) <= $sign_extend(from, to, val) && $sign_extend(from, to, val) < $_pow2(from - 1));

axiom (forall as:int, val:int, vs:int, from:int, to:int, bs:int ::
  {$bv_concat(0, as, $bv_extract(val, vs, from, to), bs)}
  as >= 1 ==>
    $bv_concat(0, as, $bv_extract(val, vs, from, to), bs) >= 0 &&
    $bv_concat(0, as, $bv_extract(val, vs, from, to), bs) < $_pow2(to - from));
    
axiom (forall s:int, from:int, to:int :: {$bv_extract(0, s, from, to)} 
  $bv_extract(0, s, from, to) == 0);

axiom (forall s1:int, s2: int :: {$bv_concat(0, s1, 0, s2)} 
  $bv_concat(0, s1, 0, s2) == 0);
*/

function $unchecked(t:$ctype, val:int) returns(int);
function $in_range_t(t:$ctype, x:int) returns(bool);

axiom (forall val:int :: {$in_range_t(^^i1, val)} $in_range_t(^^i1, val) <==> $in_range_i1(val));
axiom (forall val:int :: {$in_range_t(^^i2, val)} $in_range_t(^^i2, val) <==> $in_range_i2(val));
axiom (forall val:int :: {$in_range_t(^^i4, val)} $in_range_t(^^i4, val) <==> $in_range_i4(val));
axiom (forall val:int :: {$in_range_t(^^i8, val)} $in_range_t(^^i8, val) <==> $in_range_i8(val));
axiom (forall val:int :: {$in_range_t(^^u1, val)} $in_range_t(^^u1, val) <==> $in_range_u1(val));
axiom (forall val:int :: {$in_range_t(^^u2, val)} $in_range_t(^^u2, val) <==> $in_range_u2(val));
axiom (forall val:int :: {$in_range_t(^^u4, val)} $in_range_t(^^u4, val) <==> $in_range_u4(val));
axiom (forall val:int :: {$in_range_t(^^u8, val)} $in_range_t(^^u8, val) <==> $in_range_u8(val));
axiom (forall val:int :: {$in_range_t(^^mathint, val)} $in_range_t(^^mathint, val));

axiom (forall t:$ctype, val:int :: {$unchecked(t, val)} $in_range_t(t, val) ==> $unchecked(t, val) == val);
axiom (forall t:$ctype, val:int :: {$unchecked(t, val)} $in_range_t(t, $unchecked(t, val)));

axiom (forall val:int :: { $unchecked(^^u1, $unchecked(^^i1, val)) } $in_range_u1(val) ==> $unchecked(^^u1, $unchecked(^^i1, val)) == val);
axiom (forall val:int :: { $unchecked(^^u2, $unchecked(^^i2, val)) } $in_range_u2(val) ==> $unchecked(^^u2, $unchecked(^^i2, val)) == val);
axiom (forall val:int :: { $unchecked(^^u4, $unchecked(^^i4, val)) } $in_range_u4(val) ==> $unchecked(^^u4, $unchecked(^^i4, val)) == val);
axiom (forall val:int :: { $unchecked(^^u8, $unchecked(^^i8, val)) } $in_range_u8(val) ==> $unchecked(^^u8, $unchecked(^^i8, val)) == val);
axiom (forall val:int :: { $unchecked(^^i1, $unchecked(^^u1, val)) } $in_range_i1(val) ==> $unchecked(^^i1, $unchecked(^^u1, val)) == val);
axiom (forall val:int :: { $unchecked(^^i2, $unchecked(^^u2, val)) } $in_range_i2(val) ==> $unchecked(^^i2, $unchecked(^^u2, val)) == val);
axiom (forall val:int :: { $unchecked(^^i4, $unchecked(^^u4, val)) } $in_range_i4(val) ==> $unchecked(^^i4, $unchecked(^^u4, val)) == val);
axiom (forall val:int :: { $unchecked(^^i8, $unchecked(^^u8, val)) } $in_range_i8(val) ==> $unchecked(^^i8, $unchecked(^^u8, val)) == val);

// The semantics of $_and/$_or/...
//   Clip the number given to the appropriate range (i.e. take the lowest N bits) and perform the operation.


axiom (forall t:$ctype, x:int, y:int, z:int :: { x % $_pow2(y), $_and(t, x, z) } 
  $in_range_t(t, x) &&
  $in_range_t(t, $_pow2(y) - 1) &&
  x >= 0 ==>
    x % $_pow2(y) == $_and(t, x, $_pow2(y) - 1));

axiom (forall i: int, j: int :: { i / j }  0 <= i && 0 < j ==> i / j <= i);

axiom (forall i: int, j: int :: { i / j }  i > 0 && j > 0 ==> i - j < (i / j) * j && (i / j) * j <= i);
axiom (forall i: int :: { i / i }  i != 0 ==> i / i == 1);
axiom (forall i: int :: { 0 / i }  i != 0 ==> 0 / i == 0);

// from Spec# prelude, needs review
axiom (forall x: int, y: int :: { x % y } { x / y } x % y == x - x / y * y);
axiom (forall x: int, y: int :: { x % y } 0 <= x && 0 < y ==> 0 <= x % y && x % y < y);
axiom (forall x: int, y: int :: { x % y } 0 <= x && y < 0 ==> 0 <= x % y && x % y < 0 - y);
axiom (forall x: int, y: int :: { x % y } x <= 0 && 0 < y ==> 0 - y < x % y && x % y <= 0);
axiom (forall x: int, y: int :: { x % y } x <= 0 && y < 0 ==> y < x % y && x % y <= 0);
// Those three use +/- in triggers, won't work in Z3
//axiom (forall x: int, y: int :: { (x + y) % y } 0 <= x && 0 <= y ==> (x + y) % y == x % y);
//axiom (forall x: int, y: int :: { (y + x) % y } 0 <= x && 0 <= y ==> (y + x) % y == x % y);
//axiom (forall x: int, y: int :: { (x - y) % y } 0 <= x - y && 0 <= y ==> (x - y) % y == x % y);

// Too expensive
//axiom (forall a: int, b: int, d: int :: { a % d, b % d } 2 <= d && a % d == b % d && a < b ==> a + d <= b);

axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } 0 <= x && $in_range_t(t, x) ==> 0 <= $_and(t, x, y) && $_and(t, x, y) <= x);
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } 0 <= x && 0 <= y && $in_range_t(t, x) && $in_range_t(t, y) ==> $_and(t, x, y) <= x && $_and(t, x, y) <= y);
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } 0 <= x && 0 <= y && $in_range_t(t, x) && $in_range_t(t, y) ==> 0 <= $_or(t, x, y) && $_or(t, x, y) <= x + y);
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } 0 <= x && 0 <= y && $in_range_t(t, x) && $in_range_t(t, y) ==> x <= $_or(t, x, y) && y <= $_or(t, x, y));
axiom (forall t:$ctype, x: int, y: int, z: int :: { $_or(t, x,y), $_pow2(z) } 
  0 <= x && 0 <= y && 0 <= z && z < 64 && x < $_pow2(z) && y < $_pow2(z) && $in_range_t(t, x) && $in_range_t(t, y) ==> $_or(t, x, y) < $_pow2(z) );

axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } $in_range_u1(x) && $in_range_u1(y) ==> $in_range_u1($_or(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } $in_range_u2(x) && $in_range_u2(y) ==> $in_range_u2($_or(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } $in_range_u4(x) && $in_range_u4(y) ==> $in_range_u4($_or(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } $in_range_u8(x) && $in_range_u8(y) ==> $in_range_u8($_or(t, x, y)));

axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } $in_range_u1(x) && $in_range_u1(y) ==> $in_range_u1($_and(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } $in_range_u2(x) && $in_range_u2(y) ==> $in_range_u2($_and(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } $in_range_u4(x) && $in_range_u4(y) ==> $in_range_u4($_and(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } $in_range_u8(x) && $in_range_u8(y) ==> $in_range_u8($_and(t, x, y)));

axiom (forall t:$ctype, x: int, y: int :: { $_xor(t, x, y) } $in_range_u1(x) && $in_range_u1(y) ==> $in_range_u1($_xor(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_xor(t, x, y) } $in_range_u2(x) && $in_range_u2(y) ==> $in_range_u2($_xor(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_xor(t, x, y) } $in_range_u4(x) && $in_range_u4(y) ==> $in_range_u4($_xor(t, x, y)));
axiom (forall t:$ctype, x: int, y: int :: { $_xor(t, x, y) } $in_range_u8(x) && $in_range_u8(y) ==> $in_range_u8($_xor(t, x, y)));

axiom (forall t:$ctype, x: int :: { $_not(t, x) }  $in_range_t(t, $_not(t, x)));

//axiom (forall t:$ctype, x: int :: { $_not(t, x) } $in_range_u4(x) ==> $in_range_u4($_not(t, x)));
//axiom (forall t:$ctype, x: int :: { $_not(t, x) } $in_range_u8(x) ==> $in_range_u8($_not(t, x)));

axiom (forall t:$ctype, x: int :: { $_or(t, x, $_not(t, x)) }  $_or(t, x, $_not(t, x)) == $_not(t, 0));
axiom (forall t:$ctype, x: int :: { $_and(t, x, $_not(t, x)) }  $_and(t, x, $_not(t, x)) == 0);
axiom (forall t:$ctype, x: int :: { $_or(t, x, 0) }  $in_range_t(t, x) ==> $_or(t, x, 0) == x);
axiom (forall t:$ctype, x: int :: { $_or(t, x, $_not(t, 0)) }  $_or(t, x, $_not(t, 0)) == $_not(t, 0));
axiom (forall t:$ctype, x: int :: { $_or(t, x, x) } $in_range_t(t, x) ==>  $_or(t, x, x) == x);
axiom (forall t:$ctype, x: int :: { $_and(t, x, 0) }  $_and(t, x, 0) == 0);
axiom (forall t:$ctype, x: int :: { $_and(t, x, $_not(t, 0)) } $in_range_t(t, x) ==>  $_and(t, x, $_not(t, 0)) == x);
axiom (forall t:$ctype, x: int :: { $_and(t, x, x) } $in_range_t(t, x) ==> $_and(t, x,x) == x);
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, $_or(t, x, y), y) } $_and(t, $_or(t, x, y), y) == y);
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, $_or(t, x, y), x) } $_and(t, $_or(t, x, y), x) == x);
axiom (forall t:$ctype, x: int :: { $_xor(t, x, 0) }  $in_range_t(t, x) ==> $_xor(t, x, 0) == x);
axiom (forall t:$ctype, x: int :: { $_xor(t, x, x) }  $_xor(t, x, x) == 0);
axiom (forall t:$ctype, x: int :: { $_xor(t, x, $_not(t, 0)) }  $_xor(t, x, $_not(t, 0)) == $_not(t, x));
axiom (forall t:$ctype, x: int :: { $_not(t, $_not(t, x)) }  $in_range_t(t, x) ==> $_not(t, $_not(t, x)) == x);
axiom (forall t:$ctype, x: int, y: int :: { $_or(t, x, y) } $_or(t, x, y) == $_or(t, y, x));
axiom (forall t:$ctype, x: int, y: int :: { $_xor(t, x, y) } $_xor(t, x, y) == $_xor(t, y, x));
axiom (forall t:$ctype, x: int, y: int :: { $_and(t, x, y) } $_and(t, x, y) == $_and(t, y, x));
  

// extra function symbol for multiplication to prevent z3 from applying commutativity half-heartedly
function {:weight 0} $_mul(x:int, y:int) returns (int) { x * y }

// --------------------------------------------------------------------------------
// Strings
// --------------------------------------------------------------------------------

function $get_string_literal(id:int, length:int) returns($ptr);
axiom (forall id:int, length:int :: {$get_string_literal(id, length)} $is($get_string_literal(id, length), ^^u1));
axiom (forall id:int, length:int, S:$state :: 
  {$typed(S, $get_string_literal(id, length))}
  {$is_array(S, $get_string_literal(id, length), ^^u1, length)}
  $good_state(S) ==>
    $typed(S, $get_string_literal(id, length)) &&
    $is_thread_local_array(S, $get_string_literal(id, length), ^^u1, length));

// --------------------------------------------------------------------------------
// Function pointers
// --------------------------------------------------------------------------------

function $get_fnptr(no:int, t:$ctype) returns($ptr)
  { $ptr(t, $get_fnptr_ref(no)) }


function $get_fnptr_ref(no:int) returns(int);
function $get_fnptr_inv(rf:int) returns(int);

axiom (forall no:int :: $get_fnptr_inv($get_fnptr_ref(no)) == no);
//axiom (forall rf:int :: $get_fnptr_ref($get_fnptr_rev(rf)) == rf);

axiom (forall S:$state, no:int, t:$ctype :: 
  {$ts(S, $get_fnptr(no, t))} {$st(S, $get_fnptr(no, t))}
  $is_fnptr_type(t) &&
  $good_state(S) ==> $mutable(S, $get_fnptr(no, t)));

function $is_fnptr_type(t:$ctype) returns(bool);
function $is_math_type(t:$ctype) returns(bool);
axiom (forall t:$ctype :: {$is_math_type(t)} $is_math_type(t) ==> $is_primitive(t));
axiom (forall t:$ctype :: {$is_fnptr_type(t)} $is_fnptr_type(t) ==> $is_primitive(t));



// --------------------------------------------------------------------------------
// Claims
// --------------------------------------------------------------------------------

function $claims_obj(claim:$ptr, obj:$ptr) returns(bool);
function $valid_claim(S:$state, claim:$ptr) returns(bool);

axiom (forall S:$state, c:$ptr :: {$full_stop(S), $valid_claim(S, c)}
  $full_stop(S) && $closed(S, c) ==> $valid_claim(S, c));

axiom (forall S:$state, c:$ptr :: {$valid_claim(S, c)}
  $valid_claim(S, c) ==> $closed(S, c) && $invok_state(S));

function {:inline true} $claim_initial_assumptions(#s1:$state, c:$ptr, tok:$token) returns (bool)
  { $good_state_ext(tok, #s1) &&
    $closed_is_transitive(#s1) &&
    true
  }

function {:inline true} $claim_transitivity_assumptions(#s1:$state, #s2:$state, c:$ptr, tok:$token) returns (bool)
  { $full_stop_ext(tok, #s1) &&
    $good_state_ext(tok, #s2) &&
    $closed_is_transitive(#s1) &&
    $closed_is_transitive(#s2) &&
    $forall_inv2_when_closed(#s1, #s2) &&
    $valid_claim(#s1, c) &&
    $closed(#s2, c) &&
    true
    }

function {:inline true} $valid_claim_impl(S0:$state, S1:$state) returns(bool)
  { (forall r:int :: {$closed(S1, $ptr(^^claim, r))}
       $closed(S0, $ptr(^^claim, r)) && $closed(S1, $ptr(^^claim, r)) ==> $valid_claim(S1, $ptr(^^claim, r))) }

function $claims_claim(c1:$ptr, c2:$ptr) returns(bool);
axiom (forall c1:$ptr, c2:$ptr :: {$claims_claim(c1, c2)}
  $is(c1, ^^claim) && $is(c2, ^^claim) &&
  (forall S:$state :: $valid_claim(S, c1) ==> $closed(S, c2)) 
  ==>
  $claims_claim(c1, c2));

axiom (forall S:$state, c1:$ptr, c2:$ptr :: {$valid_claim(S, c1), $claims_claim(c1, c2)}
  $valid_claim(S, c1) && $claims_claim(c1, c2) ==> $valid_claim(S, c2));

axiom (forall S:$state, c:$ptr, o:$ptr ::
    {$closed(S, c), $claims_obj(c, o)}
    $good_state(S) ==>
      $claims_obj(c, o) && $closed(S, c) ==> $instantiate_ptrset($owns(S, o)) && $closed(S, o) && $ref_cnt(S, o) > 0);

axiom (forall S:$state, c:$ptr, o:$ptr ::
    {$valid_claim(S, c), $claims_obj(c, o)}
    $valid_claim(S, c) && $claims_obj(c, o) ==> $inv(S, o, $typ(o)));

axiom (forall S:$state, c:$ptr, r:int ::
    {$valid_claim(S, c), $claims_obj(c, $ptr(^^claim, r))}
    $valid_claim(S, c) && $claims_obj(c, $ptr(^^claim, r)) ==>
      $valid_claim(S, $ptr(^^claim, r)));

function {:weight 0} $not_shared(S:$state, p:$ptr) returns(bool)
  { $wrapped(S, p, $typ(p)) && (!$is_claimable($typ(p)) || $ref_cnt(S, p) == 0) }

function {:weight 0} $claimed_closed(s:$state, p:$ptr) returns(bool)
  { $closed(s, p) }

axiom (forall S:$state, p:$ptr :: {$invok_state(S), $claimed_closed(S, p)}
  $invok_state(S) && $claimed_closed(S, p) ==> $inv(S, p, $typ(p)));

// called at the beginning of an atomic block to simulate other threads
procedure $atomic_havoc();
  modifies $s;
  ensures $writes_nothing(old($s), $s);
  ensures (forall r:int, t:$ctype, f:$field :: 
              {$is_thread_local_storage(t), $select.mem($memory($s), $dot($ptr(t, r), f))}
              $is_thread_local_storage(t) &&
              $owner(old($s), $ptr(t, r)) == $me() ==>
                $mem_eq(old($s), $s, $dot($ptr(t, r), f)));

  ensures (forall r:int, t:$ctype, f:$field, i:int, sz:int, t2:$ctype :: 
              {$is_thread_local_storage(t), $is_primitive_embedded_volatile_array(f, sz, t2), $select.mem($memory($s), $idx($dot($ptr(t, r), f), i, t2))}
              $is_thread_local_storage(t) &&
              $is_primitive_embedded_volatile_array(f, sz, t2) &&
              0 <= i && i < sz &&
              $owner(old($s), $ptr(t, r)) == $me() ==>
                $mem_eq(old($s), $s, $idx($dot($ptr(t, r), f), i, t2)));

  ensures (forall p:$ptr, f:$field ::
    {$not_shared(old($s), p), $select.mem($memory($s), $dot(p, f))}
    $not_shared(old($s), p) ==> $mem_eq(old($s), $s, $dot(p, f)));
  ensures $timestamp_post_strict(old($s), $s);

const unique $no_claim : $ptr;
axiom $no_claim == $ptr(^^claim, 0);

procedure $alloc_claim() returns(#r:$ptr);
  modifies $s;
  ensures $owns($s, #r) == $set_empty();
  ensures $memory($s) == $memory(old($s));
  ensures $typemap($s) == $typemap(old($s));
  ensures (forall p:$ptr :: {$st($s, p)}
    p == #r || $st_eq(old($s), $s, p));
  ensures $wrapped($s, #r, ^^claim);
  ensures $is_fresh(old($s), $s, #r);
  ensures $in_range_spec_ptr($ref(#r));
  ensures $ref_cnt($s, #r) == 0;
  ensures !$closed(old($s), #r) && $owner(old($s), #r) != $me();
  ensures $timestamp_post_strict(old($s), $s);
  ensures #r != $no_claim;

// FIXME should it havoc non thread local state?
procedure $unclaim(c:$ptr);
  modifies $s;
  // TOKEN: the claim is wrapped
  requires $wrapped($s, c, ^^claim);
  // TOKEN: the claim has no outstanding references
  requires $ref_cnt($s, c) == 0;
  ensures (forall p:$ptr :: {$st($s, p)} $st_eq(old($s), $s, p) || p == c);
  ensures $typemap(old($s)) == $typemap($s);
  ensures $memory(old($s)) == $memory($s);
  ensures $timestamp_post(old($s), $s);
  ensures $good_state($s);
  ensures !$closed($s, c);

procedure $kill_claim(c:$ptr);
  modifies $s;
  ensures (forall p:$ptr :: {$st($s, p)} $st_eq(old($s), $s, p) || p == c);
  ensures $typemap(old($s)) == $typemap($s);
  ensures $memory(old($s)) == $memory($s);
  ensures $timestamp_post(old($s), $s);
  ensures $good_state($s);
  ensures !$closed($s, c);

function $claims_upgrade(the_new:$ptr, the_old:$ptr) returns(bool)
  { (forall o:$ptr :: $claims_obj(the_old, o) ==> $claims_obj(the_new, o)) }

function {:weight 0} $ref_cnt(S:$state, p:$ptr) returns(int)
  { $st_ref_cnt($st(S, p)) }

function $is_claimable($ctype) returns(bool);
axiom $is_claimable(^^claim);

function $is_thread_local_storage($ctype) returns (bool);


function $account_claim(S:$state, c:$ptr, o:$ptr) returns(bool)
  { $good_state(S) && $closed(S, c) && $claims_obj(c, o) }

function $claim_no(S:$state, o:$ptr, idx:int) returns($ptr);
function $claim_idx(o:$ptr, c:$ptr) returns(int);

axiom (forall S:$state, c:$ptr, o:$ptr :: {$account_claim(S, c, o)}
  $account_claim(S, c, o) ==>
    $claim_no(S, o, $claim_idx(o, c)) == c &&
    0 <= $claim_idx(o, c) && $claim_idx(o, c) < $ref_cnt(S, o));
    

// --------------------------------------------------------------------------------
// Frame axiom ordering
// --------------------------------------------------------------------------------

function $frame_level($pure_function) returns(int);
const $current_frame_level : int;

// assumed at the beginning of all ``normal'' functions (i.e., not frame axiom read checks)
// the $state is there only as a placeholder
function {:inline true} $can_use_all_frame_axioms(s:$state) returns(bool)
  { (forall f:$pure_function :: {$frame_level(f)} $frame_level(f) < $current_frame_level) }

function {:inline true} $can_use_frame_axiom_of(f:$pure_function) returns(bool)
  { $frame_level(f) < $current_frame_level }


// reads checking

function $reads_check_pre(s:$state) returns(bool);
function $reads_check_post(s:$state) returns(bool);
procedure $reads_havoc();
  modifies $s;
  // TOKEN: called nothing before reads_havoc()
  requires $reads_check_pre($s);
  ensures $reads_check_post($s);
  ensures $call_transition(old($s), $s);


function $start_here() returns(bool);

// --------------------------------------------------------------------------------
// Conversion functions
// --------------------------------------------------------------------------------

function $ptrset_to_int($ptrset) returns(int);
function $int_to_ptrset(int) returns($ptrset);
axiom (forall p:$ptrset :: $int_to_ptrset($ptrset_to_int(p)) == p);

function $version_to_int($version) returns(int);
function $int_to_version(int) returns($version);
axiom (forall p:$version :: $int_to_version($version_to_int(p)) == p);

function $vol_version_to_int($vol_version) returns(int);
function $int_to_vol_version(int) returns($vol_version);
axiom (forall p:$vol_version :: $int_to_vol_version($vol_version_to_int(p)) == p);

function $ptr_to_int($ptr) returns(int);
function $int_to_ptr(int) returns($ptr);
axiom (forall p:$ptr :: $int_to_ptr($ptr_to_int(p)) == p);

// --------------------------------------------------------------------------------
// Skinny writes
// --------------------------------------------------------------------------------

function $precise_test($ptr) returns(bool);

function $updated_only_values(S1:$state, S2:$state, W:$ptrset) returns(bool);
function $updated_only_domains(S1:$state, S2:$state, W:$ptrset) returns(bool);

axiom (forall S1:$state, S2:$state, W:$ptrset ::
  {$updated_only_values(S1, S2, W)}
  (forall p:$ptr :: {$dont_instantiate(p)}
    ($is_primitive($typ(p)) || $is_non_primitive($typ(p))) ==>
      $typed(S1, p) && !$irrelevant(S1, p) ==> $mem_eq(S1, S2, p) || $set_in(p, W))
  ==> $updated_only_values(S1, S2, W));

axiom (forall S1:$state, S2:$state, W:$ptrset ::
  {$updated_only_domains(S1, S2, W)}
  (forall p:$ptr :: {$dont_instantiate(p)}
    $set_in(p, W) && !$is_primitive_ch($typ(p)) ==>
      $mem_eq(S1, S2, p) || $domain_updated_at(S1, S2, p, W))
  ==> $updated_only_domains(S1, S2, W));

/*
function $version_store(v:$version, W:$ptrset) returns($version);
axiom (forall v:$version, p:$ptr, W:$ptrset :: {$fetch_from_domain($version_store(v, W), p)}
   $is_primitive_ch($typ(p)) && !$set_in(p, W) ==>
     $fetch_from_domain($version_store(v, W), p) == $fetch_from_domain(v, p));

axiom (forall v:$version, W1:$ptrset, W2:$ptrset :: 
  {$version_store($version_store(v, W1), W2), $version_store(v, $set_union(W1, W2)) }
  $version_store($version_store(v, W1), W2) == $version_store(v, $set_union(W1, W2)));
*/

function $domain_updated_at(S1:$state, S2:$state, p:$ptr, W:$ptrset) returns(bool)
  { (forall q:$ptr :: {$fetch_from_domain($read_version(S2, p), q)}
       $is_primitive_ch($typ(q)) && !$set_in(q, W) ==>
         $fetch_from_domain($read_version(S1, p), q) ==
         $fetch_from_domain($read_version(S2, p), q)) &&
    $domain(S1, p) == $domain(S2, p) }

// --------------------------------------------------------------------------------
// Floating point arithmetic - currently uninterpreted
// --------------------------------------------------------------------------------

function $add_f4(x:$primitive, y:$primitive) returns($primitive);
function $sub_f4(x:$primitive, y:$primitive) returns($primitive);
function $mul_f4(x:$primitive, y:$primitive) returns($primitive);
function $div_f4(x:$primitive, y:$primitive) returns($primitive);
function $neg_f4(x:$primitive) returns($primitive);
function $lt_f4(x:$primitive, y:$primitive) returns(bool);
function $leq_f4(x:$primitive, y:$primitive) returns(bool);
function $gt_f4(x:$primitive, y:$primitive) returns(bool);
function $geq_f4(x:$primitive, y:$primitive) returns(bool);
function $add_f8(x:$primitive, y:$primitive) returns($primitive);
function $sub_f8(x:$primitive, y:$primitive) returns($primitive);
function $mul_f8(x:$primitive, y:$primitive) returns($primitive);
function $div_f8(x:$primitive, y:$primitive) returns($primitive);
function $neg_f8(x:$primitive) returns($primitive);
function $lt_f8(x:$primitive, y:$primitive) returns(bool);
function $leq_f8(x:$primitive, y:$primitive) returns(bool);
function $gt_f8(x:$primitive, y:$primitive) returns(bool);
function $geq_f8(x:$primitive, y:$primitive) returns(bool);

// --------------------------------------------------------------------------------
// Counter Example Visualizer things
// --------------------------------------------------------------------------------

type cf_event;
type var_locglob;

const unique conditional_moment : cf_event;
const unique took_then_branch : cf_event;
const unique took_else_branch : cf_event;

const unique loop_register : cf_event;
const unique loop_entered : cf_event;
const unique loop_exited : cf_event;

const unique cev_local : var_locglob;
const unique cev_global : var_locglob;
const unique cev_parameter : var_locglob;
const unique cev_implicit : var_locglob;

function #cev_init(n:int) returns(bool);
function #cev_save_position(n:int) returns($token);
function #cev_var_intro(n:int, locorglob:var_locglob, name:$token, val:int, typ: $ctype) returns(bool);
function #cev_var_update(n:int, locorglob:var_locglob, name:$token, val:int) returns(bool);
function #cev_control_flow_event(n:int, tag : cf_event) returns(bool);
function #cev_function_call(n:int) returns(bool);

var $cev_pc : int;

procedure $cev_step(pos: $token);
  modifies $cev_pc;
  ensures #cev_save_position(old($cev_pc)) == pos;
  ensures $cev_pc == old($cev_pc) + 1;

procedure $cev_pre_loop(pos: $token) returns (oldPC: int);
  modifies $cev_pc;
  ensures #cev_control_flow_event(old($cev_pc), conditional_moment);
  ensures #cev_save_position(old($cev_pc)) == pos;
  ensures oldPC == old($cev_pc) && $cev_pc == old($cev_pc) + 1;

// That's all folks.
