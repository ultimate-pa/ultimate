//#VccPrelude
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure adda(P#a: int, P#b: int) returns ($result: int);
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation adda(P#a: int, P#b: int) returns ($result: int)
{
  var #wrTime$1^4.1: int;
  var #stackframe: int;

  anon1:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^4.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^4.1, #loc.a, P#a, ^^i4);
    assume $local_value_is($s, #tok$1^4.1, #loc.b, P#b, ^^i4);
    assume #wrTime$1^4.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^4.1, #p) } $in_writes_at(#wrTime$1^4.1, #p) == false);
    // assume @in_range_i4(a); 
    assume $in_range_i4(P#a);
    // assume @in_range_i4(b); 
    assume $in_range_i4(P#b);
    // assert @in_range_i4(+(a, b)); 
    assert $in_range_i4(P#a + P#b);
    // return +(a, b); 
    $result := P#a + P#b;
    assert $position_marker();
    goto #exit;

  anon2:
    // empty

  #exit:
}



procedure addb(P#a: int, P#b: int) returns ($result: int);
  requires P#a + P#b <= 2147483647;
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation addb(P#a: int, P#b: int) returns ($result: int)
{
  var #wrTime$1^9.1: int;
  var #stackframe: int;

  anon3:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^9.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^9.1, #loc.a, P#a, ^^i4);
    assume $local_value_is($s, #tok$1^9.1, #loc.b, P#b, ^^i4);
    assume #wrTime$1^9.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^9.1, #p) } $in_writes_at(#wrTime$1^9.1, #p) == false);
    // assume @in_range_i4(a); 
    assume $in_range_i4(P#a);
    // assume @in_range_i4(b); 
    assume $in_range_i4(P#b);
    // assert @in_range_i4(+(a, b)); 
    assert $in_range_i4(P#a + P#b);
    // return +(a, b); 
    $result := P#a + P#b;
    assert $position_marker();
    goto #exit;

  anon4:
    // empty

  #exit:
}



procedure addc(P#a: int, P#b: int) returns ($result: int);
  requires P#a + P#b >= -2147483648;
  requires P#a + P#b <= 2147483647;
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation addc(P#a: int, P#b: int) returns ($result: int)
{
  var #wrTime$1^15.1: int;
  var #stackframe: int;

  anon5:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^15.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^15.1, #loc.a, P#a, ^^i4);
    assume $local_value_is($s, #tok$1^15.1, #loc.b, P#b, ^^i4);
    assume #wrTime$1^15.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^15.1, #p) } $in_writes_at(#wrTime$1^15.1, #p) == false);
    // assume @in_range_i4(a); 
    assume $in_range_i4(P#a);
    // assume @in_range_i4(b); 
    assume $in_range_i4(P#b);
    // assert @in_range_i4(+(a, b)); 
    assert $in_range_i4(P#a + P#b);
    // return +(a, b); 
    $result := P#a + P#b;
    assert $position_marker();
    goto #exit;

  anon6:
    // empty

  #exit:
}



const unique #tok$1^15.1: $token;

const unique #tok$1^9.1: $token;

const unique #loc.b: $token;

const unique #loc.a: $token;

const unique #tok$1^4.1: $token;

const unique #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Caddc.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Caddc.cpp);
