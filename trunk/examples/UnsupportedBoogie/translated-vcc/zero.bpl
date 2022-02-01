//#VccPrelude
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure simpleLoop(P#x: int, P#l: int);
  requires $is_array($s, $ptr(^^i4, P#x), ^^i4, P#l);
  modifies $s, $cev_pc;
  ensures (forall Q#i$1^6.11#tc1: int :: $in_range_u4(Q#i$1^6.11#tc1) ==> 0 <= Q#i$1^6.11#tc1 && Q#i$1^6.11#tc1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#i$1^6.11#tc1, ^^i4)) == 0);
  free ensures (forall #p: $ptr :: {:weight 0} { $mem($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $mem_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $st($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $st_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $ts($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $ts_eq(old($s), $s, #p)) && $timestamp_post(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation simpleLoop(P#x: int, P#l: int)
{
  var loopState#0: $state;
  var L#i: int where $in_range_u4(L#i);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon4:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^3.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^3.1, #loc.x, $ptr_to_int($ptr(^^i4, P#x)), $ptr_to(^^i4)) && $local_value_is_ptr($s, #tok$1^3.1, #loc.x, $ptr(^^i4, P#x), $ptr_to(^^i4));
    assume $local_value_is($s, #tok$1^3.1, #loc.l, P#l, ^^u4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == $set_in(#p, $array_range($s, $ptr(^^i4, P#x), ^^i4, P#l)));
    assume (forall #p: $ptr :: { $st($s, #p) } { $ts($s, #p) } $set_in(#p, $array_range($s, $ptr(^^i4, P#x), ^^i4, P#l)) ==> $thread_owned_or_even_mutable($s, #p));
    // assume @in_range_phys_ptr((mathint)x); 
    assume $in_range_phys_ptr($ref($ptr(^^i4, P#x)));
    // assume @in_range_u4(l); 
    assume $in_range_u4(P#l);
    // uint32_t i; 
    assume $local_value_is($s, #tok$1^8.2, #loc.i, L#i, ^^u4);
    // i := 0; 
    L#i := 0;
    assume $local_value_is($s, #tok$1^8.2, #loc.i, L#i, ^^u4);
    loopState#0 := $s;
    while (true)
      invariant (forall Q#j$1^10.14#tc1: int :: $in_range_u4(Q#j$1^10.14#tc1) ==> 0 <= Q#j$1^10.14#tc1 && Q#j$1^10.14#tc1 < L#i ==> $mem($s, $idx($ptr(^^i4, P#x), Q#j$1^10.14#tc1, ^^i4)) == 0);
    {
      anon3:
        assume (forall #p: $ptr :: {:weight 0} { $mem($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $mem_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $st($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $st_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $ts($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $ts_eq(old($s), $s, #p)) && $timestamp_post(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume true;
        assume $full_stop_ext(#tok$1^9.2, $s);
        assume $local_value_is($s, #tok$1^9.2, #loc.i, L#i, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.l, P#l, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.x, $ptr_to_int($ptr(^^i4, P#x)), $ptr_to(^^i4)) && $local_value_is_ptr($s, #tok$1^9.2, #loc.x, $ptr(^^i4, P#x), $ptr_to(^^i4));
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (<(i, l)) ...
        if (L#i < P#l)
        {
          anon1:
            // assert @_vcc_typed2(@state, x[i]); 
            assert $typed2($s, $idx($ptr(^^i4, P#x), L#i, ^^i4), ^^i4);
            // assert @prim_writes_check(x[i]); 
            assert $writable($s, #wrTime$1^3.1, $idx($ptr(^^i4, P#x), L#i, ^^i4));
            // *x[i] := 0; 
            call $write_int($idx($ptr(^^i4, P#x), L#i, ^^i4), 0);
            assume $full_stop_ext(#tok$1^12.3, $s);
            // assert @in_range_u4(+(i, 1)); 
            assert $in_range_u4(L#i + 1);
            // i := +(i, 1); 
            L#i := L#i + 1;
            assume $local_value_is($s, #tok$1^13.3, #loc.i, L#i, ^^u4);
        }
        else
        {
          anon2:
            // goto #break_1; 
            goto #break_1;
        }

      #continue_1:
    }

  anon5:
    assume $full_stop_ext(#tok$1^9.2, $s);

  #break_1:
    // return; 
    assert $position_marker();
    goto #exit;

  #exit:
}



const unique #tok$1^13.3: $token;

const unique #tok$1^12.3: $token;

const unique #tok$1^9.2: $token;

const unique #loc.i: $token;

const unique #tok$1^8.2: $token;

const unique #loc.l: $token;

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^^i4);

const unique #loc.x: $token;

const unique #tok$1^3.1: $token;

axiom $type_code_is(1, ^^u4);

const unique #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Czero.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Czero.cpp);
