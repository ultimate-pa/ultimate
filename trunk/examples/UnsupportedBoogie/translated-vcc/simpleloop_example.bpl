//#VccPrelude

axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure simpleLoop(P#l: int);
  modifies $s, $cev_pc;
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation simpleLoop(P#l: int)
{
  var loopState#0: $state;
  var L#i: int where $in_range_u4(L#i);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon4:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^3.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^3.1, #loc.l, P#l, ^^u4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == false);
    // assume @in_range_u4(l); 
    assume $in_range_u4(P#l);
    // uint32_t i; 
    assume $local_value_is($s, #tok$1^8.2, #loc.i, L#i, ^^u4);
    // i := 0; 
    L#i := 0;
    assume $local_value_is($s, #tok$1^8.2, #loc.i, L#i, ^^u4);
    loopState#0 := $s;
    while (true)
      invariant L#i >= 0 && L#i <= P#l;
    {
      anon3:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume true;
        assume $full_stop_ext(#tok$1^9.2, $s);
        assume $local_value_is($s, #tok$1^9.2, #loc.i, L#i, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.l, P#l, ^^u4);
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (<(i, l)) ...
        if (L#i < P#l)
        {
          anon1:
            // assert @in_range_u4(+(i, 1)); 
            assert $in_range_u4(L#i + 1);
            // i := +(i, 1); 
            L#i := L#i + 1;
            assume $local_value_is($s, #tok$1^14.3, #loc.i, L#i, ^^u4);
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
    // assert ==(i, l); 
    assert L#i == P#l;
    // assume ==(i, l); 
    assume L#i == P#l;
    // return; 
    assert $position_marker();
    goto #exit;

  #exit:
}



const unique #tok$1^14.3: $token;

const unique #tok$1^9.2: $token;

const unique #loc.i: $token;

const unique #tok$1^8.2: $token;

const unique #loc.l: $token;

const unique #tok$1^3.1: $token;

const unique #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Czero.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate2?5Cexamples?5CVCC?5Czero.cpp);
