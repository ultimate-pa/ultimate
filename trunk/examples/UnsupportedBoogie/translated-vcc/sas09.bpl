//#VccPrelude #Safe
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure sas09(P#n: int) returns ($result: int);
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation sas09(P#n: int) returns ($result: int)
{
  var loopState#0: $state;
  var L#x: int where $in_range_i4(L#x);
  var L#y: int where $in_range_i4(L#y);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon4:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^3.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^3.1, #loc.n, P#n, ^^i4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == false);
    // assume @in_range_i4(n); 
    assume $in_range_i4(P#n);
    // int32_t y; 
    assume $local_value_is($s, #tok$1^6.2, #loc.y, L#y, ^^i4);
    // int32_t x; 
    assume $local_value_is($s, #tok$1^5.2, #loc.x, L#x, ^^i4);
    // x := 0; 
    L#x := 0;
    assume $local_value_is($s, #tok$1^5.2, #loc.x, L#x, ^^i4);
    // y := 0; 
    L#y := 0;
    assume $local_value_is($s, #tok$1^6.2, #loc.y, L#y, ^^i4);
    loopState#0 := $s;
    while (true)
    {
      anon3:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume true;
        assume $full_stop_ext(#tok$1^8.2, $s);
        assume $local_value_is($s, #tok$1^8.2, #loc.x, L#x, ^^i4);
        assume $local_value_is($s, #tok$1^8.2, #loc.y, L#y, ^^i4);
        assume $local_value_is($s, #tok$1^8.2, #loc.n, P#n, ^^i4);
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (<(x, n)) ...
        if (L#x < P#n)
        {
          anon1:
            // assert @in_range_i4(+(x, 1)); 
            assert $in_range_i4(L#x + 1);
            // x := +(x, 1); 
            L#x := L#x + 1;
            assume $local_value_is($s, #tok$1^10.3, #loc.x, L#x, ^^i4);
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
    assume $full_stop_ext(#tok$1^8.2, $s);

  #break_1:
    // assert !=(x, -1); 
    assert L#x != -1;
    // assume !=(x, -1); 
    assume L#x != -1;
    // assert !=(y, -1); 
    assert L#y != -1;
    // assume !=(y, -1); 
    assume L#y != -1;
    // empty

  #exit:
}



const unique #tok$1^10.3: $token;

const unique #tok$1^8.2: $token;

const unique #loc.x: $token;

const unique #tok$1^5.2: $token;

const unique #loc.y: $token;

const unique #tok$1^6.2: $token;

const unique #loc.n: $token;

const unique #tok$1^3.1: $token;

const unique #file^C?3A?5CUsers?5Cheizmann?5Cultimate?5Cexamples?5Csas09.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cheizmann?5Cultimate?5Cexamples?5Csas09.cpp);
