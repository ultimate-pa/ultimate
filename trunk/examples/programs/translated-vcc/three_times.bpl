//#VccPrelude #Safe
procedure three_times(P#n: int) returns ($result: int);
  requires P#n >= 0;
  requires $_mul(3, P#n) < 2147483647;
  modifies $s;
  ensures $result == $_mul(3, P#n);
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation three_times(P#n: int) returns ($result: int)
{
  var loopState#0: $state;
  var L#s: int where $in_range_i4(L#s);
  var L#i: int where $in_range_i4(L#i);
  var #wrTime$1^4.1: int;
  var #stackframe: int;

  anon4:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^4.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^4.1, #loc.n, P#n, ^^i4);
    assume #wrTime$1^4.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^4.1, #p) } $in_writes_at(#wrTime$1^4.1, #p) == false);
    // assume @in_range_i4(n); 
    assume $in_range_i4(P#n);
    // int32_t i; 
    // int32_t s; 
    // var int32_t s
    // s := 0; 
    L#s := 0;
    assume $local_value_is($s, #tok$1^9.2, #loc.s, L#s, ^^i4);
    // var int32_t i
    // i := 0; 
    L#i := 0;
    assume $local_value_is($s, #tok$1^10.2, #loc.i, L#i, ^^i4);
    loopState#0 := $s;
    while (true)
      invariant L#s == $_mul(L#i, 3);
      invariant L#i <= P#n;
    {
      anon3:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume $full_stop_ext(#tok$1^12.2, $s);
        assume $local_value_is($s, #tok$1^12.2, #loc.i, L#i, ^^i4);
        assume $local_value_is($s, #tok$1^12.2, #loc.s, L#s, ^^i4);
        assume $local_value_is($s, #tok$1^12.2, #loc.n, P#n, ^^i4);
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (<(i, n)) ...
        if (L#i < P#n)
        {
          anon1:
            // assert @in_range_i4(+(s, 3)); 
            assert $in_range_i4(L#s + 3);
            // s := +(s, 3); 
            L#s := L#s + 3;
            assume $local_value_is($s, #tok$1^16.3, #loc.s, L#s, ^^i4);
            // assert @in_range_i4(+(i, 1)); 
            assert $in_range_i4(L#i + 1);
            // i := +(i, 1); 
            L#i := L#i + 1;
            assume $local_value_is($s, #tok$1^17.3, #loc.i, L#i, ^^i4);
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
    assume $full_stop_ext(#tok$1^12.2, $s);

  #break_1:
    // assert ==(i, n); 
    assert L#i == P#n;
    // assume ==(i, n); 
    assume L#i == P#n;
    // return s; 
    $result := L#s;
    assert $position_marker();
    goto #exit;

  anon6:
    // empty

  #exit:
}



const unique #tok$1^17.3: $token;

const unique #tok$1^16.3: $token;

const unique #tok$1^12.2: $token;

const unique #loc.i: $token;

const unique #tok$1^10.2: $token;

const unique #loc.s: $token;

const unique #tok$1^9.2: $token;

const unique #loc.n: $token;

const unique #tok$1^4.1: $token;

const unique #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate?5Ctrunk?5Cexamples?5CVCC?5Cthree_times.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate?5Ctrunk?5Cexamples?5CVCC?5Cthree_times.cpp);
