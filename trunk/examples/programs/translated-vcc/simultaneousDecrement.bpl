//#VccPrelude
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure simultaneousDecrement(P#i: int, P#j: int) returns ($result: int);
  requires P#i >= 0;
  requires P#j >= 0;
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation simultaneousDecrement(P#i: int, P#j: int) returns ($result: int)
{
  var loopState#0: $state;
  var L#x: int where $in_range_i4(L#x);
  var L#y: int where $in_range_i4(L#y);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon6:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^3.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^3.1, #loc.i, P#i, ^^i4);
    assume $local_value_is($s, #tok$1^3.1, #loc.j, P#j, ^^i4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == false);
    // assume @in_range_i4(i); 
    assume $in_range_i4(P#i);
    // assume @in_range_i4(j); 
    assume $in_range_i4(P#j);
    // int32_t y; 
    assume $local_value_is($s, #tok$1^8.2, #loc.y, L#y, ^^i4);
    // int32_t x; 
    assume $local_value_is($s, #tok$1^7.2, #loc.x, L#x, ^^i4);
    // x := i; 
    L#x := P#i;
    assume $local_value_is($s, #tok$1^7.2, #loc.x, L#x, ^^i4);
    // y := j; 
    L#y := P#j;
    assume $local_value_is($s, #tok$1^8.2, #loc.y, L#y, ^^i4);
    loopState#0 := $s;
    while (true)
    {
      anon3:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume true;
        assume $full_stop_ext(#tok$1^10.2, $s);
        assume $local_value_is($s, #tok$1^10.2, #loc.x, L#x, ^^i4);
        assume $local_value_is($s, #tok$1^10.2, #loc.y, L#y, ^^i4);
        assume $local_value_is($s, #tok$1^10.2, #loc.j, P#j, ^^i4);
        assume $local_value_is($s, #tok$1^10.2, #loc.i, P#i, ^^i4);
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (>(x, 0)) ...
        if (L#x > 0)
        {
          anon1:
            // assert @in_range_i4(-(x, 1)); 
            assert $in_range_i4(L#x - 1);
            // x := -(x, 1); 
            L#x := L#x - 1;
            assume $local_value_is($s, #tok$1^12.3, #loc.x, L#x, ^^i4);
            // assert @in_range_i4(-(y, 1)); 
            assert $in_range_i4(L#y - 1);
            // y := -(y, 1); 
            L#y := L#y - 1;
            assume $local_value_is($s, #tok$1^13.3, #loc.y, L#y, ^^i4);
        }
        else
        {
          anon2:
            // goto #break_1; 
            goto #break_1;
        }

      #continue_1:
    }

  anon7:
    assume $full_stop_ext(#tok$1^10.2, $s);

  #break_1:
    // if (==(i, j)) ...
    if (P#i == P#j)
    {
      anon4:
        // assert ==(y, 0); 
        assert L#y == 0;
        // assume ==(y, 0); 
        assume L#y == 0;
    }
    else
    {
      anon5:
        // empty
    }

  anon8:
    // empty

  #exit:
}



const unique #tok$1^13.3: $token;

const unique #tok$1^12.3: $token;

const unique #tok$1^10.2: $token;

const unique #loc.x: $token;

const unique #tok$1^7.2: $token;

const unique #loc.y: $token;

const unique #tok$1^8.2: $token;

const unique #loc.j: $token;

const unique #loc.i: $token;

const unique #tok$1^3.1: $token;

const unique #file^C?3A?5CUsers?5Cheizmann?5Cultimate?5Cexamples?5CVCC?5CsimultaneousDecrement.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cheizmann?5Cultimate?5Cexamples?5CVCC?5CsimultaneousDecrement.cpp);
