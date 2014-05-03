//#VccPrelude
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

procedure sort(P#x: int, P#l: int) returns ($result: int);
  requires P#l >= 1;
  requires $is_array($s, $ptr(^^i4, P#x), ^^i4, P#l);
  modifies $s, $cev_pc;
  free ensures $in_range_phys_ptr($ref($ptr(^^i4, $result)));
  ensures (forall Q#i$1^7.11#tc1: int, Q#j$1^7.11#tc1: int :: $in_range_u4(Q#i$1^7.11#tc1) && $in_range_u4(Q#j$1^7.11#tc1) ==> Q#i$1^7.11#tc1 < Q#j$1^7.11#tc1 && Q#j$1^7.11#tc1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#i$1^7.11#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), Q#j$1^7.11#tc1, ^^i4)));
  free ensures (forall #p: $ptr :: {:weight 0} { $mem($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $mem_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $st($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $st_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $ts($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $ts_eq(old($s), $s, #p)) && $timestamp_post(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation sort(P#x: int, P#l: int) returns ($result: int)
{
  var loopState#1: $state;
  var loopState#0: $state;
  var L#i: int where $in_range_u4(L#i);
  var L#j: int where $in_range_u4(L#j);
  var L#temp: int where $in_range_i4(L#temp);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon11:
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
    // int32_t temp; 
    assume $local_value_is($s, #tok$1^11.2, #loc.temp, L#temp, ^^i4);
    // uint32_t j; 
    assume $local_value_is($s, #tok$1^10.2, #loc.j, L#j, ^^u4);
    // uint32_t i; 
    assume $local_value_is($s, #tok$1^9.2, #loc.i, L#i, ^^u4);
    // assert @in_range_u4(-(l, 1)); 
    assert $in_range_u4(P#l - 1);
    // i := -(l, 1); 
    L#i := P#l - 1;
    assume $local_value_is($s, #tok$1^9.2, #loc.i, L#i, ^^u4);
    // var uint32_t j
    // var int32_t temp
    loopState#0 := $s;
    while (true)
      invariant L#i >= 0 && L#i < P#l;
      invariant (forall Q#m$1^16.15#tc1: int :: $in_range_u4(Q#m$1^16.15#tc1) ==> Q#m$1^16.15#tc1 <= L#i + 1 && L#i + 1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#m$1^16.15#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), L#i + 1, ^^i4)));
      invariant (forall Q#o$1^18.15#tc1: int :: $in_range_u4(Q#o$1^18.15#tc1) ==> L#i + 1 <= Q#o$1^18.15#tc1 && Q#o$1^18.15#tc1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), L#i + 1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), Q#o$1^18.15#tc1, ^^i4)));
      invariant (forall Q#n$1^20.15#tc1: int, Q#m$1^20.15#tc1: int :: $in_range_u4(Q#n$1^20.15#tc1) && $in_range_u4(Q#m$1^20.15#tc1) ==> Q#n$1^20.15#tc1 > L#i && Q#n$1^20.15#tc1 < Q#m$1^20.15#tc1 && Q#m$1^20.15#tc1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#n$1^20.15#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), Q#m$1^20.15#tc1, ^^i4)));
    {
      anon10:
        assume (forall #p: $ptr :: {:weight 0} { $mem($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $mem_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $st($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $st_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $ts($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $ts_eq(old($s), $s, #p)) && $timestamp_post(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume true;
        assume $full_stop_ext(#tok$1^12.2, $s);
        assume $local_value_is($s, #tok$1^12.2, #loc.i, L#i, ^^u4);
        assume $local_value_is($s, #tok$1^12.2, #loc.j, L#j, ^^u4);
        assume $local_value_is($s, #tok$1^12.2, #loc.temp, L#temp, ^^i4);
        assume $local_value_is($s, #tok$1^12.2, #loc.l, P#l, ^^u4);
        assume $local_value_is($s, #tok$1^12.2, #loc.x, $ptr_to_int($ptr(^^i4, P#x)), $ptr_to(^^i4)) && $local_value_is_ptr($s, #tok$1^12.2, #loc.x, $ptr(^^i4, P#x), $ptr_to(^^i4));
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (<(0, i)) ...
        if (0 < L#i)
        {
          anon7:
            // j := 0; 
            L#j := 0;
            assume $local_value_is($s, #tok$1^22.3, #loc.j, L#j, ^^u4);
            loopState#1 := $s;
            while (true)
              invariant L#j >= 0 && L#j <= L#i;
              invariant (forall Q#k$1^27.16#tc1: int :: $in_range_u4(Q#k$1^27.16#tc1) ==> Q#k$1^27.16#tc1 < L#j ==> $mem($s, $idx($ptr(^^i4, P#x), Q#k$1^27.16#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), L#j, ^^i4)));
              invariant (forall Q#n$1^29.16#tc1: int, Q#m$1^29.16#tc1: int :: $in_range_u4(Q#n$1^29.16#tc1) && $in_range_u4(Q#m$1^29.16#tc1) ==> Q#n$1^29.16#tc1 > L#i && Q#n$1^29.16#tc1 < Q#m$1^29.16#tc1 && Q#m$1^29.16#tc1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#n$1^29.16#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), Q#m$1^29.16#tc1, ^^i4)));
              invariant (forall Q#p$1^31.16#tc1: int :: $in_range_u4(Q#p$1^31.16#tc1) ==> Q#p$1^31.16#tc1 <= L#i && L#i + 1 < P#l ==> $mem($s, $idx($ptr(^^i4, P#x), Q#p$1^31.16#tc1, ^^i4)) <= $mem($s, $idx($ptr(^^i4, P#x), L#i + 1, ^^i4)));
            {
              anon6:
                assume (forall #p: $ptr :: {:weight 0} { $mem($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $mem_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $st($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $st_eq(old($s), $s, #p)) && (forall #p: $ptr :: {:weight 0} { $ts($s, #p) } $irrelevant(old($s), #p) || $set_in(#p, $array_range(old($s), $ptr(^^i4, P#x), ^^i4, P#l)) || $ts_eq(old($s), $s, #p)) && $timestamp_post(old($s), $s);
                assume $timestamp_post(loopState#1, $s);
                assume true;
                assume $full_stop_ext(#tok$1^23.3, $s);
                assume $local_value_is($s, #tok$1^23.3, #loc.i, L#i, ^^u4);
                assume $local_value_is($s, #tok$1^23.3, #loc.j, L#j, ^^u4);
                assume $local_value_is($s, #tok$1^23.3, #loc.temp, L#temp, ^^i4);
                assume $local_value_is($s, #tok$1^23.3, #loc.l, P#l, ^^u4);
                assume $local_value_is($s, #tok$1^23.3, #loc.x, $ptr_to_int($ptr(^^i4, P#x)), $ptr_to(^^i4)) && $local_value_is_ptr($s, #tok$1^23.3, #loc.x, $ptr(^^i4, P#x), $ptr_to(^^i4));
                // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
                assume $meta_eq(loopState#1, $s);
                // if (<(j, i)) ...
                if (L#j < L#i)
                {
                  anon3:
                    // assert @reads_check_normal(x[+(j, 1)]); 
                    assert $typed2($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4), ^^i4);
                    assert $thread_local2($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4), ^^i4);
                    // assert @in_range_u4(+(j, 1)); 
                    assert $in_range_u4(L#j + 1);
                    // assert @reads_check_normal(x[j]); 
                    assert $typed2($s, $idx($ptr(^^i4, P#x), L#j, ^^i4), ^^i4);
                    assert $thread_local2($s, $idx($ptr(^^i4, P#x), L#j, ^^i4), ^^i4);
                    // if (<(*(x[+(j, 1)]), *(x[j]))) ...
                    if ($mem($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4)) < $mem($s, $idx($ptr(^^i4, P#x), L#j, ^^i4)))
                    {
                      anon1:
                        // assert @reads_check_normal(x[j]); 
                        assert $typed2($s, $idx($ptr(^^i4, P#x), L#j, ^^i4), ^^i4);
                        assert $thread_local2($s, $idx($ptr(^^i4, P#x), L#j, ^^i4), ^^i4);
                        // temp := *(x[j]); 
                        L#temp := $mem($s, $idx($ptr(^^i4, P#x), L#j, ^^i4));
                        assume $local_value_is($s, #tok$1^35.5, #loc.temp, L#temp, ^^i4);
                        // assert @_vcc_typed2(@state, x[j]); 
                        assert $typed2($s, $idx($ptr(^^i4, P#x), L#j, ^^i4), ^^i4);
                        // assert @prim_writes_check(x[j]); 
                        assert $writable($s, #wrTime$1^3.1, $idx($ptr(^^i4, P#x), L#j, ^^i4));
                        // assert @reads_check_normal(x[+(j, 1)]); 
                        assert $typed2($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4), ^^i4);
                        assert $thread_local2($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4), ^^i4);
                        // assert @in_range_u4(+(j, 1)); 
                        assert $in_range_u4(L#j + 1);
                        // *x[j] := *(x[+(j, 1)]); 
                        call $write_int($idx($ptr(^^i4, P#x), L#j, ^^i4), $mem($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4)));
                        assume $full_stop_ext(#tok$1^36.5, $s);
                        // assert @_vcc_typed2(@state, x[+(j, 1)]); 
                        assert $typed2($s, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4), ^^i4);
                        // assert @prim_writes_check(x[+(j, 1)]); 
                        assert $writable($s, #wrTime$1^3.1, $idx($ptr(^^i4, P#x), L#j + 1, ^^i4));
                        // assert @in_range_u4(+(j, 1)); 
                        assert $in_range_u4(L#j + 1);
                        // *x[+(j, 1)] := temp; 
                        call $write_int($idx($ptr(^^i4, P#x), L#j + 1, ^^i4), L#temp);
                        assume $full_stop_ext(#tok$1^37.5, $s);
                    }
                    else
                    {
                      anon2:
                        // empty
                    }

                  anon4:
                    // assert @in_range_u4(+(j, 1)); 
                    assert $in_range_u4(L#j + 1);
                    // j := +(j, 1); 
                    L#j := L#j + 1;
                    assume $local_value_is($s, #tok$1^39.4, #loc.j, L#j, ^^u4);
                }
                else
                {
                  anon5:
                    // goto #break_2; 
                    goto #break_2;
                }

              #continue_2:
            }

          anon8:
            assume $full_stop_ext(#tok$1^23.3, $s);

          #break_2:
            // assert @in_range_u4(-(i, 1)); 
            assert $in_range_u4(L#i - 1);
            // i := -(i, 1); 
            L#i := L#i - 1;
            assume $local_value_is($s, #tok$1^44.3, #loc.i, L#i, ^^u4);
        }
        else
        {
          anon9:
            // goto #break_1; 
            goto #break_1;
        }

      #continue_1:
    }

  anon12:
    assume $full_stop_ext(#tok$1^12.2, $s);

  #break_1:
    // return x; 
    $result := $ref($ptr(^^i4, P#x));
    assert $position_marker();
    goto #exit;

  anon13:
    // empty

  #exit:
}



const unique #tok$1^44.3: $token;

const unique #tok$1^39.4: $token;

const unique #tok$1^37.5: $token;

const unique #tok$1^36.5: $token;

const unique #tok$1^35.5: $token;

const unique #tok$1^23.3: $token;

const unique #tok$1^22.3: $token;

const unique #tok$1^12.2: $token;

const unique #loc.i: $token;

const unique #tok$1^9.2: $token;

const unique #loc.j: $token;

const unique #tok$1^10.2: $token;

const unique #loc.temp: $token;

const unique #tok$1^11.2: $token;

const unique #loc.l: $token;

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^^i4);

const unique #loc.x: $token;

const unique #tok$1^3.1: $token;

axiom $type_code_is(1, ^^u4);

const unique #file^C?3A?5CUsers?5Cchristj?5Cexamples?5CVCC?5Csort.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cchristj?5Cexamples?5CVCC?5Csort.cpp);
