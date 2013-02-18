//#VccPrelude
procedure ggT(P#x: int, P#y: int) returns ($result: int);
  modifies $s;
  ensures $unchecked(^^u4, P#x % $result) == 0;
  free ensures $in_range_u4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation ggT(P#x: int, P#y: int) returns ($result: int)
{
  var loopState#0: $state;
  var L#a: int where $in_range_u4(L#a);
  var L#b: int where $in_range_u4(L#b);
  var #wrTime$1^3.1: int;
  var #stackframe: int;

  anon6:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^3.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^3.1, #loc.x, P#x, ^^u4);
    assume $local_value_is($s, #tok$1^3.1, #loc.y, P#y, ^^u4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == false);
    // assume @in_range_u4(x); 
    assume $in_range_u4(P#x);
    // assume @in_range_u4(y); 
    assume $in_range_u4(P#y);
    // uint32_t b; 
    // uint32_t a; 
    // var uint32_t a
    // var uint32_t b
    // a := x; 
    L#a := P#x;
    assume $local_value_is($s, #tok$1^7.2, #loc.a, L#a, ^^u4);
    // b := y; 
    L#b := P#y;
    assume $local_value_is($s, #tok$1^8.2, #loc.b, L#b, ^^u4);
    loopState#0 := $s;
    while (true)
    {
      anon5:
        assume $writes_nothing(old($s), $s);
        assume $timestamp_post(loopState#0, $s);
        assume $full_stop_ext(#tok$1^9.2, $s);
        assume $local_value_is($s, #tok$1^9.2, #loc.b, L#b, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.a, L#a, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.y, P#y, ^^u4);
        assume $local_value_is($s, #tok$1^9.2, #loc.x, P#x, ^^u4);
        // assume @_vcc_meta_eq(old(@prestate, @state), @state); 
        assume $meta_eq(loopState#0, $s);
        // if (!=(a, b)) ...
        if (L#a != L#b)
        {
          anon3:
            // if (>(a, b)) ...
            if (L#a > L#b)
            {
              anon1:
                // assert @in_range_u4(-(a, b)); 
                assert $in_range_u4(L#a - L#b);
                // a := -(a, b); 
                L#a := L#a - L#b;
                assume $local_value_is($s, #tok$1^11.14, #loc.a, L#a, ^^u4);
            }
            else
            {
              anon2:
                // assert @in_range_u4(-(b, a)); 
                assert $in_range_u4(L#b - L#a);
                // b := -(b, a); 
                L#b := L#b - L#a;
                assume $local_value_is($s, #tok$1^12.8, #loc.b, L#b, ^^u4);
            }
        }
        else
        {
          anon4:
            // goto #break_1; 
            goto #break_1;
        }

      #continue_1:
    }

  anon7:
    assume $full_stop_ext(#tok$1^9.2, $s);

  #break_1:
    // return a; 
    $result := L#a;
    assert $position_marker();
    goto #exit;

  anon8:
    // empty

  #exit:
}



procedure main();
  modifies $s;
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation main()
{
  var L#x: int where $in_range_u4(L#x);
  var L#y: int where $in_range_u4(L#y);
  var L#result: int where $in_range_u4(L#result);
  var #wrTime$1^17.1: int;
  var #stackframe: int;

  anon9:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^17.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$1^17.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^17.1, #p) } $in_writes_at(#wrTime$1^17.1, #p) == false);
    // uint32_t result; 
    // uint32_t y; 
    // uint32_t x; 
    // var uint32_t x
    // var uint32_t y
    // var uint32_t result
    // non-pure function
    // result := ggT(x, y); 
    call L#result := ggT(L#x, L#y);
    assume $full_stop_ext(#tok$1^20.11, $s);
    assume $local_value_is($s, #tok$1^20.11, #loc.result, L#result, ^^u4);
    // return; 
    assert $position_marker();
    goto #exit;

  #exit:
}



const unique #loc.result: $token;

const unique #tok$1^20.11: $token;

const unique #tok$1^17.1: $token;

const unique #tok$1^12.8: $token;

const unique #tok$1^11.14: $token;

const unique #tok$1^9.2: $token;

const unique #loc.b: $token;

const unique #tok$1^8.2: $token;

const unique #loc.a: $token;

const unique #tok$1^7.2: $token;

const unique #loc.y: $token;

const unique #loc.x: $token;

const unique #tok$1^3.1: $token;

const unique #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate?5Ctrunk?5Cexamples?5CVCC?5CggT.cpp: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5Cmaus?5CDocuments?5CUltimate?5Ctrunk?5Cexamples?5CVCC?5CggT.cpp);
