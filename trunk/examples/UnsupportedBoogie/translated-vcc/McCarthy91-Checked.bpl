//#VccPrelude #Safe
axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$#club_t: $ctype;

axiom $is_math_type(^$#club_t);

type $#club_t;

procedure mcCarthy(P#x: int) returns ($result: int);
  modifies $s, $cev_pc;
  free ensures $in_range_i4($result);
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation mcCarthy(P#x: int) returns ($result: int)
{
  var L#res: int where $in_range_i4(L#res);
  var #wrTime$1^11.1: int;
  var #stackframe: int;

  anon3:
    assume $function_entry($s);
    assume $full_stop_ext(#tok$1^11.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume $local_value_is($s, #tok$1^11.1, #loc.x, P#x, ^^i4);
    assume #wrTime$1^11.1 == $current_timestamp($s);
    assume (forall #p: $ptr :: { $in_writes_at(#wrTime$1^11.1, #p) } $in_writes_at(#wrTime$1^11.1, #p) == false);
    // assume @in_range_i4(x);
 
    assume $in_range_i4(P#x);
    // int32_t res;
 
    assume $local_value_is($s, #tok$1^13.3, #loc.res, L#res, ^^i4);
    // var int32_t res
    // if (>(x, 100)) ...
    if (P#x > 100)
    {
      anon1:
        // assert @in_range_i4(-(x, 10));
 
        assert $in_range_i4(P#x - 10);
        // res := -(x, 10);
 
        L#res := P#x - 10;
        assume $local_value_is($s, #tok$1^15.5, #loc.res, L#res, ^^i4);
    }
    else
    {
      anon2:
        // non-pure function
        // assert @in_range_i4(+(x, 11));
 
        assert $in_range_i4(P#x + 11);
        // res := mcCarthy(+(x, 11));
 
        call L#res := mcCarthy(P#x + 11);
        assume $full_stop_ext(#tok$1^18.11, $s);
        assume $local_value_is($s, #tok$1^18.11, #loc.res, L#res, ^^i4);
        // non-pure function
        // res := mcCarthy(res);
 
        call L#res := mcCarthy(L#res);
        assume $full_stop_ext(#tok$1^19.11, $s);
        assume $local_value_is($s, #tok$1^19.11, #loc.res, L#res, ^^i4);
    }

  anon4:
    // assert ||(==(res, 91), >(x, 101));
 
    assert L#res == 91 || P#x > 101;
    // assume ||(==(res, 91), >(x, 101));
 
    assume L#res == 91 || P#x > 101;
    // empty

  #exit:
}



const unique #tok$1^19.11: $token;

const unique #tok$1^18.11: $token;

const unique #tok$1^15.5: $token;

const unique #loc.res: $token;

const unique #tok$1^13.3: $token;

const unique #loc.x: $token;

const unique #tok$1^11.1: $token;

const unique #file^C?3A?5CUsers?5CEvren?5CDesktop?5CMcCarthy91.c: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5CEvren?5CDesktop?5CMcCarthy91.c);
