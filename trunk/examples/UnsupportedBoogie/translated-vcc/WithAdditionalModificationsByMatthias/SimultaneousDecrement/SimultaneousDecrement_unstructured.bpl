/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 9.8.2010
 *
 * Unstructured Version of the VCC generated simultaneousDecrement example.
 * (Output of BoogiePreprocessor and BoogiePrinter, afterwards Prelude removed)
 */




axiom $arch_ptr_size == 8;
axiom $arch_spec_ptr_start == $max.u8;
procedure simultaneousDecrement(P#i:int, P#j:int) returns ($result:int);
    requires P#i >= 0;
    requires P#j >= 0;
    modifies $s, $cev_pc;
    free ensures $min.i4 <= $result && $result <= $max.i4;
    free ensures (forall p : $ptr :: { $select.sm($statusmap($s), p) } $kind_of($typ($owner($s, p))) != $kind_thread ==> $kind_of($typ($owner(old($s), p))) != $kind_thread) && (forall p : $ptr :: { $select.mem($memory($s), p) } $thread_local(old($s), p) ==> $select.mem($memory(old($s)), p) == $select.mem($memory($s), p) && $thread_local($s, p)) && (forall p : $ptr :: { $select.sm($statusmap($s), p) } $thread_local(old($s), p) ==> $select.sm($statusmap(old($s)), p) == $select.sm($statusmap($s), p) && $thread_local($s, p)) && (forall p : $ptr :: { $select.tm($typemap($s), p) } $thread_local(old($s), p) ==> $select.tm($typemap(old($s)), p) == $select.tm($typemap($s), p) && $thread_local($s, p)) && $current_timestamp(old($s)) <= $current_timestamp($s) && (forall p : $ptr :: { :weight 0 } { $timestamp($s, p) } $timestamp(old($s), p) <= $timestamp($s, p)) && $call_transition(old($s), $s);
    free ensures $call_transition(old($s), $s);

implementation simultaneousDecrement(P#i:int, P#j:int) returns ($result:int)
{
    var loopState#0 : $state;
    var L#x : int where $min.i4 <= L#x && L#x <= $max.i4;
    var L#y : int where $min.i4 <= L#y && L#y <= $max.i4;
    var #wrTime$1^3.1 : int;
    var #stackframe : int;

  $Ultimate##0:
  anon6:
    assume $function_entry($s);
    assume $good_state_ext(#tok$1^3.1, $s) && $full_stop($s);
    assume (forall f : $pure_function :: { $frame_level(f) } $frame_level(f) < $current_frame_level);
    assume $local_value_is($s, #tok$1^3.1, #loc.i, P#i, ^^i4);
    assume $local_value_is($s, #tok$1^3.1, #loc.j, P#j, ^^i4);
    assume #wrTime$1^3.1 == $current_timestamp($s);
    assume (forall #p : $ptr :: { $in_writes_at(#wrTime$1^3.1, #p) } $in_writes_at(#wrTime$1^3.1, #p) == false);
    assume $min.i4 <= P#i && P#i <= $max.i4;
    assume $min.i4 <= P#j && P#j <= $max.i4;
    assume $local_value_is($s, #tok$1^8.2, #loc.y, L#y, ^^i4);
    assume $local_value_is($s, #tok$1^7.2, #loc.x, L#x, ^^i4);
    L#x := P#i;
    assume $local_value_is($s, #tok$1^7.2, #loc.x, L#x, ^^i4);
    L#y := P#j;
    assume $local_value_is($s, #tok$1^8.2, #loc.y, L#y, ^^i4);
    loopState#0 := $s;
    goto $Ultimate##1;
  $Ultimate##1:
    goto $Ultimate##2, $Ultimate##3;
  $Ultimate##2:
    assume true;
    goto anon3;
  anon3:
    assume (forall p : $ptr :: { $select.sm($statusmap($s), p) } $kind_of($typ($owner($s, p))) != $kind_thread ==> $kind_of($typ($owner(old($s), p))) != $kind_thread) && (forall p : $ptr :: { $select.mem($memory($s), p) } $thread_local(old($s), p) ==> $select.mem($memory(old($s)), p) == $select.mem($memory($s), p) && $thread_local($s, p)) && (forall p : $ptr :: { $select.sm($statusmap($s), p) } $thread_local(old($s), p) ==> $select.sm($statusmap(old($s)), p) == $select.sm($statusmap($s), p) && $thread_local($s, p)) && (forall p : $ptr :: { $select.tm($typemap($s), p) } $thread_local(old($s), p) ==> $select.tm($typemap(old($s)), p) == $select.tm($typemap($s), p) && $thread_local($s, p)) && $current_timestamp(old($s)) <= $current_timestamp($s) && (forall p : $ptr :: { :weight 0 } { $timestamp($s, p) } $timestamp(old($s), p) <= $timestamp($s, p)) && $call_transition(old($s), $s);
    assume $current_timestamp(loopState#0) <= $current_timestamp($s) && (forall p : $ptr :: { :weight 0 } { $timestamp($s, p) } $timestamp(loopState#0, p) <= $timestamp($s, p)) && $call_transition(loopState#0, $s);
    assume true;
    assume $good_state_ext(#tok$1^10.2, $s) && $full_stop($s);
    assume $local_value_is($s, #tok$1^10.2, #loc.x, L#x, ^^i4);
    assume $local_value_is($s, #tok$1^10.2, #loc.y, L#y, ^^i4);
    assume $local_value_is($s, #tok$1^10.2, #loc.j, P#j, ^^i4);
    assume $local_value_is($s, #tok$1^10.2, #loc.i, P#i, ^^i4);
    assume $typemap(loopState#0) == $typemap($s) && $statusmap(loopState#0) == $statusmap($s);
    goto $Ultimate##4, $Ultimate##5;
  $Ultimate##4:
    assume L#x > 0;
    goto anon1;
  anon1:
    assert $min.i4 <= L#x - 1 && L#x - 1 <= $max.i4;
    L#x := L#x - 1;
    assume $local_value_is($s, #tok$1^12.3, #loc.x, L#x, ^^i4);
    assert $min.i4 <= L#y - 1 && L#y - 1 <= $max.i4;
    L#y := L#y - 1;
    assume $local_value_is($s, #tok$1^13.3, #loc.y, L#y, ^^i4);
    goto #continue_1;
  $Ultimate##5:
    assume !(L#x > 0);
    goto anon2;
  anon2:
    goto #break_1;
  #continue_1:
    goto $Ultimate##1;
  $Ultimate##3:
    assume !true;
    goto anon7;
  anon7:
    assume $good_state_ext(#tok$1^10.2, $s) && $full_stop($s);
    goto #break_1;
  #break_1:
    goto $Ultimate##6, $Ultimate##7;
  $Ultimate##6:
    assume P#i == P#j;
    goto anon4;
  anon4:
    assert L#y == 0;
    assume L#y == 0;
    goto anon8;
  $Ultimate##7:
    assume !(P#i == P#j);
    goto anon5;
  anon5:
  anon8:
  #exit:
    return;
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
