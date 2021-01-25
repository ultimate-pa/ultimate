-- This file was generated automatically: DO NOT MODIFY IT !

with System.IO;
use System.IO;

with Ada.Unchecked_Conversion;
with Ada.Numerics.Generic_Elementary_Functions;

with TASTE_Dataview;
use TASTE_Dataview;
with TASTE_BasicTypes;
use TASTE_BasicTypes;
with adaasn1rtl;
use adaasn1rtl;

with Interfaces;
use Interfaces;

package body strblindingprotect is
   type States is (notblinded, potentiallyblind, blinded, inapogee);
   type ctxt_Ty is
      record
      state : States;
      initDone : Boolean := False;
      num_of_str_pred_blinded : aliased asn1SccT_Int8 := 0;
      activation : aliased asn1SccMyBool := false;
      num_of_str_blinded : aliased asn1SccT_Int8 := 0;
      ta : aliased asn1SccT_Int32 := 0;
   end record;
   ctxt: aliased ctxt_Ty;
   CS_Only  : constant Integer := 7;
   procedure runTransition(Id: Integer);
   procedure get_true_anomaly(TA: access asn1SccT_Int32) is
      begin
         case ctxt.state is
            when notblinded =>
               ctxt.ta := TA.all;
               runTransition(1);
            when potentiallyblind =>
               ctxt.ta := TA.all;
               runTransition(4);
            when blinded =>
               runTransition(CS_Only);
            when inapogee =>
               ctxt.ta := TA.all;
               runTransition(6);
            when others =>
               runTransition(CS_Only);
         end case;
      end get_true_anomaly;
      

   procedure STR_blinded(num_STR_blind: access asn1SccT_Int8) is
      begin
         case ctxt.state is
            when notblinded =>
               runTransition(CS_Only);
            when potentiallyblind =>
               ctxt.num_of_str_blinded := num_STR_blind.all;
               runTransition(3);
            when blinded =>
               runTransition(CS_Only);
            when inapogee =>
               ctxt.num_of_str_blinded := num_STR_blind.all;
               runTransition(5);
            when others =>
               runTransition(CS_Only);
         end case;
      end STR_blinded;
      

   procedure pred_blinded(num_pred_blind: access asn1SccT_Int8) is
      begin
         case ctxt.state is
            when notblinded =>
               runTransition(CS_Only);
            when potentiallyblind =>
               ctxt.num_of_str_pred_blinded := num_pred_blind.all;
               runTransition(2);
            when blinded =>
               runTransition(CS_Only);
            when inapogee =>
               runTransition(CS_Only);
            when others =>
               runTransition(CS_Only);
         end case;
      end pred_blinded;
      

   procedure runTransition(Id: Integer) is
      trId : Integer := Id;
      tmp5 : aliased asn1SccMyString;
      tmp41 : aliased asn1SccMyString;
      --  !! stack: _call_external_function line 1271
      tmp55 : aliased asn1SccMyString;
      tmp34 : aliased asn1SccMyString;
      tmp48 : aliased asn1SccMyString;
      tmp23 : aliased asn1SccMyString;
      tmp16 : aliased asn1SccMyString;
      begin
         while (trId /= -1) loop
            case trId is
               when 0 =>
                  --  out_msg('Not_blinded') (17,15)
                  tmp5 := (Data => (78, 111, 116, 95, 98, 108, 105, 110, 100, 101, 100, others => 0), Length => 11);
                  RIÜout_msg(tmp5'Access);
                  --  activation :=FALSE (19,13)
                  ctxt.activation := false;
                  --  function_active(activation) (21,15)
                  RIÜfunction_active(ctxt.activation'Access);
                  --  NEXT_STATE Notblinded (23,18) at 466, 230
                  trId := -1;
                  ctxt.state := Notblinded;
                  goto next_transition;
               when 1 =>
                  --  DECISION TA>100 (29,23)
                  --  ANSWER TRUE (31,17)
                  if ((ctxt.TA > 100)) = true then
                     --  out_msg('Inside apogee') (33,27)
                     tmp16 := (Data => (73, 110, 115, 105, 100, 101, 32, 97, 112, 111, 103, 101, 101, others => 0), Length => 13);
                     RIÜout_msg(tmp16'Access);
                     --  NEXT_STATE Inapogee (35,30) at 1021, 285
                     trId := -1;
                     ctxt.state := Inapogee;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  NEXT_STATE Notblinded (39,30) at 1148, 230
                     trId := -1;
                     ctxt.state := Notblinded;
                     goto next_transition;
                  end if;
               when 2 =>
                  --  DECISION num_of_str_pred_blinded = 3 (59,45)
                  --  ANSWER TRUE (61,17)
                  if ((ctxt.num_of_str_pred_blinded = 3)) = true then
                     --  out_msg('Blinded') (63,27)
                     tmp23 := (Data => (66, 108, 105, 110, 100, 101, 100, others => 0), Length => 7);
                     RIÜout_msg(tmp23'Access);
                     --  activation :=TRUE (65,25)
                     ctxt.activation := true;
                     --  function_active(activation) (67,27)
                     RIÜfunction_active(ctxt.activation'Access);
                     --  NEXT_STATE Blinded (69,30) at 661, 739
                     trId := -1;
                     ctxt.state := Blinded;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  NEXT_STATE Potentiallyblind (73,30) at 791, 579
                     trId := -1;
                     ctxt.state := Potentiallyblind;
                     goto next_transition;
                  end if;
               when 3 =>
                  --  DECISION num_of_str_blinded = 3 (78,40)
                  --  ANSWER TRUE (80,17)
                  if ((ctxt.num_of_str_blinded = 3)) = true then
                     --  NEXT_STATE potentiallyblind (82,30) at 922, 579
                     trId := -1;
                     ctxt.state := potentiallyblind;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  out_msg('Not blinded') (86,27)
                     tmp34 := (Data => (78, 111, 116, 32, 98, 108, 105, 110, 100, 101, 100, others => 0), Length => 11);
                     RIÜout_msg(tmp34'Access);
                     --  NEXT_STATE inapogee (88,30) at 1130, 629
                     trId := -1;
                     ctxt.state := inapogee;
                     goto next_transition;
                  end if;
               when 4 =>
                  --  DECISION TA>260 (93,23)
                  --  ANSWER TRUE (95,17)
                  if ((ctxt.TA > 260)) = true then
                     --  out_msg('Outside apogee') (97,27)
                     tmp41 := (Data => (79, 117, 116, 115, 105, 100, 101, 32, 97, 112, 111, 103, 101, 101, others => 0), Length => 14);
                     RIÜout_msg(tmp41'Access);
                     --  NEXT_STATE Notblinded (99,30) at 1314, 634
                     trId := -1;
                     ctxt.state := Notblinded;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  NEXT_STATE potentiallyblind (103,30) at 1464, 579
                     trId := -1;
                     ctxt.state := potentiallyblind;
                     goto next_transition;
                  end if;
               when 5 =>
                  --  DECISION num_of_str_blinded = 3 (111,40)
                  --  ANSWER TRUE (113,17)
                  if ((ctxt.num_of_str_blinded = 3)) = true then
                     --  out_msg('Potentially blinded') (115,27)
                     tmp48 := (Data => (80, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 32, 98, 108, 105, 110, 100, 101, 100, others => 0), Length => 19);
                     RIÜout_msg(tmp48'Access);
                     --  NEXT_STATE potentiallyblind (117,30) at 42, 641
                     trId := -1;
                     ctxt.state := potentiallyblind;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  NEXT_STATE Inapogee (121,30) at 256, 586
                     trId := -1;
                     ctxt.state := Inapogee;
                     goto next_transition;
                  end if;
               when 6 =>
                  --  DECISION TA>260 (126,23)
                  --  ANSWER TRUE (128,17)
                  if ((ctxt.TA > 260)) = true then
                     --  out_msg('Outside apogee') (130,27)
                     tmp55 := (Data => (79, 117, 116, 115, 105, 100, 101, 32, 97, 112, 111, 103, 101, 101, others => 0), Length => 14);
                     RIÜout_msg(tmp55'Access);
                     --  NEXT_STATE Notblinded (132,30) at 393, 626
                     trId := -1;
                     ctxt.state := Notblinded;
                     goto next_transition;
                     --  ANSWER else (None,None)
                  else
                     --  NEXT_STATE Inapogee (136,30) at 538, 571
                     trId := -1;
                     ctxt.state := Inapogee;
                     goto next_transition;
                  end if;
               when CS_Only =>
                  trId := -1;
                  goto next_transition;
               when others =>
                  null;
            end case;
            <<next_transition>>
            null;
         end loop;
      end runTransition;
      

   begin
      runTransition(0);
      ctxt.initDone := True;
end strblindingprotect;