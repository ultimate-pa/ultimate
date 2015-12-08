//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-11-05
 */

procedure main() returns (){
    var divRes : int;
    var modRes : int;

   divRes := 32 / 13;
   modRes := 32 % 13;
   assert divRes == 2;
   assert modRes == 6;
   
   divRes := 32 / -13;
   modRes := 32 % -13;
   assert divRes == -2;
   assert modRes == 6;
   
   divRes := -32 / 13;
   modRes := -32 % 13;
   assert divRes == -3;
   assert modRes == 7;
   
   divRes := -32 / -13;
   modRes := -32 % -13;
   assert divRes == 3;
   assert modRes == 7;

   
   divRes := 32 / 16;
   modRes := 32 % 16;
   assert divRes == 2;
   assert modRes == 0;
   
   divRes := 32 / -16;
   modRes := 32 % -16;
   assert divRes == -2;
   assert modRes == 0;
   
   divRes := -32 / 16;
   modRes := -32 % 16;
   assert divRes == -2;
   assert modRes == 0;
   
   divRes := -32 / -16;
   modRes := -32 % -16;
   assert divRes == 2;
   assert modRes == 0;

}