//#Safe
/*
 * Date: 2020-12-22
 * Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * Modification of Kentoriginal.bpl in which I replaced the
 * nonlinear integer division of the form 1/x by an equivalent
 * case distinction.
 * 
 * Using SMTInterpol we get a result after 8 interations in
 * around one second.
 */

var _memory : [{ base : int, offset : int }] int;
var _memory_ptr : [{ base : int, offset : int }] { base : int, offset : int };

procedure routine_42_main() returns (helper_LIR18 : int)
modifies ;

{
var helper_LIR19 : int;
var helper_LIR20 : int;
var x_LIR35 : int;
var helper_LIR21 : int;
var helper_LIR22 : int;
var helper_LIR23 : int;
var helper_LIR24 : int;
var y_LIR36 : int;
var helper_LIR25 : int;
var helper_LIR26 : int;
var helper_LIR27 : int;
var helper_LIR28 : int;
var helper_LIR29 : int;
var helper_LIR31 : int;
var helper_LIR32 : int;
var helper_LIR33 : int;
var z_LIR37 : int;
var helper_LIR30 : int;
havoc helper_LIR18;
havoc helper_LIR19;
havoc helper_LIR20;
havoc x_LIR35;
havoc helper_LIR21;
havoc helper_LIR22;
havoc helper_LIR23;
havoc helper_LIR24;
havoc y_LIR36;
havoc helper_LIR25;
havoc helper_LIR26;
havoc helper_LIR27;
havoc helper_LIR28;
havoc helper_LIR29;
havoc helper_LIR31;
havoc helper_LIR32;
havoc helper_LIR33;
havoc z_LIR37;
havoc helper_LIR30;
    goto CFG_43;
CFG_43:
    assume  true;
    goto CFG_59;
CFG_59:
    assume  true;
    helper_LIR19 := 1;
    helper_LIR20 := (if x_LIR35 < helper_LIR19 then 1 else 0);
    if (helper_LIR20 != 0) {  goto CFG_51; } else {  goto CFG_60; }
CFG_60:
    assume  true;
    helper_LIR21 := 100;
    helper_LIR22 := (if x_LIR35 > helper_LIR21 then 1 else 0);
    if (helper_LIR22 != 0) {  goto CFG_51; } else {  goto CFG_61; }
CFG_61:
    assume  true;
    helper_LIR23 := 1;
    helper_LIR24 := (if y_LIR36 < helper_LIR23 then 1 else 0);
    if (helper_LIR24 != 0) {  goto CFG_52; } else {  goto CFG_62; }
CFG_62:
    assume  true;
    helper_LIR25 := 100;
    helper_LIR26 := (if y_LIR36 > helper_LIR25 then 1 else 0);
    if (helper_LIR26 != 0) {  goto CFG_52; } else {  goto CFG_54; }
CFG_54:
    assume  true;
    goto CFG_63;
CFG_63:
    assume  true;
    assume { :symbol "~swrap32" } (x_LIR35 + y_LIR36 > 2147483647 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36 - 4294967296) && (x_LIR35 + y_LIR36 < -2147483648 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36 + 4294967296) && (-2147483648 <= x_LIR35 + y_LIR36 && x_LIR35 + y_LIR36 <= 2147483647 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36);
    helper_LIR27 := ~swrap32(x_LIR35 + y_LIR36);
    helper_LIR28 := 1;
    helper_LIR29 := (if helper_LIR27 > helper_LIR28 then 1 else 0);
    if (helper_LIR29 != 0) {  goto CFG_55; } else {  goto CFG_53; }
CFG_53:
    assume  true;
    helper_LIR31 := 1;
    assume { :symbol "~swrap32" } (x_LIR35 + y_LIR36 > 2147483647 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36 - 4294967296) && (x_LIR35 + y_LIR36 < -2147483648 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36 + 4294967296) && (-2147483648 <= x_LIR35 + y_LIR36 && x_LIR35 + y_LIR36 <= 2147483647 ==> ~swrap32(x_LIR35 + y_LIR36) == x_LIR35 + y_LIR36);
    helper_LIR32 := ~swrap32(x_LIR35 + y_LIR36);
    assert { :LIR "74" } { :check "div-by-zero" } helper_LIR32 != 0;
//    helper_LIR33 := helper_LIR31 / helper_LIR32;
    if (helper_LIR32 > 1) {
        helper_LIR33 := 0;
    } else if (helper_LIR32 == 1) {
        helper_LIR33 := 1;
    } else if (helper_LIR32 < 0) {
        helper_LIR33 := -1;
    } else {
        assert false;
    }
    z_LIR37 := helper_LIR33;
    helper_LIR18 := z_LIR37;
    goto CFG_47;
CFG_55:
    assume  true;
    helper_LIR30 := 1;
    assume { :symbol "~swrap32" } (x_LIR35 - helper_LIR30 > 2147483647 ==> ~swrap32(x_LIR35 - helper_LIR30) == x_LIR35 - helper_LIR30 - 4294967296) && (x_LIR35 - helper_LIR30 < -2147483648 ==> ~swrap32(x_LIR35 - helper_LIR30) == x_LIR35 - helper_LIR30 + 4294967296) && (-2147483648 <= x_LIR35 - helper_LIR30 && x_LIR35 - helper_LIR30 <= 2147483647 ==> ~swrap32(x_LIR35 - helper_LIR30) == x_LIR35 - helper_LIR30);
    x_LIR35 := ~swrap32(x_LIR35 - helper_LIR30);
    goto CFG_63;
CFG_52:
    assume  true;
    helper_LIR18 := 0;
    goto CFG_47;
CFG_51:
    assume  true;
    helper_LIR18 := 0;
    goto CFG_47;
CFG_47:
    assume  true;
}

function  ~swrap32(in0 : int) returns (out : int) ;

const #funAddr~~1~LIR39 : { base : int, offset : int };
const #funAddr~~2~LIR40 : { base : int, offset : int };
const #funAddr~~3~LIR41 : { base : int, offset : int };
const #funAddr~main~4~LIR42 : { base : int, offset : int };

axiom  #funAddr~~1~LIR39 == { base : -1, offset : 1 };
axiom  #funAddr~~2~LIR40 == { base : -1, offset : 2 };
axiom  #funAddr~~3~LIR41 == { base : -1, offset : 3 };
axiom  #funAddr~main~4~LIR42 == { base : -1, offset : 4 };
