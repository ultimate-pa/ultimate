int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
int v8 = nondet();
int v9 = nondet();
int v10 = nondet();
int v11 = nondet();
goto loc_55;
loc_55:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( v11 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v3 = nondet();
  v7 = v3;
  v3 = nondet();
  if (!( 0 <= v7 )) goto end;
  if (!( v7 <= 0 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v3 = nondet();
  v7 = v3;
  v3 = nondet();
  goto loc_18;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  goto loc_8;
 }
 goto end;
loc_CP_12:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( v11 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  goto loc_14;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v2 = 0;
  v1 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  goto loc_5;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_4;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( v11 <= 0 )) goto end;
  v6 = v9;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  if (!( 1 <= v11 )) goto end;
  if (!( 1 <= v10+v11 )) goto end;
  goto loc_11;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_10;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_13;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_15;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_19;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  goto loc_19;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  v1 = 1;
  v4 = v10;
  v5 = v11;
  goto loc_17;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( 1+v10 <= v4 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( 1+v11 <= v5 )) goto end;
  goto loc_21;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( v5 <= v11 )) goto end;
  if (!( v4+v5 <= v10+v11 )) goto end;
  v2 = 1;
  goto loc_22;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( 1+v10 <= v4 )) goto end;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( 1+v11 <= v5 )) goto end;
  goto loc_24;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( v5 <= v11 )) goto end;
  if (!( v4+v5 <= v10+v11 )) goto end;
  v2 = 1;
  goto loc_22;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( 1+v10 <= v4 )) goto end;
  goto loc_25;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( 1+v11 <= v5 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( v5 <= v11 )) goto end;
  if (!( v4+v5 <= v10+v11 )) goto end;
  v2 = 1;
  goto loc_22;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( 1+v10 <= v4 )) goto end;
  goto loc_27;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( 1+v11 <= v5 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  if (!( v4 <= v10 )) goto end;
  if (!( v5 <= v11 )) goto end;
  if (!( v4+v5 <= v10+v11 )) goto end;
  v2 = 1;
  goto loc_22;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_29;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_30;
 }
 goto end;
loc_30:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_31;
 }
 goto end;
loc_31:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_32;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_32;
 }
 goto end;
loc_32:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_33:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_34;
 }
 goto end;
loc_34:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_35;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_35;
 }
 goto end;
loc_35:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_36;
 }
 goto end;
loc_36:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_37;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_37;
 }
 goto end;
loc_37:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_6;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_38;
 }
 goto end;
loc_38:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_39;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_39;
 }
 goto end;
loc_39:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_6;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_40;
 }
 goto end;
loc_40:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_41;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_41;
 }
 goto end;
loc_41:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_6;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_42;
 }
 goto end;
loc_42:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_43;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_43;
 }
 goto end;
loc_43:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_44;
 }
 goto end;
loc_44:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_45;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_45;
 }
 goto end;
loc_45:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_46:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_9;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_47;
 }
 goto end;
loc_47:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_48;
 }
 goto end;
loc_48:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_2;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_49;
 }
 goto end;
loc_49:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_50;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_50;
 }
 goto end;
loc_50:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_6;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_51;
 }
 goto end;
loc_51:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_52;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_52;
 }
 goto end;
loc_52:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_6;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v10 = -2+v11;
  v11 = 1+v10;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v8 = v3;
  v3 = nondet();
  goto loc_53;
 }
 goto end;
loc_53:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_54;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_54;
 }
 goto end;
loc_54:
 if (nondet_bool()) {
  v10 = -1+v10;
  v11 = v10;
  goto loc_CP_1;
 }
 goto end;
loc_22:
loc_3:
end:
;
}
