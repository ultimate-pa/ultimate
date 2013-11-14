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
int v12 = nondet();
int v13 = nondet();
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
int v23 = nondet();
int v24 = nondet();
goto loc_50;
loc_50:
 if (nondet_bool()) {
  goto loc_49;
 }
 goto end;
loc_CP_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_21:
 if (nondet_bool()) {
  goto loc_22;
 }
 goto end;
loc_CP_24:
 if (nondet_bool()) {
  goto loc_25;
 }
 goto end;
loc_CP_30:
 if (nondet_bool()) {
  goto loc_31;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v18 = v15;
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v18 <= 0 )) goto end;
  if (!( 0 <= v18 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v18 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v15 = 10;
  goto loc_2;
 }
 if (nondet_bool()) {
  v15 = 0;
  goto loc_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v6 = 50;
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  goto loc_10;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( v5 <= v1 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v5 )) goto end;
  v1 = 1+v1;
  goto loc_CP_12;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v21 = v10;
  goto loc_15;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( v21 <= 0 )) goto end;
  if (!( 0 <= v21 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v21 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1+v21 <= 0 )) goto end;
  goto loc_13;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  v10 = 10;
  goto loc_14;
 }
 if (nondet_bool()) {
  v10 = 0;
  goto loc_14;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  v17 = v14;
  goto loc_19;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v17 <= 0 )) goto end;
  if (!( 0 <= v17 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v17 )) goto end;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v17 <= 0 )) goto end;
  goto loc_17;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v14 = 10;
  goto loc_18;
 }
 if (nondet_bool()) {
  v14 = 0;
  goto loc_18;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  goto loc_7;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v5 = 200;
  goto loc_23;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  if (!( v8 <= v4 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v8 )) goto end;
  v4 = 1+v4;
  goto loc_CP_21;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  v4 = 0;
  goto loc_CP_21;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  v24 = v9;
  goto loc_28;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  if (!( v24 <= 0 )) goto end;
  if (!( 0 <= v24 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v24 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  if (!( 1+v24 <= 0 )) goto end;
  goto loc_26;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  v9 = 10;
  goto loc_27;
 }
 if (nondet_bool()) {
  v9 = 0;
  goto loc_27;
 }
 goto end;
loc_32:
 if (nondet_bool()) {
  goto loc_29;
 }
 goto end;
loc_33:
 if (nondet_bool()) {
  v20 = v13;
  goto loc_34;
 }
 goto end;
loc_35:
 if (nondet_bool()) {
  goto loc_36;
 }
 goto end;
loc_34:
 if (nondet_bool()) {
  if (!( v20 <= 0 )) goto end;
  if (!( 0 <= v20 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v20 )) goto end;
  goto loc_32;
 }
 if (nondet_bool()) {
  if (!( 1+v20 <= 0 )) goto end;
  goto loc_32;
 }
 goto end;
loc_31:
 if (nondet_bool()) {
  if (!( v7 <= v3 )) goto end;
  goto loc_35;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v7 )) goto end;
  v3 = 1+v3;
  goto loc_CP_30;
 }
 goto end;
loc_37:
 if (nondet_bool()) {
  v3 = 0;
  goto loc_CP_30;
 }
 goto end;
loc_38:
 if (nondet_bool()) {
  v23 = v12;
  goto loc_39;
 }
 goto end;
loc_39:
 if (nondet_bool()) {
  if (!( v23 <= 0 )) goto end;
  if (!( 0 <= v23 )) goto end;
  goto loc_35;
 }
 if (nondet_bool()) {
  if (!( 1 <= v23 )) goto end;
  goto loc_37;
 }
 if (nondet_bool()) {
  if (!( 1+v23 <= 0 )) goto end;
  goto loc_37;
 }
 goto end;
loc_40:
 if (nondet_bool()) {
  v12 = 10;
  goto loc_38;
 }
 if (nondet_bool()) {
  v12 = 0;
  goto loc_38;
 }
 goto end;
loc_41:
 if (nondet_bool()) {
  goto loc_40;
 }
 goto end;
loc_42:
 if (nondet_bool()) {
  v19 = v16;
  goto loc_43;
 }
 goto end;
loc_43:
 if (nondet_bool()) {
  if (!( v19 <= 0 )) goto end;
  if (!( 0 <= v19 )) goto end;
  goto loc_35;
 }
 if (nondet_bool()) {
  if (!( 1 <= v19 )) goto end;
  goto loc_41;
 }
 if (nondet_bool()) {
  if (!( 1+v19 <= 0 )) goto end;
  goto loc_41;
 }
 goto end;
loc_44:
 if (nondet_bool()) {
  v16 = 10;
  goto loc_42;
 }
 if (nondet_bool()) {
  v16 = 0;
  goto loc_42;
 }
 goto end;
loc_45:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_44;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc_35;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v7 = 20;
  goto loc_45;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v13 = 10;
  goto loc_33;
 }
 if (nondet_bool()) {
  v13 = 0;
  goto loc_33;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( v6 <= v2 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v6 )) goto end;
  v2 = 1+v2;
  goto loc_CP_24;
 }
 goto end;
loc_46:
 if (nondet_bool()) {
  v2 = 0;
  goto loc_CP_24;
 }
 goto end;
loc_47:
 if (nondet_bool()) {
  v22 = v11;
  goto loc_48;
 }
 goto end;
loc_48:
 if (nondet_bool()) {
  if (!( v22 <= 0 )) goto end;
  if (!( 0 <= v22 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v22 )) goto end;
  goto loc_46;
 }
 if (nondet_bool()) {
  if (!( 1+v22 <= 0 )) goto end;
  goto loc_46;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v11 = 10;
  goto loc_47;
 }
 if (nondet_bool()) {
  v11 = 0;
  goto loc_47;
 }
 goto end;
loc_49:
 if (nondet_bool()) {
  v8 = 100;
  goto loc_8;
 }
 goto end;
loc_36:
end:
;
}
