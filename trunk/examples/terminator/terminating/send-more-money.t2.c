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
goto loc_68;
loc_68:
 if (nondet_bool()) {
  goto loc_67;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v2 = v20;
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 10 <= v12 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= 10 )) goto end;
  v20 = 1;
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v1 = v13;
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 10 <= v10 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= 10 )) goto end;
  goto loc_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 10 <= v9 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= 10 )) goto end;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 10 <= v7 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 10 )) goto end;
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 10 <= v5 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 10 )) goto end;
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 10 <= v8 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 10 )) goto end;
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 10 <= v6 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 10 )) goto end;
  goto loc_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 10 <= v11 )) goto end;
  v20 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 10 )) goto end;
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v1 = v19;
  goto loc_11;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  v13 = 1;
  goto loc_3;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v19 = 1;
  goto loc_12;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( v10 <= v12 )) goto end;
  if (!( v12 <= v10 )) goto end;
  v19 = 0;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v10 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v12 )) goto end;
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v19 = 0;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_15;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  v1 = v18;
  goto loc_16;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  v18 = 1;
  goto loc_17;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v9 <= v12 )) goto end;
  if (!( v12 <= v9 )) goto end;
  v18 = 0;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v9 )) goto end;
  goto loc_18;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v12 )) goto end;
  goto loc_18;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( v9 <= v10 )) goto end;
  if (!( v10 <= v9 )) goto end;
  v18 = 0;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc_19;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc_19;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( v11 <= v12 )) goto end;
  if (!( v12 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v11 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v12 )) goto end;
  goto loc_13;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v18 = 0;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_20;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  v1 = v17;
  goto loc_22;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  v17 = 1;
  goto loc_23;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( v7 <= v12 )) goto end;
  if (!( v12 <= v7 )) goto end;
  v17 = 0;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v7 )) goto end;
  goto loc_24;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v12 )) goto end;
  goto loc_24;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  if (!( v7 <= v10 )) goto end;
  if (!( v10 <= v7 )) goto end;
  v17 = 0;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v7 )) goto end;
  goto loc_25;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v10 )) goto end;
  goto loc_25;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  if (!( v7 <= v9 )) goto end;
  if (!( v9 <= v7 )) goto end;
  v17 = 0;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v7 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v9 )) goto end;
  goto loc_26;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  if (!( v11 <= v10 )) goto end;
  if (!( v10 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v11 )) goto end;
  goto loc_21;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v10 )) goto end;
  goto loc_21;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v17 = 0;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_27;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_27;
 }
 goto end;
loc_30:
 if (nondet_bool()) {
  v1 = v16;
  goto loc_29;
 }
 goto end;
loc_31:
 if (nondet_bool()) {
  v16 = 1;
  goto loc_30;
 }
 goto end;
loc_32:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  if (!( v12 <= v5 )) goto end;
  v16 = 0;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  goto loc_31;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v12 )) goto end;
  goto loc_31;
 }
 goto end;
loc_33:
 if (nondet_bool()) {
  if (!( v5 <= v10 )) goto end;
  if (!( v10 <= v5 )) goto end;
  v16 = 0;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v5 )) goto end;
  goto loc_32;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v10 )) goto end;
  goto loc_32;
 }
 goto end;
loc_34:
 if (nondet_bool()) {
  if (!( v11 <= v9 )) goto end;
  if (!( v9 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v11 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v9 )) goto end;
  goto loc_28;
 }
 goto end;
loc_35:
 if (nondet_bool()) {
  if (!( v5 <= v9 )) goto end;
  if (!( v9 <= v5 )) goto end;
  v16 = 0;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v5 )) goto end;
  goto loc_33;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v9 )) goto end;
  goto loc_33;
 }
 goto end;
loc_36:
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  if (!( v7 <= v5 )) goto end;
  v16 = 0;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc_35;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v7 )) goto end;
  goto loc_35;
 }
 goto end;
loc_37:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v16 = 0;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_36;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_36;
 }
 goto end;
loc_38:
 if (nondet_bool()) {
  v1 = v15;
  goto loc_37;
 }
 goto end;
loc_39:
 if (nondet_bool()) {
  if (!( v11 <= v7 )) goto end;
  if (!( v7 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v11 )) goto end;
  goto loc_34;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v7 )) goto end;
  goto loc_34;
 }
 goto end;
loc_40:
 if (nondet_bool()) {
  v15 = 1;
  goto loc_38;
 }
 goto end;
loc_41:
 if (nondet_bool()) {
  if (!( v8 <= v12 )) goto end;
  if (!( v12 <= v8 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v8 )) goto end;
  goto loc_40;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v12 )) goto end;
  goto loc_40;
 }
 goto end;
loc_42:
 if (nondet_bool()) {
  if (!( v8 <= v10 )) goto end;
  if (!( v10 <= v8 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v8 )) goto end;
  goto loc_41;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v10 )) goto end;
  goto loc_41;
 }
 goto end;
loc_43:
 if (nondet_bool()) {
  if (!( v8 <= v9 )) goto end;
  if (!( v9 <= v8 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v8 )) goto end;
  goto loc_42;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v9 )) goto end;
  goto loc_42;
 }
 goto end;
loc_44:
 if (nondet_bool()) {
  if (!( v8 <= v7 )) goto end;
  if (!( v7 <= v8 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v8 )) goto end;
  goto loc_43;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v7 )) goto end;
  goto loc_43;
 }
 goto end;
loc_45:
 if (nondet_bool()) {
  if (!( v8 <= v5 )) goto end;
  if (!( v5 <= v8 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v8 )) goto end;
  goto loc_44;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  goto loc_44;
 }
 goto end;
loc_46:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v15 = 0;
  goto loc_38;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_45;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_45;
 }
 goto end;
loc_47:
 if (nondet_bool()) {
  if (!( v11 <= v5 )) goto end;
  if (!( v5 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v11 )) goto end;
  goto loc_39;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v5 )) goto end;
  goto loc_39;
 }
 goto end;
loc_48:
 if (nondet_bool()) {
  v1 = v14;
  goto loc_46;
 }
 goto end;
loc_49:
 if (nondet_bool()) {
  v14 = 1;
  goto loc_48;
 }
 goto end;
loc_50:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  if (!( v12 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  goto loc_49;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v12 )) goto end;
  goto loc_49;
 }
 goto end;
loc_51:
 if (nondet_bool()) {
  if (!( v6 <= v10 )) goto end;
  if (!( v10 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v6 )) goto end;
  goto loc_50;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v10 )) goto end;
  goto loc_50;
 }
 goto end;
loc_52:
 if (nondet_bool()) {
  if (!( v6 <= v9 )) goto end;
  if (!( v9 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v6 )) goto end;
  goto loc_51;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc_51;
 }
 goto end;
loc_53:
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  if (!( v7 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  goto loc_52;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v7 )) goto end;
  goto loc_52;
 }
 goto end;
loc_54:
 if (nondet_bool()) {
  if (!( v11 <= v8 )) goto end;
  if (!( v8 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v11 )) goto end;
  goto loc_47;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v8 )) goto end;
  goto loc_47;
 }
 goto end;
loc_55:
 if (nondet_bool()) {
  if (!( v6 <= v5 )) goto end;
  if (!( v5 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  goto loc_53;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  goto loc_53;
 }
 goto end;
loc_56:
 if (nondet_bool()) {
  if (!( v6 <= v8 )) goto end;
  if (!( v8 <= v6 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v6 )) goto end;
  goto loc_55;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v8 )) goto end;
  goto loc_55;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v14 = 0;
  goto loc_48;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_56;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_56;
 }
 goto end;
loc_57:
 if (nondet_bool()) {
  goto loc_58;
 }
 goto end;
loc_59:
 if (nondet_bool()) {
  v22 = 0;
  goto loc_57;
 }
 goto end;
loc_60:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v22 = 1;
  goto loc_57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_59;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_59;
 }
 goto end;
loc_61:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v22 = 1;
  goto loc_57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_60;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_60;
 }
 goto end;
loc_62:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v22 = 1;
  goto loc_57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_61;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_61;
 }
 goto end;
loc_63:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v22 = 1;
  goto loc_57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_62;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_62;
 }
 goto end;
loc_64:
 if (nondet_bool()) {
  v3 = v21;
  v4 = nondet();
  goto loc_63;
 }
 goto end;
loc_65:
 if (nondet_bool()) {
  v21 = 1;
  goto loc_64;
 }
 goto end;
loc_66:
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  if (!( 0 <= v11 )) goto end;
  v21 = 0;
  goto loc_64;
 }
 if (nondet_bool()) {
  if (!( 1 <= v11 )) goto end;
  goto loc_65;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 0 )) goto end;
  goto loc_65;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  v21 = 0;
  goto loc_64;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_66;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  goto loc_66;
 }
 goto end;
loc_67:
 if (nondet_bool()) {
  if (!( v11 <= v6 )) goto end;
  if (!( v6 <= v11 )) goto end;
  v13 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v11 )) goto end;
  goto loc_54;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v6 )) goto end;
  goto loc_54;
 }
 goto end;
loc_58:
end:
;
}
