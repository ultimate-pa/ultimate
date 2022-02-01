int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_31;
loc_31:
 if (nondet_bool()) {
  goto loc_30;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  v4 = v3;
  goto loc_CP_7;
 }
 if (nondet_bool()) {
  goto loc_8;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_2;
 }
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_CP_11:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_4;
 }
 if (nondet_bool()) {
  goto loc_13;
 }
 goto end;
loc_CP_14:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_5;
 }
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc_3;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_2;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_CP_7;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_4;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  goto loc_CP_11;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_5;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  goto loc_CP_14;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_18;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_18;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_2;
 }
 if (nondet_bool()) {
  v3 = 2;
  goto loc_CP_7;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_2;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_4;
 }
 if (nondet_bool()) {
  v3 = 2;
  goto loc_CP_11;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_4;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_5;
 }
 if (nondet_bool()) {
  v3 = 2;
  goto loc_CP_14;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_5;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_24;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_24;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_2;
 }
 if (nondet_bool()) {
  v3 = 1;
  goto loc_17;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_2;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_4;
 }
 if (nondet_bool()) {
  v3 = 1;
  goto loc_19;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_4;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  if (!( 1+v4 <= 2 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_5;
 }
 if (nondet_bool()) {
  v3 = 1;
  goto loc_21;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_5;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  v4 = v3;
  goto loc_19;
 }
 if (nondet_bool()) {
  v3 = 2;
  goto loc_CP_6;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_30:
 if (nondet_bool()) {
  v4 = v3;
  goto loc_27;
 }
 if (nondet_bool()) {
  v3 = 1;
  goto loc_29;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_1:
loc_3:
end:
;
}
