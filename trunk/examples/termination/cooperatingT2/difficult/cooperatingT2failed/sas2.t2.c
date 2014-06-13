int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_17;
loc_17:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  v4 = nondet();
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v1 = -1+v1;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 0 <= v6 )) goto end;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 0 )) goto end;
  goto loc_6;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v2 = 1;
  v6 = -1*v1+v6;
  goto loc_8;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v3 = 1;
  v1 = -1+v1;
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 3 <= v2 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 2 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( v2 <= 2 )) goto end;
  if (!( 2 <= v2 )) goto end;
  goto loc_11;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v5 <= v4 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc_12;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v6 <= 255 )) goto end;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( 256 <= v6 )) goto end;
  goto loc_6;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v2 = 2;
  v6 = v1+v6;
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v3 = 1;
  v1 = -1+v1;
  goto loc_14;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 2 <= v2 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 1 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( v2 <= 1 )) goto end;
  if (!( 1 <= v2 )) goto end;
  goto loc_15;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  v1 = 4;
  v3 = 0;
  v2 = 0;
  goto loc_CP_9;
 }
 goto end;
loc_7:
end:
;
}
