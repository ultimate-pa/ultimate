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
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( -1+v2 <= v5 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= -1+v2 )) goto end;
  v5 = 1+v5;
  goto loc_CP_6;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_CP_7;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v6 = nondet();
  goto loc_9;
 }
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( -1+v2-v5 <= v4 )) goto end;
  v5 = 1+v5;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= -1+v2-v5 )) goto end;
  goto loc_10;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( -1+v2 <= v5 )) goto end;
  v5 = 0;
  goto loc_CP_6;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= -1+v2 )) goto end;
  v4 = 0;
  goto loc_CP_7;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = v1;
  v5 = 0;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc_CP_0;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v7 = nondet();
  v3 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_5:
end:
;
}
