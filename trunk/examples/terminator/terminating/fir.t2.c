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
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v4 <= v2 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc_0;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 if (nondet_bool()) {
  v2 = -1+v2;
  goto loc_1;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v2 <= v7 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v2 )) goto end;
  v1 = nondet();
  v7 = 1+v7;
  goto loc_CP_7;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v6 <= v5 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  v1 = nondet();
  v7 = 1;
  goto loc_CP_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v6 = 10;
  v4 = 35;
  v8 = 285;
  v3 = nondet();
  v2 = v3;
  v5 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_8:
end:
;
}
