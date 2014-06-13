int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  v3 = nondet();
  goto loc_4;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v1 = 1;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc_1;
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
  goto loc_6;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v1 = 0;
  goto loc_5;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_7;
 }
 goto end;
loc_6:
end:
;
}
