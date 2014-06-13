int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 0 <= v2 )) goto end;
  v2 = -1+v2;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v2 = 999;
  goto loc_CP_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 0 <= v4 )) goto end;
  v4 = -1+v4;
  goto loc_CP_8;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v4 = 999;
  goto loc_CP_8;
 }
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc_CP_4;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v3 = 999;
  goto loc_CP_4;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v1 = 1;
  goto loc_3;
 }
 goto end;
loc_7:
end:
;
}
