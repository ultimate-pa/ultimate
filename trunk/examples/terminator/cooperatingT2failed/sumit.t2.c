int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v2 <= v3 )) goto end;
  v3 = 0;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( v3 <= v2 )) goto end;
  v3 = 1+v3;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v4 = nondet();
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v3 <= v1 )) goto end;
  if (!( v1 <= v3 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= v2 )) goto end;
  v3 = 1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_6:
end:
;
}
