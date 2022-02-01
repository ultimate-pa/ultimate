int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_9;
loc_9:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  v4 = v5;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v3 = nondet();
  v6 = v3;
  v3 = nondet();
  if (!( v1 <= 2*v6 )) goto end;
  if (!( 2*v6 <= v1 )) goto end;
  v1 = v6;
  if (!( v1 <= v6 )) goto end;
  if (!( v6 <= v1 )) goto end;
  if (!( 1 <= 2*v6 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  v2 = nondet();
  if (!( 1 <= v1 )) goto end;
  v3 = nondet();
  v6 = v3;
  v3 = nondet();
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v1 <= 2*v6 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1+2*v6 <= v1 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v1 = 1+3*v1;
  if (!( v1 <= 1+3*v2 )) goto end;
  if (!( 1+3*v2 <= v1 )) goto end;
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2*v6 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+2*v6 <= v2 )) goto end;
  goto loc_8;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
end:
;
}
