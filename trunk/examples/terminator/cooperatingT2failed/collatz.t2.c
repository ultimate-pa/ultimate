int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+2*v2 <= v1 )) goto end;
  if (!( v1 <= 1+2*v2 )) goto end;
  v1 = 1+3*v1;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 2*v2 <= v1 )) goto end;
  if (!( v1 <= 2*v2 )) goto end;
  v1 = v2;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1+v1 <= 2 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v1 <= 4 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 5 <= v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v1 = nondet();
  if (!( 1 <= v1 )) goto end;
  goto loc_CP_1;
 }
 goto end;
end:
;
}
