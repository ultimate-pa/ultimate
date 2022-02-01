int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( -20+v2 <= 0 )) goto end;
  v1 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 0 <= -21+v2 )) goto end;
  goto loc_CP_2;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  if (!( -30+v3 <= 0 )) goto end;
  v2 = -1+v2;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 0 <= -31+v3 )) goto end;
  v3 = -1+v3;
  goto loc_4;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_1:
end:
;
}
