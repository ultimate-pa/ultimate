int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 36 <= v1 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 36 )) goto end;
  v3 = 1+v3;
  v1 = 1+v1;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v2 <= 127 )) goto end;
  v3 = nondet();
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 128 <= v2 )) goto end;
  goto loc_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_3;
 }
 goto end;
loc_1:
end:
;
}
