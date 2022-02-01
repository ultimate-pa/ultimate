int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_2;
 }
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 42 <= v1 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 42 )) goto end;
  goto loc_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_5:
end:
;
}
