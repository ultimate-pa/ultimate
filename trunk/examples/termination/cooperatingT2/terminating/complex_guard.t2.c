int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 3 )) goto end;
  v1 = 1+v1;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_0;
 }
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v1 <= 2 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_5:
end:
;
}
