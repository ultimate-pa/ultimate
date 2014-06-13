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
loc_CP_0:
 if (nondet_bool()) {
  if (!( 1 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  v2 = 0;
  goto loc_2;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1+v2 <= 1 )) goto end;
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  v2 = 1;
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v1 = 1;
  goto loc_4;
 }
 goto end;
loc_3:
end:
;
}
