int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  v2 = 2+v2;
  v1 = 2+v2;
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 20 <= v2 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 20 )) goto end;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v2 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_1:
end:
;
}
