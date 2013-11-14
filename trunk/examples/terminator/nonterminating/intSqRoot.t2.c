int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v4 = v2;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  v3 = v2;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v3 <= 1+v4 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 2+v4 <= v3 )) goto end;
  v2 = nondet();
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v4 = 1;
  v3 = v1;
  goto loc_CP_1;
 }
 goto end;
loc_3:
end:
;
}
