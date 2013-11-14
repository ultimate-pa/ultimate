int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_3;
loc_3:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  if (!( v2 <= v3 )) goto end;
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v2 = -1+v2;
  v3 = v2+v3;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  v1 = -1+v1;
  v2 = -1+v2;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
end:
;
}
