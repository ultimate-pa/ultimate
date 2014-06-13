int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc_3;
loc_3:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2000 )) goto end;
  v1 = 1000+v1;
  if (!( 111 <= v1 )) goto end;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v2 = 3000;
  goto loc_CP_0;
 }
 goto end;
end:
;
}
