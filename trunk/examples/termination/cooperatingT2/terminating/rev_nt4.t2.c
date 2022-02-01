int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v1 = 1;
  v2 = v3;
  v5 = v1;
  v4 = v2;
  if (!( 0 <= -1+v4 )) goto end;
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_3:
loc_1:
end:
;
}
