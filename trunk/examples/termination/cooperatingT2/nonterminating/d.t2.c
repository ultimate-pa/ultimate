int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_3;
loc_3:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( 1 <= 1+v3 )) goto end;
  if (!( 1 <= v3 )) goto end;
  v3 = nondet();
  v1 = v2;
  if (!( 1 <= 1+v3 )) goto end;
  if (!( 1 <= v3 )) goto end;
  v3 = nondet();
  if (!( 0 <= -1*v1 )) goto end;
  if (!( -1*v1 <= 0 )) goto end;
  v2 = v4;
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
  goto loc_CP_0;
 }
 goto end;
end:
;
}
