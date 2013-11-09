int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc3;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
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
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
end:
;
}
