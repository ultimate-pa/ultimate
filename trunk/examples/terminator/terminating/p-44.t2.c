int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1+v2 )) goto end;
  if (!( v3 <= 0 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1+v2 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  if (!( v2+v3 <= 0 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1+v2 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  if (!( 0 <= -1+v2+v3 )) goto end;
  v2 = -2+v3;
  v3 = 1+v2;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
loc1:
loc1:
end:
;
}
