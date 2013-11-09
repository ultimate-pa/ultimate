int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = 1+v2;
  v3 = 1+v3;
  v4 = -1+v4;
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
  if (!( -1*v2+v3 <= 0 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2+v3 )) goto end;
  if (!( -1*v3+v4 <= 0 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2+v3 )) goto end;
  if (!( 0 <= -1-v3+v4 )) goto end;
  if (!( 0 <= -1-v2+v4 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2+v3 )) goto end;
  if (!( 0 <= -1-v3+v4 )) goto end;
  if (!( -1*v2+v4 <= 0 )) goto end;
  goto loc0;
 }
 goto end;
loc3:
loc3:
loc3:
end:
;
}
