int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 0 <= -2-v5 )) goto end;
  v5 = 1+v5;
  v6 = 1+v6;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1-v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v2;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 0 <= -2+v3 )) goto end;
  if (!( 0 <= -2+v4 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( -1+v3 <= 0 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 goto end;
loc3:
loc3:
end:
;
}
