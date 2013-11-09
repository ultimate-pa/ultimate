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
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v5 = nondet();
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v6 <= -1 )) goto end;
  if (!( -1 <= v6 )) goto end;
  v2 = 0;
  v1 = nondet();
  v4 = nondet();
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 0 <= v6 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= -1 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v3 = nondet();
  v6 = nondet();
  goto loc3;
 }
 goto end;
loc1:
end:
;
}
