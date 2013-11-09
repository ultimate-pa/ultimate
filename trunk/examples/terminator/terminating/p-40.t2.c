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
  goto loc0;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 500 <= v1 )) goto end;
  v3 = v6;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 500 )) goto end;
  v1 = 1+v1;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = v5;
  v2 = v4;
  v1 = v2;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 500 <= v1 )) goto end;
  v3 = v6;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 500 )) goto end;
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
loc3:
end:
;
}
