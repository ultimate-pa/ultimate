int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v2 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  v5 = nondet();
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = v4;
  v2 = 10;
  v1 = 0;
  goto loc2;
 }
 goto end;
loc1:
end:
;
}
