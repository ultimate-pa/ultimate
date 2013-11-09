int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc3;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  if (!( v2 <= v3 )) goto end;
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = -1+v2;
  v3 = v2+v3;
  goto loc1;
 }
 if (nondet_bool()) {
  v1 = -1+v1;
  v2 = -1+v2;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
end:
;
}
