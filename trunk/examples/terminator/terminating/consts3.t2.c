int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc3;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = -1+v1;
  if (!( 201 <= v1 )) goto end;
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
