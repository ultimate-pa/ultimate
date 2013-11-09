int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc2;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = 5;
  v2 = v1;
  if (!( v2 <= 0 )) goto end;
  goto loc1;
 }
 goto end;
loc1:
end:
;
}
