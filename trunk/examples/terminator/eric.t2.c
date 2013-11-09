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
  if (!( 1+v1 <= v3 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v3 <= v2 )) goto end;
  v3 = 1+v3;
  if (!( v3 <= 1+v2 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v3 )) goto end;
  if (!( 1 <= v3 )) goto end;
  v3 = 0;
  if (!( v3 <= 1+v2 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  if (!( 1 <= v1 )) goto end;
  if (!( 1 <= v2 )) goto end;
  v3 = 1+v1;
  if (!( v3 <= 1+v2 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc1;
 }
 goto end;
end:
;
}
