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
loc1:
 if (nondet_bool()) {
  if (!( -1+2*v3 <= v2+v5 )) goto end;
  if (!( v2+v5 <= 2*v3 )) goto end;
  v4 = v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v2+v5 <= -1+2*v3 )) goto end;
  v4 = -1+v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+2*v3 <= v2+v5 )) goto end;
  v4 = 1+v3;
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = v1;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v3 = v4;
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 0 <= v5 )) goto end;
  if (!( v5 <= 3 )) goto end;
  if (!( 0 <= v3 )) goto end;
  if (!( v3 <= 3 )) goto end;
  v2 = 2;
  goto loc1;
 }
 goto end;
end:
;
}
