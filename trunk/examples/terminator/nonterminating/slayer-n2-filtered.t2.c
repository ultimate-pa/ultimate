int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 10 <= v2 )) goto end;
  v4 = v5;
  goto loc3;
 }
 if (nondet_bool()) {
  v3 = nondet();
  if (!( 1+v2 <= 10 )) goto end;
  v2 = -1+v2;
  if (!( v2 <= -1+v3 )) goto end;
  if (!( -1+v3 <= v2 )) goto end;
  if (!( 1+v3 <= 10 )) goto end;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = 0;
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 0 )) goto end;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1+v2 <= 10 )) goto end;
  v2 = -1+v2;
  v2 = nondet();
  if (!( -1 <= v2 )) goto end;
  if (!( v2 <= -1 )) goto end;
  v1 = nondet();
  if (!( v1 <= v2 )) goto end;
  if (!( v2 <= v1 )) goto end;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
end:
;
}
