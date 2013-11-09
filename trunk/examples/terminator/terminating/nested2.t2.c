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
loc1:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v4 = 5000;
  if (!( 1 <= v4 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( v4 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v6 = nondet();
  if (!( 1 <= v4 )) goto end;
  v1 = -1+v1;
  v4 = -1+v4;
  if (!( v1 <= -1+v3 )) goto end;
  if (!( -1+v3 <= v1 )) goto end;
  if (!( v4 <= -1+v6 )) goto end;
  if (!( -1+v6 <= v4 )) goto end;
  if (!( 1 <= v6 )) goto end;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = nondet();
  v4 = nondet();
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v2 = nondet();
  v5 = nondet();
  if (!( 1 <= v4 )) goto end;
  v1 = -1+v1;
  v4 = -1+v4;
  if (!( v1 <= -1+v2 )) goto end;
  if (!( -1+v2 <= v1 )) goto end;
  if (!( v4 <= -1+v5 )) goto end;
  if (!( -1+v5 <= v4 )) goto end;
  if (!( 1 <= v2 )) goto end;
  if (!( 1 <= v5 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
end:
;
}
