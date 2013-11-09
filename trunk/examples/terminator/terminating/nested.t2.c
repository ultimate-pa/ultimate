int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
int v8 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v6 = nondet();
  if (!( 1 <= v6 )) goto end;
  if (!( 1 <= v3 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  v1 = v2;
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  if (!( v6 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  v5 = nondet();
  v8 = nondet();
  if (!( 1 <= v6 )) goto end;
  v3 = -1+v3;
  v6 = -1+v6;
  if (!( v3 <= -1+v5 )) goto end;
  if (!( -1+v5 <= v3 )) goto end;
  if (!( v6 <= -1+v8 )) goto end;
  if (!( -1+v8 <= v6 )) goto end;
  if (!( 1 <= v8 )) goto end;
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v3 = nondet();
  v6 = nondet();
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v4 = nondet();
  v7 = nondet();
  if (!( 1 <= v6 )) goto end;
  v3 = -1+v3;
  v6 = -1+v6;
  if (!( v3 <= -1+v4 )) goto end;
  if (!( -1+v4 <= v3 )) goto end;
  if (!( v6 <= -1+v7 )) goto end;
  if (!( -1+v7 <= v6 )) goto end;
  if (!( 1 <= v4 )) goto end;
  if (!( 1 <= v7 )) goto end;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc3:
end:
;
}
