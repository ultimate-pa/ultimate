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
int v9 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 2+v8 <= -1+2*v5 )) goto end;
  if (!( -1+2*v5 <= 2+v8 )) goto end;
  v6 = v5;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 2+v8 <= 2*v5 )) goto end;
  if (!( 2*v5 <= 2+v8 )) goto end;
  v6 = v5;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 3+v8 <= -1+2*v5 )) goto end;
  v6 = -1+v5;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+2*v5 <= 2+v8 )) goto end;
  v6 = 1+v5;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = v1;
  goto loc2;
 }
 if (nondet_bool()) {
  v2 = v2;
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v5 = v6;
  v3 = v4;
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v5 = v6;
  v3 = v4;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v5+v9 <= -1+2*v3 )) goto end;
  if (!( -1+2*v3 <= v5+v9 )) goto end;
  v4 = v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v5+v9 <= 2*v3 )) goto end;
  if (!( 2*v3 <= v5+v9 )) goto end;
  v4 = v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v5+v9 <= -1+2*v3 )) goto end;
  v4 = -1+v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+2*v3 <= v5+v9 )) goto end;
  v4 = 1+v3;
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 3 )) goto end;
  if (!( 0 <= v5 )) goto end;
  if (!( v7 <= 3 )) goto end;
  if (!( 0 <= v9 )) goto end;
  if (!( v9 <= 3 )) goto end;
  if (!( 0 <= v3 )) goto end;
  if (!( v3 <= 3 )) goto end;
  goto loc1;
 }
 goto end;
end:
;
}
