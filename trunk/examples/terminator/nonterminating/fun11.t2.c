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
goto loc12;
loc12:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  goto loc8;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v5 = nondet();
  v8 = v5;
  v9 = v8;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v2 = v2;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 0 <= -1+v9 )) goto end;
  v9 = 1+v9;
  goto loc4;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v3 = v3;
  goto loc9;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 0 <= -1+v9 )) goto end;
  v9 = 1+v9;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  v1 = nondet();
  goto loc3;
 }
 if (nondet_bool()) {
  v6 = nondet();
  v7 = v6;
  goto loc10;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v4 = v4;
  goto loc11;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 0 <= -1+v9 )) goto end;
  v9 = 1+v9;
  goto loc4;
 }
 goto end;
loc3:
loc3:
loc3:
end:
;
}
