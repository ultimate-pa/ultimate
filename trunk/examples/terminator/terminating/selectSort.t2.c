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
goto loc12;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( -1+v2 <= v5 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= -1+v2 )) goto end;
  v5 = 1+v5;
  goto loc6;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc7;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v6 = v4;
  goto loc9;
 }
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v7 = nondet();
  v5 = 1+v5;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc10;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( -1+v2 <= v5 )) goto end;
  v5 = 0;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= -1+v2 )) goto end;
  v6 = v5;
  v4 = 1+v5;
  goto loc7;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = v1;
  v5 = 0;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc0;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v8 = nondet();
  v3 = 0;
  goto loc0;
 }
 goto end;
loc5:
end:
;
}
