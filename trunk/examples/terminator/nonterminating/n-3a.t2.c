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
goto loc13;
loc13:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( -1*v6+v7 <= 0 )) goto end;
  if (!( -1*v6+v7 <= 0 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( -1*v6+v7 <= 0 )) goto end;
  if (!( -1*v6+v7 <= 0 )) goto end;
  if (!( v6 <= v7 )) goto end;
  if (!( v7 <= v6 )) goto end;
  v5 = nondet();
  if (!( v5 <= 0 )) goto end;
  if (!( 0 <= v5 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( -1*v6+v7 <= 0 )) goto end;
  if (!( -1*v6+v7 <= 0 )) goto end;
  if (!( v6 <= v7 )) goto end;
  if (!( v7 <= v6 )) goto end;
  v5 = nondet();
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v6+v7 )) goto end;
  v5 = nondet();
  if (!( v5 <= 0 )) goto end;
  if (!( 0 <= v5 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v6+v7 )) goto end;
  v5 = nondet();
  goto loc11;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v2 = v2;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v3 = v3;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v6 = 1+v6;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v4 = v4;
  goto loc12;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v6 = 1+v6;
  goto loc10;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
end:
;
}
