int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc17;
loc17:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v4 = nondet();
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v1 = -1+v1;
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 0 <= v6 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 0 )) goto end;
  goto loc6;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v2 = 1;
  v6 = -1*v1+v6;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v3 = 1;
  v1 = -1+v1;
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( 3 <= v2 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 2 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v2 <= 2 )) goto end;
  if (!( 2 <= v2 )) goto end;
  goto loc11;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v5 <= v4 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc12;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( v6 <= 255 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 256 <= v6 )) goto end;
  goto loc6;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v2 = 2;
  v6 = v1+v6;
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v3 = 1;
  v1 = -1+v1;
  goto loc14;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 2 <= v2 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 1 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( v2 <= 1 )) goto end;
  if (!( 1 <= v2 )) goto end;
  goto loc15;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v1 = 4;
  v3 = 0;
  v2 = 0;
  goto loc9;
 }
 goto end;
loc7:
end:
;
}
