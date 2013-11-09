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
int v10 = nondet();
int v11 = nondet();
int v12 = nondet();
int v13 = nondet();
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
goto loc18;
loc18:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = v1;
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v16 <= 0 )) goto end;
  if (!( 0 <= v16 )) goto end;
  v16 = v17;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v2 = v2;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v8 = v8;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v9 = v9;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v10 = v10;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v11 = v11;
  goto loc9;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v12 = v12;
  goto loc10;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v13 = v13;
  goto loc11;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v14 = v14;
  goto loc12;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v15 = v15;
  goto loc13;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v3 = v3;
  goto loc14;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v4 = v4;
  goto loc15;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v5 = v5;
  goto loc16;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v6 = v6;
  goto loc17;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v7 = v7;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
end:
;
}
