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
goto loc31;
loc31:
 if (nondet_bool()) {
  goto loc30;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v13 = v12;
  goto loc7;
 }
 if (nondet_bool()) {
  goto loc8;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v1 = v1;
  goto loc9;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc2;
 }
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v2 = v2;
  goto loc12;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc4;
 }
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v3 = v3;
  goto loc15;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  if (!( 0 <= v11 )) goto end;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v10 <= 1 )) goto end;
  if (!( 1 <= v10 )) goto end;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v10 <= 1 )) goto end;
  if (!( 1 <= v10 )) goto end;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v10 <= 1 )) goto end;
  if (!( 1 <= v10 )) goto end;
  goto loc3;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v10 = 0;
  goto loc2;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v10 = 0;
  goto loc4;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v10 = 0;
  goto loc5;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v4 = v4;
  goto loc18;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc2;
 }
 if (nondet_bool()) {
  v12 = 2;
  goto loc7;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v10 = 0;
  goto loc2;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  v5 = v5;
  goto loc20;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc4;
 }
 if (nondet_bool()) {
  v12 = 2;
  goto loc11;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  v10 = 0;
  goto loc4;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  v6 = v6;
  goto loc22;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  v12 = 2;
  goto loc14;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v10 = 0;
  goto loc5;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  v7 = v7;
  goto loc24;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc2;
 }
 if (nondet_bool()) {
  v12 = 1;
  goto loc17;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  v10 = 0;
  goto loc2;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v8 = v8;
  goto loc26;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc4;
 }
 if (nondet_bool()) {
  v12 = 1;
  goto loc19;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  v10 = 0;
  goto loc4;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  v9 = v9;
  goto loc28;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  v12 = 1;
  goto loc21;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  v10 = 0;
  goto loc5;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  v13 = v12;
  goto loc19;
 }
 if (nondet_bool()) {
  v12 = 2;
  goto loc6;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  v13 = v12;
  goto loc27;
 }
 if (nondet_bool()) {
  v12 = 1;
  goto loc29;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc3:
loc3:
loc3:
loc3:
loc3:
loc1:
loc3:
end:
;
}
