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
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
int v23 = nondet();
int v24 = nondet();
int v25 = nondet();
int v26 = nondet();
int v27 = nondet();
goto loc25;
loc25:
 if (nondet_bool()) {
  goto loc24;
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
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  goto loc23;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1+v12 <= v2 )) goto end;
  v1 = 2+v1;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v2 <= v12 )) goto end;
  v13 = v2;
  v14 = v8+v13;
  v21 = nondet();
  v20 = nondet();
  v2 = v2+v9;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( -1+v4+v10 <= v1 )) goto end;
  v27 = v26;
  v26 = nondet();
  v23 = nondet();
  v4 = v4+v10;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v1 <= -2+v4+v10 )) goto end;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1+v8 <= v4 )) goto end;
  v8 = v9;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v4 <= v8 )) goto end;
  goto loc7;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v11 <= v8 )) goto end;
  v17 = nondet();
  v7 = -1+v7;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v11 )) goto end;
  v9 = nondet();
  v22 = nondet();
  v27 = nondet();
  v25 = nondet();
  v24 = nondet();
  v26 = 1;
  v23 = 0;
  goto loc10;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v3 = v3+v6;
  v2 = v2+v10;
  goto loc0;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v3 <= v6 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v3 )) goto end;
  v3 = v3-v6;
  v6 = nondet();
  goto loc13;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 1+v6 <= v10 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( v10 <= v6 )) goto end;
  goto loc18;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  v6 = nondet();
  goto loc13;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1+v12 <= v4 )) goto end;
  v1 = 2+v1;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v4 <= v12 )) goto end;
  v5 = -1*v2+v3+v4;
  v21 = nondet();
  v21 = nondet();
  v4 = v4+v11;
  goto loc4;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( -1+v2+v10 <= v1 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( v1 <= -2+v2+v10 )) goto end;
  goto loc4;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( v3 <= v2 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v3 )) goto end;
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v11 <= v2 )) goto end;
  v8 = v10;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v2 <= v11 )) goto end;
  goto loc20;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( 1+v7 <= 1 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v15 = nondet();
  v18 = nondet();
  v10 = nondet();
  v11 = nondet();
  v12 = nondet();
  v3 = 1;
  goto loc0;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( 1+v16 <= v7 )) goto end;
  v17 = 1;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( v7 <= v16 )) goto end;
  v19 = nondet();
  v7 = 1+v7;
  goto loc24;
 }
 goto end;
loc22:
end:
;
}
