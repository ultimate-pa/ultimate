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
goto loc46;
loc46:
 if (nondet_bool()) {
  goto loc45;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc41;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc34;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  goto loc27;
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
loc3:
 if (nondet_bool()) {
  v16 = 0;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  if (!( 0 <= v5 )) goto end;
  v16 = 0;
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v6 = 1+v6;
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 0 <= v10 )) goto end;
  v1 = v12;
  v5 = 1+v5;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= 0 )) goto end;
  v9 = 1;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v10 = nondet();
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v14 <= 10 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 11 <= v14 )) goto end;
  v14 = 10;
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v14 = nondet();
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v9 = 1;
  goto loc5;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v22 <= 1 )) goto end;
  if (!( 1 <= v22 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 2 <= v22 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1+v22 <= 1 )) goto end;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 4 <= v7 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 3 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( v7 <= 3 )) goto end;
  if (!( 3 <= v7 )) goto end;
  v22 = nondet();
  goto loc15;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( 0 <= v10 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= 0 )) goto end;
  v9 = 1;
  goto loc8;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  v10 = nondet();
  goto loc17;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v20 <= 0 )) goto end;
  if (!( 0 <= v20 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1 <= v20 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v20 <= 0 )) goto end;
  goto loc20;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v20 = nondet();
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( v21 <= 0 )) goto end;
  if (!( 0 <= v21 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1 <= v21 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v21 <= 0 )) goto end;
  goto loc22;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( v12 <= 0 )) goto end;
  if (!( 0 <= v12 )) goto end;
  v21 = nondet();
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1 <= v12 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= 0 )) goto end;
  goto loc24;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  goto loc29;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  if (!( 1+v13 <= v4 )) goto end;
  v12 = nondet();
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( v4 <= v13 )) goto end;
  goto loc5;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  v13 = 1+v13;
  goto loc26;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= -1 )) goto end;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( v1 <= -1 )) goto end;
  if (!( -1 <= v1 )) goto end;
  goto loc28;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( v4 <= v13 )) goto end;
  goto loc28;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v4 )) goto end;
  goto loc31;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc33:
 if (nondet_bool()) {
  if (!( v19 <= 0 )) goto end;
  if (!( 0 <= v19 )) goto end;
  goto loc26;
 }
 if (nondet_bool()) {
  if (!( 1 <= v19 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1+v19 <= 0 )) goto end;
  goto loc32;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  if (!( v18 <= 0 )) goto end;
  if (!( 0 <= v18 )) goto end;
  v19 = nondet();
  goto loc33;
 }
 if (nondet_bool()) {
  if (!( 1 <= v18 )) goto end;
  goto loc26;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  goto loc26;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v2 <= v6 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v2 )) goto end;
  v18 = nondet();
  goto loc35;
 }
 goto end;
loc36:
 if (nondet_bool()) {
  v17 = 0;
  goto loc37;
 }
 goto end;
loc38:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc36;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc36;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( 0 <= v8 )) goto end;
  v17 = 1;
  goto loc37;
 }
 goto end;
loc37:
 if (nondet_bool()) {
  v6 = v8;
  goto loc9;
 }
 goto end;
loc39:
 if (nondet_bool()) {
  v17 = 1;
  goto loc37;
 }
 goto end;
loc40:
 if (nondet_bool()) {
  if (!( v16 <= 0 )) goto end;
  if (!( 0 <= v16 )) goto end;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1 <= v16 )) goto end;
  goto loc39;
 }
 if (nondet_bool()) {
  if (!( 1+v16 <= 0 )) goto end;
  goto loc39;
 }
 goto end;
loc41:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc42:
 if (nondet_bool()) {
  goto loc43;
 }
 goto end;
loc43:
 if (nondet_bool()) {
  v16 = nondet();
  goto loc40;
 }
 goto end;
loc44:
 if (nondet_bool()) {
  if (!( 4 <= v11 )) goto end;
  goto loc42;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 3 )) goto end;
  goto loc42;
 }
 if (nondet_bool()) {
  if (!( v11 <= 3 )) goto end;
  if (!( 3 <= v11 )) goto end;
  goto loc43;
 }
 goto end;
loc45:
 if (nondet_bool()) {
  v15 = 1;
  v13 = 0;
  v5 = 0;
  v2 = nondet();
  v8 = nondet();
  if (!( 0 <= v8 )) goto end;
  v3 = nondet();
  if (!( 1 <= v3 )) goto end;
  v16 = nondet();
  goto loc44;
 }
 goto end;
loc1:
end:
;
}
