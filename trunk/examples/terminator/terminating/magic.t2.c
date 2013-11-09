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
goto loc57;
loc57:
 if (nondet_bool()) {
  goto loc56;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc35;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  goto loc20;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  goto loc34;
 }
 goto end;
loc37:
 if (nondet_bool()) {
  goto loc36;
 }
 goto end;
loc38:
 if (nondet_bool()) {
  goto loc39;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v19 = 0;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v3 = v19;
  v12 = 1+v12;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1+v7 <= v11 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v7 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v11 <= v7 )) goto end;
  if (!( v7 <= v11 )) goto end;
  v19 = 1;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v19 = 0;
  goto loc1;
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
loc7:
 if (nondet_bool()) {
  if (!( v5 <= v13 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v5 )) goto end;
  v11 = nondet();
  v13 = 1+v13;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  v13 = 0;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  v11 = 0;
  v13 = 0;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v18 = 0;
  goto loc12;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v3 = v18;
  v12 = 0;
  goto loc2;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1+v7 <= v10 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v7 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( v10 <= v7 )) goto end;
  if (!( v7 <= v10 )) goto end;
  v18 = 1;
  goto loc12;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v18 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc15;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  v10 = nondet();
  v12 = 1+v12;
  goto loc18;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  v17 = 0;
  goto loc22;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v3 = v17;
  v12 = 0;
  goto loc18;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( 1+v7 <= v9 )) goto end;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v7 )) goto end;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( v9 <= v7 )) goto end;
  if (!( v7 <= v9 )) goto end;
  v17 = 1;
  goto loc22;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v17 = 0;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc23;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  v9 = nondet();
  v12 = 1+v12;
  goto loc19;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v1 = v16;
  v13 = 1+v13;
  goto loc13;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  v16 = 1;
  goto loc25;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  goto loc26;
 }
 if (nondet_bool()) {
  v16 = 0;
  goto loc25;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v16 = 0;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc27;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc27;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v6 <= v13 )) goto end;
  v12 = 1+v12;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v6 )) goto end;
  goto loc28;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  v12 = 0;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  v13 = 1+v12;
  goto loc13;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  v2 = v15;
  v12 = 1+v12;
  goto loc30;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  v15 = 0;
  goto loc29;
 }
 if (nondet_bool()) {
  v15 = 1;
  goto loc29;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  v15 = 0;
  goto loc29;
 }
 if (nondet_bool()) {
  goto loc31;
 }
 goto end;
loc33:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v15 = 0;
  goto loc29;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc32;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  v12 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  goto loc33;
 }
 goto end;
loc36:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  v12 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  v12 = 1+v12;
  goto loc37;
 }
 goto end;
loc40:
 if (nondet_bool()) {
  goto loc41;
 }
 goto end;
loc42:
 if (nondet_bool()) {
  v22 = 0;
  goto loc40;
 }
 goto end;
loc43:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v22 = 1;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc42;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc42;
 }
 goto end;
loc44:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v22 = 1;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc43;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc43;
 }
 goto end;
loc45:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v22 = 1;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc44;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc44;
 }
 goto end;
loc46:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v22 = 1;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc45;
 }
 goto end;
loc47:
 if (nondet_bool()) {
  v4 = v21;
  goto loc46;
 }
 goto end;
loc48:
 if (nondet_bool()) {
  v21 = 1;
  goto loc47;
 }
 if (nondet_bool()) {
  v21 = 0;
  goto loc47;
 }
 goto end;
loc49:
 if (nondet_bool()) {
  goto loc48;
 }
 if (nondet_bool()) {
  v21 = 0;
  goto loc47;
 }
 goto end;
loc50:
 if (nondet_bool()) {
  goto loc49;
 }
 if (nondet_bool()) {
  v21 = 0;
  goto loc47;
 }
 goto end;
loc51:
 if (nondet_bool()) {
  goto loc50;
 }
 if (nondet_bool()) {
  v21 = 0;
  goto loc47;
 }
 goto end;
loc52:
 if (nondet_bool()) {
  v20 = 0;
  goto loc53;
 }
 goto end;
loc53:
 if (nondet_bool()) {
  v3 = v20;
  v13 = 1+v13;
  goto loc10;
 }
 goto end;
loc54:
 if (nondet_bool()) {
  if (!( 1+v7 <= v8 )) goto end;
  goto loc52;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v7 )) goto end;
  goto loc52;
 }
 if (nondet_bool()) {
  if (!( v8 <= v7 )) goto end;
  if (!( v7 <= v8 )) goto end;
  v20 = 1;
  goto loc53;
 }
 goto end;
loc55:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v20 = 0;
  goto loc53;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc54;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc54;
 }
 goto end;
loc39:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  goto loc55;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  v8 = nondet();
  v12 = 1+v12;
  goto loc38;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  if (!( v5 <= v13 )) goto end;
  goto loc51;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v5 )) goto end;
  v8 = 0;
  v12 = 0;
  goto loc38;
 }
 goto end;
loc56:
 if (nondet_bool()) {
  v5 = 4;
  v6 = nondet();
  v7 = nondet();
  v2 = 1;
  v1 = 1;
  v3 = 1;
  v4 = 0;
  v9 = 0;
  v10 = 0;
  v11 = 0;
  v8 = 0;
  v14 = nondet();
  v12 = 0;
  goto loc37;
 }
 goto end;
loc41:
end:
;
}
