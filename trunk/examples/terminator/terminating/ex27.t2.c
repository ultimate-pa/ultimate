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
int v28 = nondet();
int v29 = nondet();
int v30 = nondet();
goto loc62;
loc62:
 if (nondet_bool()) {
  goto loc61;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  goto loc25;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  goto loc27;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  goto loc35;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v22 = v18;
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v22 <= 0 )) goto end;
  if (!( 0 <= v22 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v22 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v22 <= 0 )) goto end;
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v18 = 10;
  goto loc2;
 }
 if (nondet_bool()) {
  v18 = 0;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc4;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v7 = 50;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( v6 <= v1 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v6 )) goto end;
  v1 = 1+v1;
  goto loc12;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v1 = 0;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v26 = v12;
  goto loc15;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v26 <= 0 )) goto end;
  if (!( 0 <= v26 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v26 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v26 <= 0 )) goto end;
  goto loc13;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v12 = 10;
  goto loc14;
 }
 if (nondet_bool()) {
  v12 = 0;
  goto loc14;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  v21 = v17;
  goto loc21;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v21 <= 0 )) goto end;
  if (!( 0 <= v21 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v21 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v21 <= 0 )) goto end;
  goto loc19;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v17 = 10;
  goto loc20;
 }
 if (nondet_bool()) {
  v17 = 0;
  goto loc20;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc10;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v6 = 200;
  goto loc23;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v9 <= v4 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v9 )) goto end;
  v4 = 1+v4;
  goto loc17;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  v4 = 0;
  goto loc17;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  v30 = v11;
  goto loc30;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  if (!( v30 <= 0 )) goto end;
  if (!( 0 <= v30 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1 <= v30 )) goto end;
  goto loc28;
 }
 if (nondet_bool()) {
  if (!( 1+v30 <= 0 )) goto end;
  goto loc28;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  v11 = 10;
  goto loc29;
 }
 if (nondet_bool()) {
  v11 = 0;
  goto loc29;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  goto loc33;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  if (!( v10 <= v5 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v10 )) goto end;
  v5 = 1+v5;
  goto loc34;
 }
 goto end;
loc36:
 if (nondet_bool()) {
  goto loc31;
 }
 goto end;
loc37:
 if (nondet_bool()) {
  v5 = 0;
  goto loc34;
 }
 goto end;
loc38:
 if (nondet_bool()) {
  v29 = v15;
  goto loc39;
 }
 goto end;
loc39:
 if (nondet_bool()) {
  if (!( v29 <= 0 )) goto end;
  if (!( 0 <= v29 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1 <= v29 )) goto end;
  goto loc37;
 }
 if (nondet_bool()) {
  if (!( 1+v29 <= 0 )) goto end;
  goto loc37;
 }
 goto end;
loc40:
 if (nondet_bool()) {
  v15 = 10;
  goto loc38;
 }
 if (nondet_bool()) {
  v15 = 0;
  goto loc38;
 }
 goto end;
loc41:
 if (nondet_bool()) {
  v25 = v16;
  goto loc42;
 }
 goto end;
loc43:
 if (nondet_bool()) {
  goto loc40;
 }
 goto end;
loc44:
 if (nondet_bool()) {
  v24 = v20;
  goto loc45;
 }
 goto end;
loc45:
 if (nondet_bool()) {
  if (!( v24 <= 0 )) goto end;
  if (!( 0 <= v24 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1 <= v24 )) goto end;
  goto loc43;
 }
 if (nondet_bool()) {
  if (!( 1+v24 <= 0 )) goto end;
  goto loc43;
 }
 goto end;
loc46:
 if (nondet_bool()) {
  v20 = 10;
  goto loc44;
 }
 if (nondet_bool()) {
  v20 = 0;
  goto loc44;
 }
 goto end;
loc42:
 if (nondet_bool()) {
  if (!( v25 <= 0 )) goto end;
  if (!( 0 <= v25 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1 <= v25 )) goto end;
  goto loc36;
 }
 if (nondet_bool()) {
  if (!( 1+v25 <= 0 )) goto end;
  goto loc36;
 }
 goto end;
loc47:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  goto loc46;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc32;
 }
 goto end;
loc48:
 if (nondet_bool()) {
  v10 = 200;
  goto loc47;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( v8 <= v3 )) goto end;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v8 )) goto end;
  v3 = 1+v3;
  goto loc26;
 }
 goto end;
loc49:
 if (nondet_bool()) {
  v3 = 0;
  goto loc26;
 }
 goto end;
loc50:
 if (nondet_bool()) {
  v28 = v14;
  goto loc51;
 }
 goto end;
loc51:
 if (nondet_bool()) {
  if (!( v28 <= 0 )) goto end;
  if (!( 0 <= v28 )) goto end;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1 <= v28 )) goto end;
  goto loc49;
 }
 if (nondet_bool()) {
  if (!( 1+v28 <= 0 )) goto end;
  goto loc49;
 }
 goto end;
loc52:
 if (nondet_bool()) {
  v14 = 10;
  goto loc50;
 }
 if (nondet_bool()) {
  v14 = 0;
  goto loc50;
 }
 goto end;
loc53:
 if (nondet_bool()) {
  goto loc52;
 }
 goto end;
loc54:
 if (nondet_bool()) {
  v23 = v19;
  goto loc55;
 }
 goto end;
loc55:
 if (nondet_bool()) {
  if (!( v23 <= 0 )) goto end;
  if (!( 0 <= v23 )) goto end;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1 <= v23 )) goto end;
  goto loc53;
 }
 if (nondet_bool()) {
  if (!( 1+v23 <= 0 )) goto end;
  goto loc53;
 }
 goto end;
loc56:
 if (nondet_bool()) {
  v19 = 10;
  goto loc54;
 }
 if (nondet_bool()) {
  v19 = 0;
  goto loc54;
 }
 goto end;
loc57:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc56;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  goto loc48;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v8 = 20;
  goto loc57;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v16 = 10;
  goto loc41;
 }
 if (nondet_bool()) {
  v16 = 0;
  goto loc41;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( v7 <= v2 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v7 )) goto end;
  v2 = 1+v2;
  goto loc24;
 }
 goto end;
loc58:
 if (nondet_bool()) {
  v2 = 0;
  goto loc24;
 }
 goto end;
loc59:
 if (nondet_bool()) {
  v27 = v13;
  goto loc60;
 }
 goto end;
loc60:
 if (nondet_bool()) {
  if (!( v27 <= 0 )) goto end;
  if (!( 0 <= v27 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v27 )) goto end;
  goto loc58;
 }
 if (nondet_bool()) {
  if (!( 1+v27 <= 0 )) goto end;
  goto loc58;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v13 = 10;
  goto loc59;
 }
 if (nondet_bool()) {
  v13 = 0;
  goto loc59;
 }
 goto end;
loc61:
 if (nondet_bool()) {
  v9 = 100;
  goto loc6;
 }
 goto end;
loc33:
end:
;
}
