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
goto loc68;
loc68:
 if (nondet_bool()) {
  goto loc67;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = v20;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 10 <= v12 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= 10 )) goto end;
  v20 = 1;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v1 = v13;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 10 <= v10 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= 10 )) goto end;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 10 <= v9 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= 10 )) goto end;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 10 <= v7 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 10 )) goto end;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 10 <= v5 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 10 )) goto end;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 10 <= v8 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 10 )) goto end;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 10 <= v6 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 10 )) goto end;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 10 <= v11 )) goto end;
  v20 = 0;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 10 )) goto end;
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v1 = v19;
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v13 = 1;
  goto loc3;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v19 = 1;
  goto loc12;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v10 <= v12 )) goto end;
  if (!( v12 <= v10 )) goto end;
  v19 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v10 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v12 )) goto end;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v19 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc15;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v1 = v18;
  goto loc16;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v18 = 1;
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v9 <= v12 )) goto end;
  if (!( v12 <= v9 )) goto end;
  v18 = 0;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v9 )) goto end;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v12 )) goto end;
  goto loc18;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( v9 <= v10 )) goto end;
  if (!( v10 <= v9 )) goto end;
  v18 = 0;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc19;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v11 <= v12 )) goto end;
  if (!( v12 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v11 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v12 )) goto end;
  goto loc13;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v18 = 0;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc20;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  v1 = v17;
  goto loc22;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  v17 = 1;
  goto loc23;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( v7 <= v12 )) goto end;
  if (!( v12 <= v7 )) goto end;
  v17 = 0;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v7 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v12 )) goto end;
  goto loc24;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  if (!( v7 <= v10 )) goto end;
  if (!( v10 <= v7 )) goto end;
  v17 = 0;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v7 )) goto end;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v10 )) goto end;
  goto loc25;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( v7 <= v9 )) goto end;
  if (!( v9 <= v7 )) goto end;
  v17 = 0;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v7 )) goto end;
  goto loc26;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v9 )) goto end;
  goto loc26;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  if (!( v11 <= v10 )) goto end;
  if (!( v10 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v11 )) goto end;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v10 )) goto end;
  goto loc21;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v17 = 0;
  goto loc23;
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
loc30:
 if (nondet_bool()) {
  v1 = v16;
  goto loc29;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  v16 = 1;
  goto loc30;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  if (!( v5 <= v12 )) goto end;
  if (!( v12 <= v5 )) goto end;
  v16 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v5 )) goto end;
  goto loc31;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v12 )) goto end;
  goto loc31;
 }
 goto end;
loc33:
 if (nondet_bool()) {
  if (!( v5 <= v10 )) goto end;
  if (!( v10 <= v5 )) goto end;
  v16 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v5 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v10 )) goto end;
  goto loc32;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  if (!( v11 <= v9 )) goto end;
  if (!( v9 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v11 )) goto end;
  goto loc28;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v9 )) goto end;
  goto loc28;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  if (!( v5 <= v9 )) goto end;
  if (!( v9 <= v5 )) goto end;
  v16 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v5 )) goto end;
  goto loc33;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v9 )) goto end;
  goto loc33;
 }
 goto end;
loc36:
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  if (!( v7 <= v5 )) goto end;
  v16 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc35;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v7 )) goto end;
  goto loc35;
 }
 goto end;
loc37:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v16 = 0;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc36;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc36;
 }
 goto end;
loc38:
 if (nondet_bool()) {
  v1 = v15;
  goto loc37;
 }
 goto end;
loc39:
 if (nondet_bool()) {
  if (!( v11 <= v7 )) goto end;
  if (!( v7 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v11 )) goto end;
  goto loc34;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v7 )) goto end;
  goto loc34;
 }
 goto end;
loc40:
 if (nondet_bool()) {
  v15 = 1;
  goto loc38;
 }
 goto end;
loc41:
 if (nondet_bool()) {
  if (!( v8 <= v12 )) goto end;
  if (!( v12 <= v8 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v8 )) goto end;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v12 )) goto end;
  goto loc40;
 }
 goto end;
loc42:
 if (nondet_bool()) {
  if (!( v8 <= v10 )) goto end;
  if (!( v10 <= v8 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v8 )) goto end;
  goto loc41;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v10 )) goto end;
  goto loc41;
 }
 goto end;
loc43:
 if (nondet_bool()) {
  if (!( v8 <= v9 )) goto end;
  if (!( v9 <= v8 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v8 )) goto end;
  goto loc42;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v9 )) goto end;
  goto loc42;
 }
 goto end;
loc44:
 if (nondet_bool()) {
  if (!( v8 <= v7 )) goto end;
  if (!( v7 <= v8 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v8 )) goto end;
  goto loc43;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v7 )) goto end;
  goto loc43;
 }
 goto end;
loc45:
 if (nondet_bool()) {
  if (!( v8 <= v5 )) goto end;
  if (!( v5 <= v8 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v8 )) goto end;
  goto loc44;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  goto loc44;
 }
 goto end;
loc46:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v15 = 0;
  goto loc38;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc45;
 }
 goto end;
loc47:
 if (nondet_bool()) {
  if (!( v11 <= v5 )) goto end;
  if (!( v5 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v11 )) goto end;
  goto loc39;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v5 )) goto end;
  goto loc39;
 }
 goto end;
loc48:
 if (nondet_bool()) {
  v1 = v14;
  goto loc46;
 }
 goto end;
loc49:
 if (nondet_bool()) {
  v14 = 1;
  goto loc48;
 }
 goto end;
loc50:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  if (!( v12 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  goto loc49;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v12 )) goto end;
  goto loc49;
 }
 goto end;
loc51:
 if (nondet_bool()) {
  if (!( v6 <= v10 )) goto end;
  if (!( v10 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v6 )) goto end;
  goto loc50;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v10 )) goto end;
  goto loc50;
 }
 goto end;
loc52:
 if (nondet_bool()) {
  if (!( v6 <= v9 )) goto end;
  if (!( v9 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v6 )) goto end;
  goto loc51;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc51;
 }
 goto end;
loc53:
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  if (!( v7 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  goto loc52;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v7 )) goto end;
  goto loc52;
 }
 goto end;
loc54:
 if (nondet_bool()) {
  if (!( v11 <= v8 )) goto end;
  if (!( v8 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v11 )) goto end;
  goto loc47;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v8 )) goto end;
  goto loc47;
 }
 goto end;
loc55:
 if (nondet_bool()) {
  if (!( v6 <= v5 )) goto end;
  if (!( v5 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  goto loc53;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  goto loc53;
 }
 goto end;
loc56:
 if (nondet_bool()) {
  if (!( v6 <= v8 )) goto end;
  if (!( v8 <= v6 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v6 )) goto end;
  goto loc55;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v8 )) goto end;
  goto loc55;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v14 = 0;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc56;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc56;
 }
 goto end;
loc57:
 if (nondet_bool()) {
  goto loc58;
 }
 goto end;
loc59:
 if (nondet_bool()) {
  v22 = 0;
  goto loc57;
 }
 goto end;
loc60:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v22 = 1;
  goto loc57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc59;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc59;
 }
 goto end;
loc61:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v22 = 1;
  goto loc57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc60;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc60;
 }
 goto end;
loc62:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v22 = 1;
  goto loc57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc61;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc61;
 }
 goto end;
loc63:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v22 = 1;
  goto loc57;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc62;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc62;
 }
 goto end;
loc64:
 if (nondet_bool()) {
  v3 = v21;
  v4 = nondet();
  goto loc63;
 }
 goto end;
loc65:
 if (nondet_bool()) {
  v21 = 1;
  goto loc64;
 }
 goto end;
loc66:
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  if (!( 0 <= v11 )) goto end;
  v21 = 0;
  goto loc64;
 }
 if (nondet_bool()) {
  if (!( 1 <= v11 )) goto end;
  goto loc65;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 0 )) goto end;
  goto loc65;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  v21 = 0;
  goto loc64;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc66;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  goto loc66;
 }
 goto end;
loc67:
 if (nondet_bool()) {
  if (!( v11 <= v6 )) goto end;
  if (!( v6 <= v11 )) goto end;
  v13 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v11 )) goto end;
  goto loc54;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= v6 )) goto end;
  goto loc54;
 }
 goto end;
loc58:
end:
;
}
