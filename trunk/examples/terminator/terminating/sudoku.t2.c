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
goto loc58;
loc58:
 if (nondet_bool()) {
  goto loc57;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  goto loc22;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  goto loc24;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  goto loc26;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  goto loc32;
 }
 goto end;
loc33:
 if (nondet_bool()) {
  goto loc36;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  goto loc35;
 }
 goto end;
loc37:
 if (nondet_bool()) {
  goto loc38;
 }
 goto end;
loc40:
 if (nondet_bool()) {
  goto loc42;
 }
 goto end;
loc41:
 if (nondet_bool()) {
  goto loc39;
 }
 goto end;
loc43:
 if (nondet_bool()) {
  goto loc44;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  v10 = 0;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = v21;
  v9 = 1+v9;
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v21 = 1;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 if (nondet_bool()) {
  v21 = 0;
  goto loc5;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v21 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( v6 <= v9 )) goto end;
  v8 = 1+v8;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v6 )) goto end;
  goto loc9;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( -1+v6 <= v8 )) goto end;
  v10 = 1+v10;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= -1+v6 )) goto end;
  v9 = 1+v8;
  goto loc6;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v6 <= v10 )) goto end;
  v7 = 0;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v6 )) goto end;
  v8 = 0;
  goto loc3;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v3 = v20;
  v12 = 1+v12;
  goto loc15;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v20 = 1;
  goto loc14;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  goto loc16;
 }
 if (nondet_bool()) {
  v20 = 0;
  goto loc14;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v20 = 0;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v6 <= v12 )) goto end;
  v11 = 1+v11;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= v6 )) goto end;
  goto loc18;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  if (!( -1+v6 <= v11 )) goto end;
  v7 = 1+v7;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= -1+v6 )) goto end;
  v12 = 1+v11;
  goto loc15;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  v10 = 0;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  v11 = 0;
  goto loc20;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  v2 = v19;
  v10 = 1+v10;
  goto loc28;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  v19 = 0;
  goto loc27;
 }
 if (nondet_bool()) {
  v19 = 1;
  goto loc27;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  v19 = 0;
  goto loc27;
 }
 if (nondet_bool()) {
  goto loc29;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v19 = 0;
  goto loc27;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc30;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc30;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  if (!( v6 <= v10 )) goto end;
  v7 = 1+v7;
  goto loc33;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v6 )) goto end;
  goto loc31;
 }
 goto end;
loc36:
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  v7 = 0;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  v10 = 0;
  goto loc28;
 }
 goto end;
loc39:
 if (nondet_bool()) {
  if (!( v6 <= v10 )) goto end;
  v7 = 1+v7;
  goto loc40;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v6 )) goto end;
  v18 = nondet();
  v10 = 1+v10;
  goto loc41;
 }
 goto end;
loc42:
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  v7 = 0;
  goto loc33;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  v10 = 0;
  goto loc41;
 }
 goto end;
loc45:
 if (nondet_bool()) {
  goto loc46;
 }
 goto end;
loc47:
 if (nondet_bool()) {
  v23 = 0;
  goto loc45;
 }
 goto end;
loc48:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v23 = 1;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc47;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc47;
 }
 goto end;
loc49:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v23 = 1;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc48;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc48;
 }
 goto end;
loc50:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v23 = 1;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc49;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc49;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v23 = 1;
  goto loc45;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc50;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc50;
 }
 goto end;
loc51:
 if (nondet_bool()) {
  v16 = 1+v16;
  goto loc43;
 }
 goto end;
loc52:
 if (nondet_bool()) {
  v4 = v22;
  goto loc51;
 }
 goto end;
loc53:
 if (nondet_bool()) {
  v22 = 1;
  goto loc52;
 }
 goto end;
loc54:
 if (nondet_bool()) {
  goto loc53;
 }
 if (nondet_bool()) {
  v22 = 0;
  goto loc52;
 }
 goto end;
loc55:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v22 = 0;
  goto loc52;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc54;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc54;
 }
 goto end;
loc56:
 if (nondet_bool()) {
  goto loc51;
 }
 if (nondet_bool()) {
  goto loc55;
 }
 goto end;
loc44:
 if (nondet_bool()) {
  if (!( v5 <= v16 )) goto end;
  v14 = 1+v14;
  goto loc37;
 }
 if (nondet_bool()) {
  if (!( 1+v16 <= v5 )) goto end;
  goto loc56;
 }
 goto end;
loc38:
 if (nondet_bool()) {
  if (!( v5 <= v14 )) goto end;
  v15 = 1+v15;
  goto loc34;
 }
 if (nondet_bool()) {
  if (!( 1+v14 <= v5 )) goto end;
  v16 = 0;
  goto loc43;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  if (!( v5 <= v15 )) goto end;
  v13 = 1+v13;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( 1+v15 <= v5 )) goto end;
  v14 = 0;
  goto loc37;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  if (!( v5 <= v13 )) goto end;
  v10 = 1+v10;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v5 )) goto end;
  v15 = 0;
  goto loc34;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v5 <= v10 )) goto end;
  v7 = 1+v7;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v5 )) goto end;
  v13 = 0;
  goto loc25;
 }
 goto end;
loc57:
 if (nondet_bool()) {
  v5 = 3;
  v6 = nondet();
  v2 = 1;
  v3 = 1;
  v1 = 1;
  v4 = 1;
  v17 = nondet();
  v7 = 0;
  goto loc40;
 }
 goto end;
loc46:
end:
;
}
