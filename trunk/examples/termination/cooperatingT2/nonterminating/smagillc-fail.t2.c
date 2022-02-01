int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 1+v3 <= v4 )) goto end;
  v4 = -2+v4;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v3 = -1+v3;
  v4 = -2+v4;
  v5 = 1+v5;
  goto loc_CP_0;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  v1 = nondet();
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  goto loc_CP_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = v2;
  if (!( 1 <= v3 )) goto end;
  v6 = 4;
  v5 = 0;
  v4 = v6;
  goto loc_CP_0;
 }
 goto end;
loc_3:
end:
;
}
