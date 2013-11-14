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
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 if (nondet_bool()) {
  v6 = -1+v2;
  v1 = nondet();
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v6 <= v2 )) goto end;
  v4 = v1;
  v5 = v4;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v2 <= v6 )) goto end;
  v3 = nondet();
  goto loc_0;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v2 = 1+v3;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  v6 = -1+v3;
  goto loc_CP_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v7 = 8;
  v2 = 0;
  v6 = 14;
  v1 = -1;
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
