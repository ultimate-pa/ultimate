int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v2 <= v1 )) goto end;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  v5 = nondet();
  v1 = 1+v1;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_3;
 }
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = v4;
  v2 = v3;
  v1 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_6:
end:
;
}
