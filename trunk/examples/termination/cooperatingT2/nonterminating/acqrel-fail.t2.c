int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_9;
loc_9:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  v1 = 1;
  v1 = 0;
  v4 = nondet();
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_CP_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  v4 = -1+v4;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  v2 = 1;
  v2 = 0;
  v3 = nondet();
  goto loc_CP_3;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v1 = 0;
  v2 = 0;
  v3 = nondet();
  goto loc_CP_3;
 }
 goto end;
loc_6:
end:
;
}
