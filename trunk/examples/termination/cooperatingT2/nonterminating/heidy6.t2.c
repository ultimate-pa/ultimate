int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  v2 = 1;
  goto loc_1;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  v1 = 0;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc_3;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  if (!( 2 <= 0 )) goto end;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_5;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_CP_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_6;
 }
 goto end;
end:
;
}
