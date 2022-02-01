int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v4 = 2+v4;
  goto loc_1;
 }
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v3 = 0;
  goto loc_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 2+v1 <= v4 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 1+v1 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1+v1 )) goto end;
  if (!( 1+v1 <= v4 )) goto end;
  v3 = 1;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v1 <= v4 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v4 <= v1 )) goto end;
  if (!( v1 <= v4 )) goto end;
  v3 = 1;
  goto loc_6;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_4;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v4 = 0;
  v2 = 0;
  goto loc_CP_4;
 }
 goto end;
loc_8:
end:
;
}
