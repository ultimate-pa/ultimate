int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  if (!( v4 <= v2 )) goto end;
  if (!( v3 <= v5 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  v1 = 1;
  v5 = v3;
  v4 = v2;
  if (!( 1 <= v2 )) goto end;
  if (!( v3 <= 100 )) goto end;
  v3 = 11+v3;
  v2 = 1+v2;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  v1 = 1;
  v5 = v3;
  v4 = v2;
  if (!( 1 <= v2 )) goto end;
  if (!( 101 <= v3 )) goto end;
  v3 = -10+v3;
  v2 = -1+v2;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  if (!( v3 <= 100 )) goto end;
  v3 = 11+v3;
  v2 = 1+v2;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  if (!( 101 <= v3 )) goto end;
  v3 = -10+v3;
  v2 = -1+v2;
  goto loc_5;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v3 = nondet();
  v2 = 1;
  v1 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_1:
end:
;
}
