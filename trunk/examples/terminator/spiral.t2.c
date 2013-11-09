int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = v1;
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( -1*v3 <= v4 )) goto end;
  if (!( 1+v3 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v3 <= v4 )) goto end;
  if (!( 1+v3 <= -1*v4 )) goto end;
  v4 = 1+v4;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1-v3 )) goto end;
  if (!( 1+v4 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v4 <= v3 )) goto end;
  if (!( 2-v4 <= v3 )) goto end;
  v4 = -1+v4;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v2;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
end:
;
}
