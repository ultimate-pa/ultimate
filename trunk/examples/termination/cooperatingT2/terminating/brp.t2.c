int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
goto loc_1;
loc_1:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
end:
;
}
