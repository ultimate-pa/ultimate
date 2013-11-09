int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
goto loc1;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
end:
;
}
