extern void abort(void);

extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "assert.h", 3, __extension__ __PRETTY_FUNCTION__); })); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int __VERIFIER_nondet_int();
int main()
{
  int tagbuf_len;
  int t;
  tagbuf_len = __VERIFIER_nondet_int();
  if(tagbuf_len >= 1); else goto END;
  t = 0;
  --tagbuf_len;
  while (1) {
    if (t == tagbuf_len) {
      __VERIFIER_assert(0 <= t);
      __VERIFIER_assert(t <= tagbuf_len);
      goto END;
    }
    if (__VERIFIER_nondet_int()) {
      break;
    }
     __VERIFIER_assert(0 <= t);
     __VERIFIER_assert(t <= tagbuf_len);
    t++;
  }
   __VERIFIER_assert(0 <= t);
   __VERIFIER_assert(t <= tagbuf_len);
  t++;
  while (1) {
    if (t == tagbuf_len) {
      __VERIFIER_assert(0 <= t);
      __VERIFIER_assert(t <= tagbuf_len);
      goto END;
    }
    if (__VERIFIER_nondet_int()) {
      if ( __VERIFIER_nondet_int()) {
  __VERIFIER_assert(0 <= t);
 __VERIFIER_assert(t <= tagbuf_len);
        t++;
        if (t == tagbuf_len) {
   __VERIFIER_assert(0 <= t);
   __VERIFIER_assert(t <= tagbuf_len);
          goto END;
        }
      }
    }
    else if ( __VERIFIER_nondet_int()) {
      break;
    }
    __VERIFIER_assert(0 <= t);
    __VERIFIER_assert(t <= tagbuf_len);
    t++;
  }
  __VERIFIER_assert(0 <= t);
  __VERIFIER_assert(t <= tagbuf_len);
 END:
  return 0;
}
