
typedef long unsigned int size_t;
typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;
typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;
typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;
typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;
typedef int __daddr_t;
typedef int __key_t;
typedef int __clockid_t;
typedef void * __timer_t;
typedef long int __blksize_t;
typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;
typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;
typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;
typedef long int __fsword_t;
typedef long int __ssize_t;
typedef long int __syscall_slong_t;
typedef unsigned long int __syscall_ulong_t;
typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;
typedef long int __intptr_t;
typedef unsigned int __socklen_t;
struct _IO_FILE;

typedef struct _IO_FILE FILE;


typedef struct _IO_FILE __FILE;
typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
typedef struct
{
  __off_t __pos;
  __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
  __off64_t __pos;
  __mbstate_t __state;
} _G_fpos64_t;
typedef __builtin_va_list __gnuc_va_list;
struct _IO_jump_t; struct _IO_FILE;
typedef void _IO_lock_t;
struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;
  int _pos;
};
enum __codecvt_result
{
  __codecvt_ok,
  __codecvt_partial,
  __codecvt_error,
  __codecvt_noconv
};
struct _IO_FILE {
  int _flags;
  char* _IO_read_ptr;
  char* _IO_read_end;
  char* _IO_read_base;
  char* _IO_write_base;
  char* _IO_write_ptr;
  char* _IO_write_end;
  char* _IO_buf_base;
  char* _IO_buf_end;
  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;
  struct _IO_marker *_markers;
  struct _IO_FILE *_chain;
  int _fileno;
  int _flags2;
  __off_t _old_offset;
  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];
  _IO_lock_t *_lock;
  __off64_t _offset;
  void *__pad1;
  void *__pad2;
  void *__pad3;
  void *__pad4;
  size_t __pad5;
  int _mode;
  char _unused2[15 * sizeof (int) - 4 * sizeof (void *) - sizeof (size_t)];
};
typedef struct _IO_FILE _IO_FILE;
struct _IO_FILE_plus;
extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);
typedef __ssize_t __io_write_fn (void *__cookie, const char *__buf,
     size_t __n);
typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);
typedef int __io_close_fn (void *__cookie);
extern int __underflow (_IO_FILE *);
extern int __uflow (_IO_FILE *);
extern int __overflow (_IO_FILE *, int);
extern int _IO_getc (_IO_FILE *__fp);
extern int _IO_putc (int __c, _IO_FILE *__fp);
extern int _IO_feof (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ferror (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_peekc_locked (_IO_FILE *__fp);
extern void _IO_flockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern void _IO_funlockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ftrylockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_vfscanf (_IO_FILE * __restrict, const char * __restrict,
   __gnuc_va_list, int *__restrict);
extern int _IO_vfprintf (_IO_FILE *__restrict, const char *__restrict,
    __gnuc_va_list);
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t);
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t);
extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int);
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int);
extern void _IO_free_backup_area (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
typedef __gnuc_va_list va_list;
typedef __off_t off_t;
typedef __ssize_t ssize_t;

typedef _G_fpos_t fpos_t;

extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;

extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));
extern int rename (const char *__old, const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern int renameat (int __oldfd, const char *__old, int __newfd,
       const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern FILE *tmpfile (void) ;
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;

extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tempnam (const char *__dir, const char *__pfx)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int fclose (FILE *__stream);
extern int fflush (FILE *__stream);

extern int fflush_unlocked (FILE *__stream);

extern FILE *fopen (const char *__restrict __filename,
      const char *__restrict __modes) ;
extern FILE *freopen (const char *__restrict __filename,
        const char *__restrict __modes,
        FILE *__restrict __stream) ;

extern FILE *fdopen (int __fd, const char *__modes) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *fmemopen (void *__s, size_t __len, const char *__modes)
  __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__));

extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
         size_t __size) __attribute__ ((__nothrow__ , __leaf__));
extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));

extern int fprintf (FILE *__restrict __stream,
      const char *__restrict __format, ...);
extern int printf (const char *__restrict __format, ...);
extern int sprintf (char *__restrict __s,
      const char *__restrict __format, ...) __attribute__ ((__nothrow__));
extern int vfprintf (FILE *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg);
extern int vprintf (const char *__restrict __format, __gnuc_va_list __arg);
extern int vsprintf (char *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nothrow__));


extern int snprintf (char *__restrict __s, size_t __maxlen,
       const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));
extern int vsnprintf (char *__restrict __s, size_t __maxlen,
        const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));

extern int vdprintf (int __fd, const char *__restrict __fmt,
       __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));

extern int fscanf (FILE *__restrict __stream,
     const char *__restrict __format, ...) ;
extern int scanf (const char *__restrict __format, ...) ;
extern int sscanf (const char *__restrict __s,
     const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf") ;
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf") ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__));


extern int vfscanf (FILE *__restrict __s, const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s,
      const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__format__ (__scanf__, 2, 0)));


extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);
extern int getchar (void);

extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
extern int fgetc_unlocked (FILE *__stream);

extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);
extern int putchar (int __c);

extern int fputc_unlocked (int __c, FILE *__stream);
extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);
extern int getw (FILE *__stream);
extern int putw (int __w, FILE *__stream);

extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     ;

extern __ssize_t __getdelim (char **__restrict __lineptr,
          size_t *__restrict __n, int __delimiter,
          FILE *__restrict __stream) ;
extern __ssize_t getdelim (char **__restrict __lineptr,
        size_t *__restrict __n, int __delimiter,
        FILE *__restrict __stream) ;
extern __ssize_t getline (char **__restrict __lineptr,
       size_t *__restrict __n,
       FILE *__restrict __stream) ;

extern int fputs (const char *__restrict __s, FILE *__restrict __stream);
extern int puts (const char *__s);
extern int ungetc (int __c, FILE *__stream);
extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite (const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s);

extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
         size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite_unlocked (const void *__restrict __ptr, size_t __size,
          size_t __n, FILE *__restrict __stream);

extern int fseek (FILE *__stream, long int __off, int __whence);
extern long int ftell (FILE *__stream) ;
extern void rewind (FILE *__stream);

extern int fseeko (FILE *__stream, __off_t __off, int __whence);
extern __off_t ftello (FILE *__stream) ;

extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos);
extern int fsetpos (FILE *__stream, const fpos_t *__pos);


extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void perror (const char *__s);

extern int sys_nerr;
extern const char *const sys_errlist[];
extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *popen (const char *__command, const char *__modes) ;
extern int pclose (FILE *__stream);
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));


extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


typedef float float_t;
typedef double double_t;

extern double acos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __acos (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double asin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __asin (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern double cos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cos (double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern double sin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sin (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double tan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tan (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double cosh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cosh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double sinh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sinh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double tanh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tanh (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double acosh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __acosh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double asinh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __asinh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atanh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atanh (double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double exp (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __exp (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern double ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern double log (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log10 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log10 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern double __modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern double expm1 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __expm1 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log1p (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log1p (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double logb (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __logb (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double exp2 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __exp2 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log2 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log2 (double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double hypot (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __hypot (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));


extern double cbrt (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cbrt (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double ceil (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __ceil (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fabs (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fabs (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double floor (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __floor (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinf (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finite (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinf (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finite (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double drem (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __drem (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double significand (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __significand (double __x) __attribute__ ((__nothrow__ , __leaf__));

extern double copysign (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __copysign (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern double nan (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nan (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnan (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnan (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double j0 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __j0 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double j1 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __j1 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double jn (int, double) __attribute__ ((__nothrow__ , __leaf__)); extern double __jn (int, double) __attribute__ ((__nothrow__ , __leaf__));
extern double y0 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __y0 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double y1 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __y1 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double yn (int, double) __attribute__ ((__nothrow__ , __leaf__)); extern double __yn (int, double) __attribute__ ((__nothrow__ , __leaf__));

extern double erf (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __erf (double) __attribute__ ((__nothrow__ , __leaf__));
extern double erfc (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __erfc (double) __attribute__ ((__nothrow__ , __leaf__));
extern double lgamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __lgamma (double) __attribute__ ((__nothrow__ , __leaf__));


extern double tgamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __tgamma (double) __attribute__ ((__nothrow__ , __leaf__));

extern double gamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __gamma (double) __attribute__ ((__nothrow__ , __leaf__));
extern double lgamma_r (double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern double __lgamma_r (double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern double rint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __rint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double nextafter (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nextafter (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double nexttoward (double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nexttoward (double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double remainder (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __remainder (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double scalbn (double __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalbn (double __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogb (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogb (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double scalbln (double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalbln (double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern double nearbyint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __nearbyint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double round (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __round (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double trunc (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __trunc (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double remquo (double __x, double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern double __remquo (double __x, double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrint (double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lround (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lround (double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llround (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llround (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double fdim (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __fdim (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double fmax (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fmax (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fmin (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fmin (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassify (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbit (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern double fma (double __x, double __y, double __z) __attribute__ ((__nothrow__ , __leaf__)); extern double __fma (double __x, double __y, double __z) __attribute__ ((__nothrow__ , __leaf__));

extern double scalb (double __x, double __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalb (double __x, double __n) __attribute__ ((__nothrow__ , __leaf__));

extern float acosf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __acosf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float asinf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __asinf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atanf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atanf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atan2f (float __y, float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atan2f (float __y, float __x) __attribute__ ((__nothrow__ , __leaf__));
 extern float cosf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __cosf (float __x) __attribute__ ((__nothrow__ , __leaf__));
 extern float sinf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sinf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float tanf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __tanf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float coshf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __coshf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float sinhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sinhf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float tanhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __tanhf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float acoshf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __acoshf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float asinhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __asinhf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atanhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atanhf (float __x) __attribute__ ((__nothrow__ , __leaf__));


 extern float expf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __expf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float frexpf (float __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern float __frexpf (float __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern float ldexpf (float __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern float __ldexpf (float __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern float logf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __logf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log10f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log10f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float modff (float __x, float *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern float __modff (float __x, float *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern float expm1f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __expm1f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log1pf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log1pf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float logbf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __logbf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float exp2f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __exp2f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log2f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log2f (float __x) __attribute__ ((__nothrow__ , __leaf__));


 extern float powf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __powf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float sqrtf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sqrtf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float hypotf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __hypotf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));


extern float cbrtf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __cbrtf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float ceilf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __ceilf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fabsf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fabsf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float floorf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __floorf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fmodf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __fmodf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinff (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finitef (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinff (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finitef (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float dremf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __dremf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float significandf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __significandf (float __x) __attribute__ ((__nothrow__ , __leaf__));

extern float copysignf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __copysignf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern float nanf (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nanf (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnanf (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnanf (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float j0f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __j0f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float j1f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __j1f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float jnf (int, float) __attribute__ ((__nothrow__ , __leaf__)); extern float __jnf (int, float) __attribute__ ((__nothrow__ , __leaf__));
extern float y0f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __y0f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float y1f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __y1f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float ynf (int, float) __attribute__ ((__nothrow__ , __leaf__)); extern float __ynf (int, float) __attribute__ ((__nothrow__ , __leaf__));

extern float erff (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __erff (float) __attribute__ ((__nothrow__ , __leaf__));
extern float erfcf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __erfcf (float) __attribute__ ((__nothrow__ , __leaf__));
extern float lgammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __lgammaf (float) __attribute__ ((__nothrow__ , __leaf__));


extern float tgammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __tgammaf (float) __attribute__ ((__nothrow__ , __leaf__));

extern float gammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __gammaf (float) __attribute__ ((__nothrow__ , __leaf__));
extern float lgammaf_r (float, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern float __lgammaf_r (float, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern float rintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __rintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float nextafterf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nextafterf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float nexttowardf (float __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nexttowardf (float __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float remainderf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __remainderf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float scalbnf (float __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalbnf (float __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogbf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogbf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float scalblnf (float __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalblnf (float __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern float nearbyintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __nearbyintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float roundf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __roundf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float truncf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __truncf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float remquof (float __x, float __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern float __remquof (float __x, float __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lroundf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lroundf (float __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llroundf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llroundf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float fdimf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __fdimf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float fmaxf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fmaxf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fminf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fminf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassifyf (float __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbitf (float __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern float fmaf (float __x, float __y, float __z) __attribute__ ((__nothrow__ , __leaf__)); extern float __fmaf (float __x, float __y, float __z) __attribute__ ((__nothrow__ , __leaf__));

extern float scalbf (float __x, float __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalbf (float __x, float __n) __attribute__ ((__nothrow__ , __leaf__));

extern long double acosl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __acosl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double asinl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __asinl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atanl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atanl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atan2l (long double __y, long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atan2l (long double __y, long double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern long double cosl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __cosl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern long double sinl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sinl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double tanl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tanl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double coshl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __coshl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double sinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double tanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double acoshl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __acoshl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double asinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __asinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern long double expl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __expl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double frexpl (long double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern long double __frexpl (long double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern long double ldexpl (long double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern long double __ldexpl (long double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern long double logl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __logl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log10l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log10l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double modfl (long double __x, long double *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern long double __modfl (long double __x, long double *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern long double expm1l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __expm1l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log1pl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log1pl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double logbl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __logbl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double exp2l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __exp2l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log2l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log2l (long double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern long double powl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __powl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double sqrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sqrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double hypotl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __hypotl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));


extern long double cbrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __cbrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double ceill (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __ceill (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fabsl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fabsl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double floorl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __floorl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fmodl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fmodl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinfl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finitel (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinfl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finitel (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double dreml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __dreml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double significandl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __significandl (long double __x) __attribute__ ((__nothrow__ , __leaf__));

extern long double copysignl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __copysignl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern long double nanl (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nanl (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnanl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnanl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double j0l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __j0l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double j1l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __j1l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double jnl (int, long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __jnl (int, long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double y0l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __y0l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double y1l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __y1l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double ynl (int, long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __ynl (int, long double) __attribute__ ((__nothrow__ , __leaf__));

extern long double erfl (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __erfl (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double erfcl (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __erfcl (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double lgammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __lgammal (long double) __attribute__ ((__nothrow__ , __leaf__));


extern long double tgammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tgammal (long double) __attribute__ ((__nothrow__ , __leaf__));

extern long double gammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __gammal (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double lgammal_r (long double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern long double __lgammal_r (long double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern long double rintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __rintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double nextafterl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nextafterl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double nexttowardl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nexttowardl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double remainderl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __remainderl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double scalbnl (long double __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalbnl (long double __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogbl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogbl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double scalblnl (long double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalblnl (long double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern long double nearbyintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __nearbyintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double roundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __roundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double truncl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __truncl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double remquol (long double __x, long double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern long double __remquol (long double __x, long double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double fdiml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fdiml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double fmaxl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fmaxl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fminl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fminl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassifyl (long double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbitl (long double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern long double fmal (long double __x, long double __y, long double __z) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fmal (long double __x, long double __y, long double __z) __attribute__ ((__nothrow__ , __leaf__));

extern long double scalbl (long double __x, long double __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalbl (long double __x, long double __n) __attribute__ ((__nothrow__ , __leaf__));
extern int signgam;
enum
  {
    FP_NAN =
      0,
    FP_INFINITE =
      1,
    FP_ZERO =
      2,
    FP_SUBNORMAL =
      3,
    FP_NORMAL =
      4
  };
typedef enum
{
  _IEEE_ = -1,
  _SVID_,
  _XOPEN_,
  _POSIX_,
  _ISOC_
} _LIB_VERSION_TYPE;
extern _LIB_VERSION_TYPE _LIB_VERSION;
struct exception
  {
    int type;
    char *name;
    double arg1;
    double arg2;
    double retval;
  };
extern int matherr (struct exception *__exc);

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
  int a4 = -89;
  int a29 = -127;
  int a2 = 1;
  int a0 = -44;
 int calculate_output(int input) {
 if(((((a2==1) && a4 <= -86 ) && a0 <= -147 ) && ((-144 < a29) && (-16 >= a29)) )){
  error_0: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && a0 <= -147 ) && ((-16 < a29) && (43 >= a29)) )){
  error_9: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && a0 <= -147 ) && 43 < a29 )){
  error_18: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && a29 <= -144 )){
  error_47: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && a0 <= -147 ) && a29 <= -144 )){
  error_7: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && a29 <= -144 )){
  error_39: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && 43 < a29 )){
  error_50: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && 43 < a29 )){
  error_34: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && 43 < a29 )){
  error_30: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && a0 <= -147 ) && 43 < a29 )){
  error_14: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && a29 <= -144 )){
  error_51: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )){
  error_23: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && 43 < a29 )){
  error_22: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && a0 <= -147 ) && a29 <= -144 )){
  error_15: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_37: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_29: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_33: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && a0 <= -147 ) && a29 <= -144 )){
  error_3: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_25: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_41: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_40: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_48: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && a0 <= -147 ) && 43 < a29 )){
  error_2: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_45: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && 43 < a29 )){
  error_38: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && a0 <= -147 ) && ((-144 < a29) && (-16 >= a29)) )){
  error_4: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_28: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_56: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && a0 <= -147 ) && 43 < a29 )){
  error_10: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && a0 <= -147 ) && a29 <= -144 )){
  globalError: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )){
  error_35: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )){
  error_27: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_24: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_52: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && 43 < a29 )){
  error_54: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_57: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_20: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && 43 < a29 )){
  error_46: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && a0 <= -147 ) && ((-16 < a29) && (43 >= a29)) )){
  error_1: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )){
  error_19: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && 43 < a29 )){
  error_42: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_53: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && a0 <= -147 ) && ((-16 < a29) && (43 >= a29)) )){
  error_13: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_32: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && 43 < a29 )){
  error_58: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && a0 <= -147 ) && ((-144 < a29) && (-16 >= a29)) )){
  error_8: __VERIFIER_assume(0);
  }
  if(((((a2==3) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_49: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && 43 < a29 )){
  error_26: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && -61 < a0 ) && a29 <= -144 )){
  error_59: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && a0 <= -147 ) && a29 <= -144 )){
  error_11: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && a0 <= -147 ) && 43 < a29 )){
  error_6: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && a29 <= -144 )){
  error_55: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && a29 <= -144 )){
  error_43: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && a0 <= -147 ) && ((-144 < a29) && (-16 >= a29)) )){
  error_12: __VERIFIER_assume(0);
  }
  if(((((a2==1) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-16 < a29) && (43 >= a29)) )){
  error_21: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_36: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && a0 <= -147 ) && ((-144 < a29) && (-16 >= a29)) )){
  error_16: __VERIFIER_assume(0);
  }
  if(((((a2==5) && a4 <= -86 ) && a0 <= -147 ) && ((-16 < a29) && (43 >= a29)) )){
  error_17: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && a0 <= -147 ) && ((-16 < a29) && (43 >= a29)) )){
  error_5: __VERIFIER_assume(0);
  }
  if(((((a2==4) && a4 <= -86 ) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )){
  error_31: __VERIFIER_assume(0);
  }
  if(((((a2==2) && a4 <= -86 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
  error_44: __VERIFIER_assume(0);
  }
     if(( -61 < a0 && ( a4 <= -86 && ((input == 1) && (((a2==3) && a29 <= -144 ) || (((a2==2) && ((-16 < a29) && (43 >= a29)) ) || ( 43 < a29 && (a2==2)))))))){
      a0 = (((((a0 % 299926)+ -300072) / 5) * 5) - 2);
      a29 = (((a29 / 5) - 403019) / 5);
       a2 = 1;
       return -1;
     } else if(((( ((-86 < a4) && (-42 >= a4)) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 4))) && (a2==1)) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = ((((a4 * 10)/ 4) - 105635) * 5);
      a0 = (((a0 / 5) + -535974) * 1);
      a29 = ((((a29 % 299928)+ -144) + -127007) * 1);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((a2==2) && ( a29 <= -144 && (input == 3))) && ((-98 < a0) && (-61 >= a0)) ))){
      if( a0 <= -147 ){
      a4 = (((a4 / 5) + 230984) + -520005);
      a0 = (((a0 * 5) - 170894) / -5);
      a29 = ((((a29 % 29)+ 13) / 5) / 5);
       a2 = 3;
      } else{
       a29 = ((((a29 - 0) % 29)+ 23) + -9);
      } return 21;
     } else if((( a0 <= -147 && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 2)) && (a2==1))) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 - 373993) - 156849) + 1087366) + -662739);
      a0 = (((((a0 * 9)/ 10) + -38819) % 24)+ -99);
      a29 = ((((((a29 % 299978)+ 300021) / 5) - 494390) * -1)/ 10);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 3)) && ((-98 < a0) && (-61 >= a0)) ) && (a2==4)))){
      a4 = (((a4 + -343035) + 587291) - 275194);
      a0 = (((a0 + 390619) - 403210) - -569718);
      a29 = (((((a29 % 299978)- -300021) - -1) / 5) + 444143);
       a2 = 2;
       return 22;
     } else if(((((a2==3) && ((input == 3) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ))) && -61 < a0 ) && a4 <= -86 )){
      a0 = ((((a0 % 299926)- 300072) * 1) - 1);
      a29 = (((a29 - 382960) - 74074) * 1);
       a2 = 1;
       return -1;
     } else if(((((input == 5) && (( ((-144 < a29) && (-16 >= a29)) && (a2==2)) || (( 43 < a29 && (a2==1)) || ((a2==2) && a29 <= -144 )))) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = (((((a4 * 10)/ 4) * 10)/ 9) + -71483);
      a29 = (((((a29 % 299928)- 300071) + -1) / 5) - 280609);
       a2 = 1;
       return -1;
     } else if(((((( ((-144 < a29) && (-16 >= a29)) && (a2==4)) || (( 43 < a29 && (a2==3)) || ((a2==4) && a29 <= -144 ))) && (input == 2)) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = (((((a4 + -149009) - -316415) * 3) * -1)/ 10);
      a0 = ((((a0 - 0) % 24)- 121) + -1);
      a29 = ((((a29 % 299978)- -300021) / 5) - -378565);
       a2 = 3;
       return -1;
     } else if((( -61 < a0 && ((((a2==3) && a29 <= -144 ) || (( ((-16 < a29) && (43 >= a29)) && (a2==2)) || ( 43 < a29 && (a2==2)))) && (input == 2))) && a4 <= -86 )){
      a0 = ((((a0 / 5) - -215080) * 10)/ -9);
      a29 = ((((((a29 - 0) * 9)/ 10) + -50638) % 299928)- 300071);
       a2 = 1;
       return -1;
     } else if(((((a2==4) && ((input == 1) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = (((a4 * 5) + -228988) / 5);
      a0 = ((((((a0 % 18)+ -78) * 9)/ 10) * 9)/ 10);
      a29 = ((((((a29 * 9)/ 10) / 5) + 262161) % 29)- -15);
       a2 = 1;
       return -1;
     } else if((((((input == 4) && 43 < a29 ) && (a2==1)) && ((-98 < a0) && (-61 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) )){
      a29 = ((((a29 % 29)- -15) / 5) + -16);
       a2 = 5;
       return -1;
     } else if((( -61 < a0 && (((( 43 < a29 && (a2==4)) || ((a2==5) && a29 <= -144 )) || ( ((-144 < a29) && (-16 >= a29)) && (a2==5))) && (input == 1))) && a4 <= -86 )){
      a4 = ((((a4 - 0) - -490407) % 21)+ -62);
      a0 = ((((a0 - 153310) * 1) % 299926)- 300072);
      a29 = ((((a29 % 299978)+ 300021) + 1) - 0);
       a2 = 4;
       return 22;
     } else if((( ((-147 < a0) && (-98 >= a0)) && (((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) )) && (a2==3))){
      a4 = (((a4 + -155747) - 133657) - 35383);
      a0 = ((((a0 / 5) + 135798) * 4) - 984812);
      a29 = (((a29 + -315762) / 5) + -109484);
       a2 = 1;
       return -1;
     } else if((((a2==2) && (((input == 5) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) )) && ((-16 < a29) && (43 >= a29)) )){
      a4 = ((((((a4 * 21)/ 10) + 71298) / 5) * -1)/ 10);
      a0 = (((a0 - 162900) - 383694) - 31566);
      a29 = (((a29 / 5) - -341315) + 150076);
       a2 = 5;
       return -1;
     } else if((((((input == 5) && ( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && (a2==1)) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((a4 + -44548) - -443306) + -696410);
      a0 = ((((a0 / 5) * 123)/ 10) - 36241);
      a29 = ((((a29 - 0) * 9)/ 10) + 573486);
       a2 = 5;
       return -1;
     } else if(((a2==4) && ( -61 < a0 && ( a4 <= -86 && ((input == 5) && ( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))))))){
      if( 43 < a29 ){
      a4 = (((((a4 / 5) % 21)+ -60) * 9)/ 10);
      a0 = ((((a0 % 24)- 121) + -205117) - -205116);
      a29 = ((((a29 % 29)+ 14) / 5) + 22);
       a2 = 2;
      } else{
       a4 = ((((a4 % 21)+ -46) * 1) + -5);
       a0 = ((((a0 + 0) % 299926)+ -300072) * 1);
       a29 = ((((a29 + 371124) % 29)- -13) + 2);
       a2 = 3;
      } return 22;
     } else if((((((input == 3) && -61 < a0 ) && a4 <= -86 ) && ((-16 < a29) && (43 >= a29)) ) && (a2==5))){
      a4 = (((((a4 - -446919) % 21)+ -64) / 5) + -48);
      a0 = (((((a0 - 0) % 24)- 122) - 24975) - -24975);
      a29 = ((((a29 - -264394) + -320129) - 442766) - -778920);
       a2 = 2;
       return 22;
     } else if(((a2==1) && ( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && ((input == 4) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))))){
      a4 = (((a4 - 226504) - 71806) * 2);
      a29 = ((((a29 % 299928)- 144) - 38153) + -135408);
       a2 = 5;
       return -1;
     } else if((( -61 < a0 && ( 43 < a29 && ((input == 4) && (a2==5)))) && a4 <= -86 )){
       return 22;
     } else if(((((((a2==4) && ((-144 < a29) && (-16 >= a29)) ) || (((a2==3) && 43 < a29 ) || ( a29 <= -144 && (a2==4)))) && (input == 5)) && a0 <= -147 ) && ((-86 < a4) && (-42 >= a4)) )){
      a29 = ((((a29 % 299928)+ -300071) * 1) - 2);
       a2 = 3;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 3) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )) && a0 <= -147 )) && (a2==3))){
      if( ((-16 < a29) && (43 >= a29)) ){
      a0 = ((((a0 + 125283) % 24)- 122) + 1);
      a29 = (((((a29 / 5) - -520121) * 1) % 29)- -2);
       a2 = 2;
      } else{
       a29 = (((((a29 * 9)/ 10) + 5268) % 63)+ -79);
      } return -1;
     } else if(( 43 < a29 && (( -61 < a0 && ( a4 <= -86 && (input == 1))) && (a2==5)))){
      a29 = ((((a29 + -556242) % 299928)- 300071) * 1);
       a2 = 2;
       return 26;
     } else if((( a4 <= -86 && ( 43 < a29 && ((input == 2) && -61 < a0 ))) && (a2==3))){
      a0 = (((a0 / 5) / 5) + -266659);
      a29 = ((((a29 - 118281) + 14305) % 299928)- 300071);
       a2 = 1;
       return -1;
     } else if(((((input == 6) && ((((a2==1) && 43 < a29 ) || ( a29 <= -144 && (a2==2))) || ((a2==2) && ((-144 < a29) && (-16 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = (((a4 / 5) - 468667) / 5);
      a29 = ((((((a29 * 9)/ 10) % 299928)+ -300071) + 121344) + -121344);
       a2 = 1;
       return -1;
     } else if((((( ((-98 < a0) && (-61 >= a0)) && (input == 3)) && (a2==2)) && ((-86 < a4) && (-42 >= a4)) ) && 43 < a29 )){
      a4 = (((a4 - 174071) * 3) / 5);
      a29 = ((((((a29 * 9)/ 10) * 1) + -195948) % 29)- -14);
       a2 = 3;
       return -1;
     } else if(((( ((-147 < a0) && (-98 >= a0)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 5))) && (a2==4)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 * 5) + 579823) + 11517) + -660876);
      a0 = (((a0 * 5) - 6100) * 5);
      a29 = (((a29 / 5) + 176253) - -181921);
       a2 = 5;
       return -1;
     } else if(((( a4 <= -86 && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 1))) && (a2==1)) && -61 < a0 )){
      a0 = ((((a0 - 217743) % 299926)+ -300072) * 1);
      a29 = (((a29 + -396156) + -5222) * 1);
       return -1;
     } else if(( -61 < a0 && ((( 43 < a29 && (input == 6)) && (a2==5)) && a4 <= -86 ))){
      a0 = (((((a0 % 18)- 78) * 1) / 5) + -63);
      a29 = ((((a29 % 63)- 97) - 20) + 4);
       a2 = 3;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-98 < a0) && (-61 >= a0)) && (((input == 3) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (a2==5))))){
      if((a2==4)){
      a4 = (((a4 - 95607) + -173954) + -12748);
      a0 = ((((a0 * 25)/ 10) + -439586) - -307849);
      a29 = ((((a29 % 299928)+ -144) - 72109) - 18545);
       a2 = 4;
      } else{
       a4 = (((a4 + -172293) / 5) * 5);
       a29 = ((((a29 + 0) * 9)/ 10) - -585169);
       a2 = 4;
      } return 22;
     } else if((( ((-98 < a0) && (-61 >= a0)) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 5)) && ((-86 < a4) && (-42 >= a4)) )) && (a2==4))){
      a4 = (((a4 * 5) - -527193) + -830547);
      a0 = (((a0 / 5) - 111795) * 5);
      a29 = (((((a29 % 299928)- 300071) + 0) - -381711) + -381711);
       return -1;
     } else if(( a4 <= -86 && ( -61 < a0 && (((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 4)) && (a2==4))))){
      a4 = (((((a4 / 5) % 21)- 43) + 72580) - 72601);
      a0 = ((((a0 % 299926)- 300072) + 505424) - 505425);
      a29 = ((((a29 * 9)/ 10) + 571994) / 5);
       a2 = 2;
       return 26;
     } else if((((((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) || 43 < a29 ) && (input == 6)) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) ) && (a2==5))){
      a4 = ((((a4 + -159160) / 5) * 10)/ 9);
      a0 = (((a0 / 5) + -450837) * 1);
      a29 = (((((a29 % 299928)- 300071) - 1) / 5) + -101068);
       a2 = 2;
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ((a2==3) && (((input == 2) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) )))){
      a4 = (((a4 + -31484) + -538040) + -21692);
      a29 = ((((a29 % 299928)+ -144) + -155078) * 1);
       a2 = 4;
       return 21;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 5) && ((-147 < a0) && (-98 >= a0)) ) && a29 <= -144 )) && (a2==5))){
      a4 = (((a4 - 159432) - 109407) * 2);
      a0 = ((((a0 + 490072) + 32090) * 10)/ 9);
      a29 = ((((((a29 % 29)+ 23) + 1) * 5) % 29)- -13);
       return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && ((a2==3) && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 2)))))){
      a0 = ((((a0 / 5) * 4) - -113559) + -665939);
      a29 = (((a29 - 148272) + 252167) + -411458);
       a2 = 1;
       return -1;
     } else if(((((a2==3) && (( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (input == 2))) && a0 <= -147 ) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((a4 + -287863) + -192250) * 1);
      a29 = ((((a29 / 5) % 63)+ -80) - 1);
       a2 = 1;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 5)) && (a2==5)) && ((-98 < a0) && (-61 >= a0)) ))){
      a0 = (((a0 - 45) / 5) + -99);
      a29 = ((((a29 % 299928)+ -300071) / 5) + -203345);
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 1) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-147 < a0) && (-98 >= a0)) )) && (a2==4))){
      a4 = (((((a4 * 21)/ 10) - 87347) * 10)/ 9);
      a0 = (((((a0 % 18)+ -61) - 19) / 5) + -77);
      a29 = (((a29 / 5) * 4) - 587483);
       a2 = 3;
       return -1;
     } else if(((((((a2==5) && ((-144 < a29) && (-16 >= a29)) ) || (( 43 < a29 && (a2==4)) || ((a2==5) && a29 <= -144 ))) && (input == 2)) && a4 <= -86 ) && -61 < a0 )){
      a0 = ((((a0 + -267162) % 299926)- 300072) * 1);
      a29 = (((a29 + 0) / 5) - 428483);
       a2 = 1;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (( ((-98 < a0) && (-61 >= a0)) && (input == 6)) && (a2==2))) && a29 <= -144 )){
      a4 = ((((a4 + -196449) - -594193) * 10)/ -9);
      a0 = ((((a0 / 5) / 5) * 735)/ 10);
       a2 = 1;
       return -1;
     } else if(( ((-16 < a29) && (43 >= a29)) && ( a4 <= -86 && (((input == 6) && -61 < a0 ) && (a2==5))))){
      a0 = (((a0 / 5) + -324699) - 172683);
      a29 = (((((a29 - 531416) + -35692) - -697447) * -1)/ 10);
       a2 = 1;
       return -1;
     } else if((( ((-16 < a29) && (43 >= a29)) && (((input == 4) && -61 < a0 ) && a4 <= -86 )) && (a2==5))){
      a4 = ((((a4 / 5) - -571961) % 21)+ -67);
      a0 = ((((a0 % 299926)+ -300072) * 1) - 2);
      a29 = ((((a29 - -174449) * 10)/ 9) / 5);
       return 22;
     } else if(( -61 < a0 && ( a4 <= -86 && ((input == 5) && ((( ((-16 < a29) && (43 >= a29)) && (a2==2)) || ((a2==2) && 43 < a29 )) || ( a29 <= -144 && (a2==3))))))){
      a4 = (((((a4 % 21)+ -47) + 367614) + 116418) + -484038);
      a0 = ((((a0 / 5) / 5) % 24)+ -122);
      a29 = (((a29 / 5) + 298882) - 164223);
       a2 = 3;
       return 21;
     } else if((( ((-98 < a0) && (-61 >= a0)) && (((input == 1) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) )) && (a2==2))){
      a29 = (((((a29 % 63)- 79) * 1) + -90558) + 90558);
       a2 = 5;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-98 < a0) && (-61 >= a0)) && (((input == 6) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) )) && (a2==2))))){
      a0 = (((((a0 - 46) * 5) * 5) % 24)+ -121);
      a29 = ((((a29 - -1321) - 315533) * -1)/ 10);
       a2 = 3;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-147 < a0) && (-98 >= a0)) && ((input == 3) && ((( ((-16 < a29) && (43 >= a29)) && (a2==1)) || ( 43 < a29 && (a2==1))) || ((a2==2) && a29 <= -144 )))))){
      a29 = (((((a29 * 9)/ 10) - -17657) / 5) - 139328);
       a2 = 1;
       return 21;
     } else if(((( a0 <= -147 && ((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && (a2==4)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 - 480316) - 19307) * 10)/ 9);
      a0 = (((((a0 * 9)/ 10) % 24)- 119) - -21);
      a29 = (((((a29 % 29)- -14) + -78248) / 5) + 15680);
       return -1;
     } else if(((( ((-86 < a4) && (-42 >= a4)) && ((input == 4) && ( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))) && ((-98 < a0) && (-61 >= a0)) ) && (a2==1))){
      a4 = ((((a4 - 168143) + 137012) * 10)/ 9);
      a0 = (((a0 - 77791) - -335670) - -161975);
      a29 = ((((a29 % 299928)- 300071) / 5) - 343834);
       a2 = 4;
       return -1;
     } else if(( ((-147 < a0) && (-98 >= a0)) && ( a29 <= -144 && ( ((-86 < a4) && (-42 >= a4)) && ((input == 3) && (a2==5)))))){
      a4 = (((((a4 + 514012) / 5) / 5) * -1)/ 10);
      a0 = (((a0 - 351273) / 5) - 16153);
       a2 = 1;
       return -1;
     } else if(((a2==4) && ( ((-86 < a4) && (-42 >= a4)) && (((input == 5) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && a0 <= -147 )))){
      if( a0 <= -147 ){
      a0 = (((((a0 + 512655) % 24)- 121) + 294399) - 294399);
      a29 = ((((a29 % 29)+ 13) + 1) / 5);
       a2 = 5;
      } else{
       a29 = ((((a29 % 29)- -14) - 188513) + 188512);
      } return 22;
     } else if((((a2==5) && ( ((-98 < a0) && (-61 >= a0)) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 2)))) && ((-86 < a4) && (-42 >= a4)) )){
      if( -61 < a0 ){
      a0 = ((((a0 / 5) * 123)/ 10) * 5);
      a29 = ((((a29 - -515249) % 299978)+ 300021) + 0);
       a2 = 3;
      } else{
       a4 = (((a4 - 159459) + -255924) * 1);
       a0 = (((a0 + 311576) / 5) + 362176);
       a29 = (((((a29 * 9)/ 10) / 5) * 5) - -587636);
       a2 = 4;
      } return 22;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==1) && ( a0 <= -147 && ( ((-16 < a29) && (43 >= a29)) && (input == 5)))))){
      a4 = ((((a4 * 21)/ 10) + -400646) * 1);
      a29 = ((((a29 - 462276) * 10)/ 9) + -52624);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( a0 <= -147 && ((( ((-144 < a29) && (-16 >= a29)) && (a2==2)) || (((a2==1) && 43 < a29 ) || ( a29 <= -144 && (a2==2)))) && (input == 4))))){
      if( a29 <= -144 ){
      a0 = ((((a0 % 24)- 121) + 467846) + -467826);
      a29 = ((((a29 + 0) % 29)+ 13) - -2);
       a2 = 2;
      } else{
       a29 = (((((a29 % 299928)+ -300071) - 2) - -592405) + -592403);
       a2 = 3;
      } return 21;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==2) && ((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 2)) && ((-98 < a0) && (-61 >= a0)) )))){
      if((a2==4)){
      a29 = (((a29 - -453579) + -1007224) + 776721);
       a2 = 5;
      } else{
       a4 = ((((a4 * 5) / 5) * 10)/ 4);
       a0 = (((((a0 * 5) % 24)- 121) + -360939) + 360945);
       a29 = (((((a29 % 63)+ -79) + -2) - -160900) - 160899);
       a2 = 4;
      } return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && ((a2==5) && ( 43 < a29 && (input == 3)))))){
      a0 = ((((a0 - 0) + -259726) % 299926)- 300072);
       a2 = 1;
       return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && (((a2==3) && (input == 4)) && 43 < a29 )))){
      if((a2==1)){
      a4 = (((((a4 % 21)- 62) - 2) + 429144) + -429136);
      a0 = ((((a0 + -428046) - -377265) % 24)- 122);
      a29 = ((((a29 % 299928)+ -300071) * 1) * 1);
       a2 = 2;
      } else{
       a4 = ((((a4 + 0) - -403065) % 21)+ -62);
       a0 = ((((a0 + 0) % 299926)+ -300072) - 3);
       a2 = 1;
      } return 26;
     } else if((( ((-147 < a0) && (-98 >= a0)) && (((( ((-16 < a29) && (43 >= a29)) && (a2==1)) || ((a2==1) && 43 < a29 )) || ((a2==2) && a29 <= -144 )) && (input == 6))) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 + 432335) / 5) - -297443) + -770462);
      a0 = ((((a0 * 5) - 438552) * 10)/ 9);
      a29 = ((((a29 - 0) % 299928)+ -300071) + -2);
       a2 = 1;
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ((((input == 1) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && (a2==3)) && ((-86 < a4) && (-42 >= a4)) ))){
      if( 136 < a4 ){
      a0 = (((a0 + -330918) / 5) / 5);
      a29 = ((((((a29 % 63)- 78) - -182185) * 3) % 63)- 138);
       a2 = 5;
      } else{
       a0 = (((a0 - -161415) + -161458) * 1);
       a29 = ((((a29 / 5) - -215380) % 29)- 2);
       a2 = 2;
      } return -1;
     } else if((((a2==2) && (( ((-144 < a29) && (-16 >= a29)) && (input == 1)) && ((-86 < a4) && (-42 >= a4)) )) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = (((a4 / 5) + -51623) + -420756);
      a0 = ((((a0 * 5) % 18)+ -77) - 1);
      a29 = (((((a29 + -36495) - -410490) / 5) * -1)/ 10);
       a2 = 3;
       return -1;
     } else if(( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && ((input == 6) && (((a2==4) && ((-144 < a29) && (-16 >= a29)) ) || (( 43 < a29 && (a2==3)) || ((a2==4) && a29 <= -144 ))))))){
      a4 = (((a4 - 511089) / 5) * 5);
      a0 = ((((((a0 / 5) % 18)- 72) * 5) % 18)+ -69);
      a29 = ((((((a29 % 299928)- 300071) + -2) * 9)/ 10) + -51962);
       a2 = 4;
       return -1;
     } else if(((((a2==1) && ((input == 5) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 - 299758) * 10)/ 9) - 263514);
      a0 = (((a0 + -189742) * -3) / 5);
      a29 = (((((a29 - 0) + 0) - -419093) % 299978)- -300021);
       a2 = 2;
       return -1;
     } else if((( ((-98 < a0) && (-61 >= a0)) && ( ((-86 < a4) && (-42 >= a4)) && ((input == 4) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) )))) && (a2==2))){
      a4 = (((a4 - 367509) * 1) + -165889);
      a0 = (((((a0 / 5) * 123)/ 10) * 10)/ 9);
      a29 = (((a29 + -128272) * 4) - 50089);
       a2 = 3;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==5) && (( a0 <= -147 && (input == 2)) && 43 < a29 )))){
      a4 = (((a4 - 332092) + -246937) * 1);
      a0 = (((((a0 % 18)- 62) / 5) * 5) - 6);
      a29 = (((((a29 - 0) + 0) + -143280) % 29)+ 14);
       a2 = 2;
       return -1;
     } else if(((a2==1) && ( ((-86 < a4) && (-42 >= a4)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 3)) && a0 <= -147 )))){
      if( a29 <= -144 ){
      a0 = ((((a0 % 24)+ -106) + -118072) + 118060);
      a29 = ((((a29 % 299978)+ 300021) + 39812) + 4757);
       a2 = 2;
      } else{
       a29 = (((((a29 * 9)/ 10) + -26438) % 63)+ -80);
       a2 = 5;
      } return 21;
     } else if(((((a2==1) && ((input == 6) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 * 21)/ 10) + -313003) - 8733);
      a0 = ((((a0 / 5) * 78)/ 10) + -182482);
      a29 = (((a29 - -141759) / 5) + -312469);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((a2==1) && ((input == 2) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-147 < a0) && (-98 >= a0)) ))){
      a4 = ((((a4 + -92205) * 10)/ 9) * 5);
      a0 = (((a0 + -14362) + -530976) + -39701);
      a29 = ((((((a29 % 299928)+ -144) / 5) + 115683) * -1)/ 10);
       return -1;
     } else if(( a0 <= -147 && ((a2==2) && ( ((-86 < a4) && (-42 >= a4)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 2)))))){
      a4 = (((a4 * 5) + -390730) / 5);
      a29 = (((a29 / 5) + -339257) + -242099);
       a2 = 1;
       return -1;
     } else if(( ((-147 < a0) && (-98 >= a0)) && ((((( 43 < a29 && (a2==2)) || ((a2==3) && a29 <= -144 )) || ((a2==3) && ((-144 < a29) && (-16 >= a29)) )) && (input == 4)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 * 5) + -596150) + -2176);
      a0 = ((((a0 * -5) * 5) * 10)/ 9);
      a29 = (((((a29 + 0) / 5) * 4) % 299978)- -300021);
       a2 = 2;
       return 22;
     } else if(((((a2==5) && ((input == 4) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((a4 / 5) + -480007) - 49681);
      a29 = ((((((a29 % 63)- 40) * 9)/ 10) - -63664) + -63691);
       a2 = 3;
       return -1;
     } else if(((a2==2) && ( ((-98 < a0) && (-61 >= a0)) && (( a29 <= -144 && (input == 1)) && ((-86 < a4) && (-42 >= a4)) )))){
      a0 = (((((a0 * 25)/ 10) - 475114) * 10)/ 9);
      a29 = (((((a29 + 0) % 29)+ 34) - -250200) + -250207);
       a2 = 1;
       return 26;
     } else if(((( a4 <= -86 && ( -61 < a0 && (input == 5))) && (a2==5)) && ((-16 < a29) && (43 >= a29)) )){
      a0 = ((((a0 % 299926)+ -300072) + -1) * 1);
      a29 = (((a29 + -335818) + -248420) / 5);
       a2 = 1;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 6)) && (a2==4)) && ((-98 < a0) && (-61 >= a0)) ))){
      if( a4 <= -86 ){
      a4 = ((((a4 * 21)/ 10) + 345448) + -402040);
      a0 = (((a0 - 104609) / -5) - -278005);
      a29 = ((((a29 % 29)+ 34) + 10997) - 11008);
       a2 = 3;
      } else{
       a4 = ((((a4 / 5) * 5) - -85502) - 357269);
       a0 = ((((a0 - 38) + -11) + -393003) + 393006);
       a29 = ((((a29 % 299928)+ -144) * 1) + -134411);
       a2 = 3;
      } return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==5) && ( ((-98 < a0) && (-61 >= a0)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 4)))))){
      a4 = ((((a4 * 10)/ 4) - -531993) + -849572);
      a0 = (((((a0 / 5) * 9)/ 10) - 551674) * -1);
      a29 = (((((a29 + 0) % 299978)- -300021) / 5) + 138947);
       return 26;
     } else if(((( ((-86 < a4) && (-42 >= a4)) && ((input == 4) && ((-98 < a0) && (-61 >= a0)) )) && a29 <= -144 ) && (a2==2))){
      a4 = ((((a4 + 545933) * -1)/ 10) * 5);
      a0 = ((((a0 + -122294) * -4) * 10)/ 9);
       a2 = 4;
       return 21;
     } else if(((a2==1) && ((((input == 1) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && a0 <= -147 ) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 - 583803) / 5) / 5);
      a0 = (((((a0 / 5) % 24)+ -100) - 190928) - -190917);
      a29 = ((((a29 % 29)- -33) + 470403) + -470405);
       a2 = 3;
       return -1;
     } else if(( a4 <= -86 && ( -61 < a0 && (((((a2==4) && 43 < a29 ) || ((a2==5) && a29 <= -144 )) || ( ((-144 < a29) && (-16 >= a29)) && (a2==5))) && (input == 3))))){
      a4 = (((((a4 % 21)+ -44) * 1) / 5) - 48);
      a0 = ((((a0 % 299926)- 300072) * 1) - 3);
      a29 = ((((a29 % 299978)+ 300021) * 1) * 1);
       a2 = 3;
       return 22;
     } else if((((a2==5) && (((input == 5) && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) || 43 < a29 )) && ((-147 < a0) && (-98 >= a0)) )) && ((-86 < a4) && (-42 >= a4)) )){
      a29 = (((((a29 % 299978)+ 300021) * 1) - 479458) + 479460);
       return 22;
     } else if(((( ((-16 < a29) && (43 >= a29)) && ((input == 1) && ((-147 < a0) && (-98 >= a0)) )) && (a2==2)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((((a4 * 10)/ 4) - 371477) * 10)/ 9);
      a0 = (((((a0 * 10)/ 15) - 0) / 5) + -57);
      a29 = (((a29 * 5) / 5) - 552027);
       a2 = 3;
       return -1;
     } else if((( a4 <= -86 && ((input == 6) && ((((a2==2) && ((-16 < a29) && (43 >= a29)) ) || ((a2==2) && 43 < a29 )) || ((a2==3) && a29 <= -144 )))) && -61 < a0 )){
      a0 = (((a0 / 5) + -278887) / 5);
      a29 = ((((a29 % 299928)+ -300071) - -514060) - 514060);
       a2 = 1;
       return -1;
     } else if(((( -61 < a0 && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 5))) && a4 <= -86 ) && (a2==3))){
      a0 = ((((a0 + -325280) + -120034) % 299926)+ -300072);
      a29 = (((a29 + -112448) + -33410) * 4);
       a2 = 1;
       return -1;
     } else if(( ((-147 < a0) && (-98 >= a0)) && ( ((-86 < a4) && (-42 >= a4)) && ((((a2==3) && ((-144 < a29) && (-16 >= a29)) ) || (( 43 < a29 && (a2==2)) || ((a2==3) && a29 <= -144 ))) && (input == 5))))){
      a4 = (((a4 - 179640) + -196180) * 1);
      a0 = (((((a0 * 5) % 18)+ -68) * 10)/ 9);
      a29 = ((((a29 / 5) * 4) % 299978)+ 300021);
       a2 = 3;
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ((((input == 6) && ((-86 < a4) && (-42 >= a4)) ) && (a2==1)) && 43 < a29 ))){
      a4 = ((((a4 * 10)/ 4) * 5) + -460043);
      a0 = ((((a0 - 39) - -1) / 5) - 102);
      a29 = (((a29 / 5) * 4) - 486694);
       a2 = 2;
       return -1;
     } else if(( a0 <= -147 && ((((input == 6) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && (a2==4)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 - 124968) - 172519) + -276986);
      a29 = (((((a29 % 299928)- 300071) - -241689) + 178566) + -420255);
       a2 = 2;
       return -1;
     } else if(((((a2==1) && ((input == 2) && ( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((a4 + 4337) - 75733) * 5);
      a0 = ((((a0 * 10)/ 4) + -416474) * 1);
      a29 = ((((((a29 % 63)- 79) * 1) * 5) % 63)- 77);
       return -1;
     } else if((( ((-98 < a0) && (-61 >= a0)) && ((a2==4) && ((input == 4) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((a4 - 5349) - 71855) - 8649);
      a0 = ((((a0 - 80857) * 10)/ 9) / 5);
      a29 = ((((((a29 % 63)+ -58) * 9)/ 10) - 554414) + 554401);
       a2 = 2;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 4) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )) && a0 <= -147 )) && (a2==3))){
      a4 = (((a4 + -429677) * 1) * 1);
      a0 = (((a0 - -600060) + 7) / 5);
      a29 = (((((a29 * 9)/ 10) % 63)- 78) - 2);
       a2 = 4;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((( a29 <= -144 && (a2==2)) || (( ((-16 < a29) && (43 >= a29)) && (a2==1)) || ((a2==1) && 43 < a29 ))) && (input == 4))) && ((-147 < a0) && (-98 >= a0)) )){
      if( ((-42 < a4) && (136 >= a4)) ){
      a29 = ((((a29 - 0) - 0) % 299978)+ 300021);
       a2 = 4;
      } else{
       a0 = (((((a0 % 18)+ -72) + 11) * 10)/ 9);
       a29 = (((((a29 % 63)- 78) + 354675) - 303746) - 50931);
       a2 = 1;
      } return 21;
     } else if(( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && ((input == 1) && (( ((-144 < a29) && (-16 >= a29)) && (a2==4)) || (( 43 < a29 && (a2==3)) || ((a2==4) && a29 <= -144 ))))))){
      a4 = ((((a4 + -38853) + -127579) * 10)/ 9);
      a0 = (((a0 - -600019) * 1) - -48);
      a29 = ((((a29 % 299928)+ -300071) + -1) * 1);
       a2 = 3;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 5)) && (a2==2))) && a0 <= -147 )){
      a4 = ((((a4 - 432014) * 1) * 10)/ 9);
      a29 = ((((a29 % 299928)- 300071) * 1) * 1);
       a2 = 1;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==3) && ( ((-147 < a0) && (-98 >= a0)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 5)))))){
      a4 = (((a4 + -445432) - 38917) / 5);
      a0 = (((a0 + -523061) * 1) / 5);
      a29 = ((((a29 % 299928)+ -300071) - 1) + -1);
       a2 = 1;
       return -1;
     } else if(((a2==5) && ((( a0 <= -147 && (input == 5)) && 43 < a29 ) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 - 571896) + -12207) * 1);
      a0 = (((a0 + 600032) - -112) / 5);
      a29 = (((((a29 % 29)+ -10) + -1) + -180973) + 180992);
       return -1;
     } else if(( ((-16 < a29) && (43 >= a29)) && (( ((-86 < a4) && (-42 >= a4)) && ((a2==1) && (input == 3))) && a0 <= -147 ))){
      if( ((-144 < a29) && (-16 >= a29)) ){
      a0 = (((((a0 % 24)+ -116) - -428496) + 96525) + -525025);
      a29 = (((((a29 / 5) - -588420) - -8138) * -1)/ 10);
       a2 = 5;
      } else{
       a29 = (((a29 - -367691) + 130494) - -35139);
       a2 = 5;
      } return 22;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-147 < a0) && (-98 >= a0)) && ((a2==4) && ((input == 4) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )))))){
      a4 = (((((a4 * 10)/ 4) + 147908) - -409340) + -1095280);
      a0 = (((a0 * -5) / 5) - -445352);
      a29 = ((((((a29 + -342777) % 29)+ 14) * 5) % 29)- -14);
       return -1;
     } else if((( a4 <= -86 && ((input == 3) && ((((a2==1) && 43 < a29 ) || ( a29 <= -144 && (a2==2))) || ((a2==2) && ((-144 < a29) && (-16 >= a29)) )))) && -61 < a0 )){
      a0 = ((((a0 % 299926)- 300072) + 0) - 0);
      a29 = ((((a29 % 299928)+ -300071) * 1) * 1);
       a2 = 1;
       return -1;
     } else if(((a2==4) && ((((input == 6) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) ))){
      a0 = (((a0 * 5) * 5) * 5);
      a29 = ((((a29 - 587266) % 29)+ 13) + 2);
       return -1;
     } else if(((a2==5) && ((((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 3)) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 ))){
      a4 = ((((((a4 * 21)/ 10) * 10)/ 9) / 5) - 395341);
      a0 = ((((a0 - -158225) % 18)- 78) - 1);
      a29 = (((((a29 + 522034) % 299928)+ -300071) + 203886) + -203887);
       a2 = 1;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((((a2==3) && ((-144 < a29) && (-16 >= a29)) ) || (((a2==2) && 43 < a29 ) || ( a29 <= -144 && (a2==3)))) && (input == 1))) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = ((((a4 - 71431) + 461687) - -176106) + -1067274);
      a29 = ((((a29 + 0) % 299978)+ 300021) * 1);
       a2 = 4;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (input == 2)) && a0 <= -147 ) && (a2==5)))){
      a4 = ((((a4 * 5) + -282138) * 10)/ 9);
      a29 = (((a29 / 5) - 228236) * 1);
       a2 = 3;
       return -1;
     } else if(( a4 <= -86 && ( -61 < a0 && ((input == 5) && ((( 43 < a29 && (a2==4)) || ( a29 <= -144 && (a2==5))) || ((a2==5) && ((-144 < a29) && (-16 >= a29)) )))))){
      a0 = (((a0 / 5) + -531058) + -5391);
      a29 = ((((a29 % 299928)- 300071) - 1) + -1);
       a2 = 1;
       return -1;
     } else if(((a2==3) && ( a4 <= -86 && ((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 1)) && -61 < a0 )))){
      a29 = (((a29 * 5) - -271226) / 5);
       a2 = 5;
       return 21;
     } else if(((a2==5) && ((((input == 1) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) ))){
      if( ((-147 < a0) && (-98 >= a0)) ){
      a29 = ((((a29 % 299928)+ -144) * 1) - 299526);
       a2 = 3;
      } else{
       a29 = ((((a29 % 29)- -25) + -3) - 3);
       a2 = 4;
      } return -1;
     } else if((((( -61 < a0 && (input == 2)) && 43 < a29 ) && a4 <= -86 ) && (a2==5))){
      a0 = (((((a0 - 0) % 18)- 79) + -287852) - -287851);
      a29 = ((((a29 + -432842) % 63)+ -79) * 1);
       a2 = 1;
       return -1;
     } else if((((((input == 1) && (a2==1)) && 43 < a29 ) && ((-98 < a0) && (-61 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((((a4 * 10)/ 4) - 50479) + 331538) - 286662);
      a0 = (((a0 + -221394) * 2) - 61944);
       a2 = 5;
       return 22;
     } else if(((((a2==2) && ((input == 4) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = ((((a4 / 5) * 108)/ 10) + -99001);
      a0 = (((a0 + 600024) * 1) - -69);
      a29 = (((((a29 * 9)/ 10) % 29)+ 13) + 1);
       return 22;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 6) && 43 < a29 ) && (a2==2))) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((a4 / 5) + -431166) * 1);
      a0 = ((((((a0 * 25)/ 10) + 207162) * 2) * -1)/ 10);
      a29 = ((((a29 % 299928)- 300071) / 5) + -301321);
       a2 = 1;
       return 21;
     } else if(( ((-147 < a0) && (-98 >= a0)) && (((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 3)) && ((-86 < a4) && (-42 >= a4)) ) && (a2==3)))){
      a0 = ((((a0 - -11543) + -341421) * 10)/ 9);
      a29 = ((((a29 / 5) % 63)+ -79) * 1);
       a2 = 4;
       return 22;
     } else if((( ((-147 < a0) && (-98 >= a0)) && (((input == 1) && (a2==5)) && ((-86 < a4) && (-42 >= a4)) )) && a29 <= -144 )){
      a4 = (((a4 / 5) - 552897) * 1);
      a0 = (((a0 + 155241) + 354784) / 5);
      a29 = (((((a29 * 9)/ 10) - 55038) % 29)+ 15);
       return 26;
     } else if((((a2==1) && ( a0 <= -147 && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 6)))) && ((-86 < a4) && (-42 >= a4)) )){
      a29 = ((((a29 + 0) % 299978)+ 300021) - -243945);
       a2 = 5;
       return 22;
     } else if(((((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 2)) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) ) && (a2==4))){
      a4 = ((((a4 - -387581) * 10)/ -9) - 92057);
      a0 = ((((a0 - 206221) - -444674) / 5) + -346446);
      a29 = (((((a29 - -129597) * 1) + -62679) % 299928)+ -300071);
       a2 = 1;
       return -1;
     } else if((((a2==1) && (((input == 5) && ((-86 < a4) && (-42 >= a4)) ) && 43 < a29 )) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = ((((a4 * 21)/ 10) - 513244) - 63334);
      a29 = ((((a29 % 29)- 14) + 8) - -20);
       a2 = 5;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ( ((-98 < a0) && (-61 >= a0)) && ((input == 5) && (a2==2)))) && a29 <= -144 )){
      a4 = ((((a4 + -126587) * 10)/ 9) * 4);
      a0 = (((((a0 * 25)/ 10) * 10)/ 9) - 138870);
      a29 = (((((a29 * 9)/ 10) * 1) % 29)- -18);
       a2 = 1;
       return -1;
     } else if((( -61 < a0 && ((a2==1) && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 3)))) && a4 <= -86 )){
      a0 = (((((a0 % 299926)- 300072) * 1) - -96529) - 96530);
      a29 = (((a29 * 5) + -30526) + -238122);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((((((a2==1) && ((-16 < a29) && (43 >= a29)) ) || ( 43 < a29 && (a2==1))) || ((a2==2) && a29 <= -144 )) && (input == 5)) && ((-147 < a0) && (-98 >= a0)) ))){
      a4 = ((((a4 * 10)/ 4) * 5) / 5);
      a0 = ((((a0 * 10)/ 6) - 118188) + -397063);
      a29 = ((((a29 % 299928)- 300071) + -1) + -1);
       a2 = 1;
       return -1;
     } else if((((( ((-147 < a0) && (-98 >= a0)) && (input == 4)) && ((-16 < a29) && (43 >= a29)) ) && (a2==2)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 / 5) - 192549) * 10)/ 9);
      a0 = (((a0 + 287869) * 2) * 1);
      a29 = (((a29 - -35786) + 395553) - 630549);
       a2 = 4;
       return -1;
     } else if(( a4 <= -86 && ((( 43 < a29 && (input == 5)) && -61 < a0 ) && (a2==3)))){
      a0 = ((((a0 % 299926)- 300072) - 1) + -2);
      a29 = (((((a29 - 0) * 9)/ 10) / 5) - 544016);
       a2 = 1;
       return -1;
     } else if((((a2==4) && ( a4 <= -86 && ((input == 3) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )))) && -61 < a0 )){
      a0 = ((((a0 % 299926)+ -300072) * 1) + -3);
      a29 = ((((a29 % 299928)+ -300071) + -2) + 0);
       a2 = 1;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (((( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (input == 6)) && ((-98 < a0) && (-61 >= a0)) ) && (a2==1)))){
      a4 = ((((a4 / 5) / 5) * 861)/ 10);
      a0 = (((a0 - -100650) / 5) + -453515);
      a29 = ((((a29 % 29)+ 13) / 5) - -27);
       a2 = 3;
       return -1;
     } else if(((((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 6)) && ((-86 < a4) && (-42 >= a4)) ) && (a2==2)) && a0 <= -147 )){
      a4 = (((a4 / 5) - 522593) + -49139);
      a29 = (((a29 / 5) + -408943) - 141073);
       a2 = 1;
       return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && ((( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (input == 2)) && (a2==4))))){
      a0 = ((((a0 % 299926)+ -300072) - 2) * 1);
      a29 = ((((a29 - 0) * 9)/ 10) + -22730);
       a2 = 1;
       return -1;
     } else if((((((input == 1) && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) || 43 < a29 )) && ((-147 < a0) && (-98 >= a0)) ) && (a2==5)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((a4 - 464292) / 5) + -349277);
      a0 = (((((a0 - -292898) % 18)- 83) * 10)/ 9);
      a29 = (((((a29 * 9)/ 10) % 29)- -13) - -1);
       a2 = 1;
       return -1;
     } else if(((( ((-98 < a0) && (-61 >= a0)) && ((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && (a2==3)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 - -392870) * 1) * 1) + -704326);
      a0 = (((a0 - 3611) * 5) / 5);
      a29 = ((((((a29 * 9)/ 10) % 29)+ 14) + -564199) - -564199);
       return 26;
     } else if((((a2==4) && ( ((-86 < a4) && (-42 >= a4)) && ((input == 1) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )))) && ((-98 < a0) && (-61 >= a0)) )){
      a29 = ((((((a29 % 63)- 80) + -1) * 5) % 63)+ -70);
       return 22;
     } else if((((a2==2) && (( ((-147 < a0) && (-98 >= a0)) && (input == 4)) && ((-86 < a4) && (-42 >= a4)) )) && ((-144 < a29) && (-16 >= a29)) )){
      a4 = (((((a4 * 10)/ 4) * 5) * 10)/ 9);
      a0 = (((a0 - 286794) / -5) * 5);
      a29 = (((((a29 * 5) % 29)- -15) - -348140) + -348131);
       a2 = 4;
       return -1;
     } else if(((a2==5) && ( ((-86 < a4) && (-42 >= a4)) && (( ((-147 < a0) && (-98 >= a0)) && (input == 4)) && a29 <= -144 )))){
      a4 = (((a4 * 5) / 5) + -406842);
      a29 = ((((a29 - -600125) + 18) - 208856) + 208841);
       return -1;
     } else if(( a4 <= -86 && ((((((a2==2) && ((-16 < a29) && (43 >= a29)) ) || ( 43 < a29 && (a2==2))) || ((a2==3) && a29 <= -144 )) && (input == 3)) && -61 < a0 ))){
      a29 = ((((a29 + 0) + 0) % 29)+ 14);
       a2 = 4;
       return 22;
     } else if(((a2==2) && ( ((-86 < a4) && (-42 >= a4)) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 1)) && a0 <= -147 )))){
      a29 = ((((a29 % 29)- -14) / 5) / 5);
       return 26;
     } else if(( a0 <= -147 && ((((((a2==3) && 43 < a29 ) || ( a29 <= -144 && (a2==4))) || ((a2==4) && ((-144 < a29) && (-16 >= a29)) )) && (input == 4)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 - -368988) + -509555) * 4);
      a29 = (((a29 / 5) - 269560) - -609922);
       a2 = 4;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && (( a0 <= -147 && ((a2==5) && (input == 1))) && 43 < a29 ))){
      a4 = ((((a4 - 527117) * 10)/ 9) + -13727);
      a0 = (((a0 - -361747) - -238361) - -15);
      a29 = ((((((a29 - 0) * 9)/ 10) / 5) % 29)+ -13);
       return 26;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 3)) && ((-98 < a0) && (-61 >= a0)) )) && (a2==5))){
      if( ((-144 < a29) && (-16 >= a29)) ){
      a0 = (((a0 - -265548) + 287278) + -1007061);
      a29 = ((((a29 % 63)+ -78) * 1) + -3);
       a2 = 2;
      } else{
       a4 = (((a4 + -300226) / 5) + -5161);
       a0 = (((a0 - 211989) + -343212) / 5);
       a29 = (((((a29 / 5) / 5) + -325965) % 63)+ -68);
       a2 = 1;
      } return 22;
     } else if((((a2==2) && (((input == 4) && ((-86 < a4) && (-42 >= a4)) ) && 43 < a29 )) && ((-98 < a0) && (-61 >= a0)) )){
      if((a2==2)){
      a4 = (((a4 / 5) - -464382) - 647516);
      a0 = ((((a0 / 5) / -5) * 10)/ 9);
       a2 = 5;
      } else{
       a0 = ((((a0 - 280318) + -109923) + 576736) + -186541);
       a29 = ((((a29 + -496909) * 1) % 29)- -14);
       a2 = 4;
      } return -1;
     } else if((((((( ((-16 < a29) && (43 >= a29)) && (a2==1)) || ( 43 < a29 && (a2==1))) || ((a2==2) && a29 <= -144 )) && (input == 2)) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = (((((a4 * 10)/ 4) * 5) - -131007) - 193084);
      a0 = (((a0 / 5) - 548765) - 28905);
      a29 = ((((a29 % 299928)+ -300071) + -1) * 1);
       a2 = 1;
       return -1;
     } else if(( a4 <= -86 && (((input == 6) && ((( 43 < a29 && (a2==1)) || ( a29 <= -144 && (a2==2))) || ((a2==2) && ((-144 < a29) && (-16 >= a29)) ))) && -61 < a0 ))){
      a29 = ((((((a29 * 9)/ 10) % 29)- -14) + -303719) + 303718);
       a2 = 3;
       return 26;
     } else if(((a2==1) && (( 43 < a29 && ((input == 2) && ((-98 < a0) && (-61 >= a0)) )) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 * 5) + -378206) * 1);
      a0 = (((((a0 + -41) + 3) * 5) % 24)- 116);
      a29 = (((((a29 % 299928)- 300071) * 10)/ 9) + -191104);
       return -1;
     } else if((((((input == 4) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) )) && a4 <= -86 ) && (a2==3)) && -61 < a0 )){
      a4 = ((((((a4 % 21)- 48) * 9)/ 10) / 5) + -43);
      a0 = (((((a0 % 299926)+ -300072) * 1) / 5) - 339337);
      a29 = (((((a29 % 63)- 79) + -57784) - -570548) - 512763);
       a2 = 1;
       return 22;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && (a2==4))) && ((-98 < a0) && (-61 >= a0)) )){
      if( ((-16 < a29) && (43 >= a29)) ){
      a29 = ((((a29 % 299978)- -300021) + 0) * 1);
      } else{
       a4 = (((a4 * 5) - 209138) * 2);
       a0 = (((a0 - -253752) + -726068) - 17929);
       a29 = ((((a29 % 299928)+ -300071) + -1) - 1);
       a2 = 3;
      } return -1;
     } else if(((a2==2) && (((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 3)) && ((-98 < a0) && (-61 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = ((((a4 * 10)/ 4) / 5) * 5);
      a0 = (((a0 + 570549) + 7739) + 17884);
      a29 = ((((a29 - -418570) / 5) - 588464) - -504725);
       a2 = 4;
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ((((input == 2) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (a2==4)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 - 175972) - 86348) + -117422);
      a0 = (((a0 + -58554) + -305933) - 232165);
      a29 = (((((a29 + 0) - 0) - 0) % 29)- -29);
       a2 = 1;
       return 26;
     } else if(( ((-147 < a0) && (-98 >= a0)) && ( ((-86 < a4) && (-42 >= a4)) && (((input == 2) && (( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) || 43 < a29 )) && (a2==5))))){
      a4 = (((a4 + 316167) + -662467) * 1);
      a29 = ((((a29 % 29)- -13) + 0) - 0);
       a2 = 4;
       return -1;
     } else if(( 43 < a29 && ( a4 <= -86 && ( -61 < a0 && ((a2==3) && (input == 3)))))){
      a0 = ((((a0 % 299926)- 300072) - 0) - 1);
      a29 = ((((a29 % 299928)- 300071) + 99924) + -200774);
       a2 = 1;
       return -1;
     } else if((((((input == 1) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) ) && (a2==3))){
      if( ((-98 < a0) && (-61 >= a0)) ){
      a29 = ((((((a29 % 29)- -13) + -61659) * 5) % 29)+ 24);
       a2 = 5;
      } else{
       a0 = (((a0 - 401265) / 5) + -135803);
       a29 = ((((a29 % 299978)+ 300021) - 0) * 1);
       a2 = 4;
      } return 22;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( a0 <= -147 && ((( ((-144 < a29) && (-16 >= a29)) && (a2==2)) || (( 43 < a29 && (a2==1)) || ((a2==2) && a29 <= -144 ))) && (input == 1))))){
      a29 = ((((((a29 - 0) - 0) * 9)/ 10) % 29)- -13);
       a2 = 2;
       return 21;
     } else if(((a2==4) && ((((input == 3) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) ))){
      a0 = ((((a0 * 5) - 152016) * 10)/ 9);
      a29 = ((((a29 % 299928)+ -300071) + 0) * 1);
       a2 = 3;
       return -1;
     } else if(((a2==4) && ((((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 1)) && a4 <= -86 ) && -61 < a0 ))){
      a0 = (((((a0 - 0) % 299926)- 300072) + 580975) - 580976);
      a29 = (((a29 - 0) / 5) - 197811);
       a2 = 1;
       return -1;
     } else if((((a2==4) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 4)) && ((-98 < a0) && (-61 >= a0)) )) && ((-86 < a4) && (-42 >= a4)) )){
      a0 = ((((a0 - 43) * 5) % 24)+ -121);
      a29 = ((((a29 % 63)- 79) - -14650) + -14651);
       a2 = 2;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ( 43 < a29 && ((input == 3) && (a2==1)))) && ((-98 < a0) && (-61 >= a0)) )){
      a0 = (((((a0 * 5) - 204273) * 2) % 24)- 115);
      a29 = ((((a29 + 0) / 5) % 29)+ -10);
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ((a2==1) && ( ((-86 < a4) && (-42 >= a4)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 3)))))){
      a0 = (((a0 - 558048) + -12197) - 637);
      a29 = ((((a29 % 63)- 78) + -41396) - -41393);
       a2 = 3;
       return -1;
     } else if(( a0 <= -147 && (((((a2==2) && ((-144 < a29) && (-16 >= a29)) ) || (( 43 < a29 && (a2==1)) || ( a29 <= -144 && (a2==2)))) && (input == 2)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = ((((a4 * 10)/ 4) - 138332) + -409121);
      a29 = (((((a29 % 299928)+ -300071) + 218992) * 1) + -218992);
       a2 = 1;
       return -1;
     } else if(((( ((-86 < a4) && (-42 >= a4)) && ((input == 2) && (a2==2))) && ((-147 < a0) && (-98 >= a0)) ) && ((-144 < a29) && (-16 >= a29)) )){
      a4 = (((a4 / 5) - 28051) / 5);
      a0 = (((a0 - -70089) + 469661) + -953384);
       a2 = 1;
       return -1;
     } else if((((( ((-98 < a0) && (-61 >= a0)) && (input == 2)) && a29 <= -144 ) && (a2==2)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = (((a4 + -494899) * 1) - 70550);
      a0 = ((((a0 - -314354) + 111880) * 10)/ 9);
      a29 = ((((a29 + 0) / 5) % 63)- 54);
       a2 = 1;
       return -1;
     } else if((((a2==5) && ( -61 < a0 && ((input == 5) && 43 < a29 ))) && a4 <= -86 )){
      a4 = ((((((a4 % 21)- 62) - 1) * 5) % 21)- 47);
      a0 = ((((a0 / 5) + 345979) * 10)/ -9);
       a2 = 3;
       return 22;
     } else if((((( a0 <= -147 && (input == 6)) && (a2==5)) && 43 < a29 ) && ((-86 < a4) && (-42 >= a4)) )){
       a2 = 2;
       return -1;
     } else if(( 43 < a29 && ((((input == 4) && a0 <= -147 ) && ((-86 < a4) && (-42 >= a4)) ) && (a2==5)))){
      a4 = ((((a4 * 21)/ 10) * 5) - 593094);
      a0 = ((((((a0 % 24)- 122) + -1) * 5) % 24)+ -109);
       return -1;
     } else if((( ((-147 < a0) && (-98 >= a0)) && ((a2==1) && ((input == 3) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))) && ((-86 < a4) && (-42 >= a4)) )){
      a0 = (((a0 + -127384) / 5) + -187730);
      a29 = (((((a29 - -345279) + -27646) * 1) % 299928)- 300071);
       a2 = 4;
       return -1;
     } else if(( -61 < a0 && (((input == 1) && ((( 43 < a29 && (a2==1)) || ( a29 <= -144 && (a2==2))) || ( ((-144 < a29) && (-16 >= a29)) && (a2==2)))) && a4 <= -86 ))){
      a0 = (((((a0 % 299926)+ -300072) / 5) - -67866) - 413054);
      a29 = ((((a29 % 299928)+ -300071) + -1) - 1);
       a2 = 1;
       return -1;
     } else if(((( ((-98 < a0) && (-61 >= a0)) && ((input == 6) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && (a2==3)) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 - 339023) + -231980) - -829860) - 719049);
      a0 = (((a0 / 5) * 5) + -38);
      a29 = ((((a29 - 0) + 561071) % 299978)- -300021);
       a2 = 5;
       return -1;
     } else if(((a2==3) && (( ((-98 < a0) && (-61 >= a0)) && ((input == 4) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = ((((a4 * 10)/ 4) - -506734) - 541845);
      a29 = ((((a29 % 63)- 80) + 2) + -3);
       a2 = 1;
       return 22;
     } else if(( -61 < a0 && ((((( 43 < a29 && (a2==1)) || ( a29 <= -144 && (a2==2))) || ( ((-144 < a29) && (-16 >= a29)) && (a2==2))) && (input == 2)) && a4 <= -86 ))){
      a0 = (((((a0 % 299926)+ -300072) - 2) + 355893) - 355891);
      a29 = (((((a29 % 299928)- 300071) + 0) / 5) + -174546);
       a2 = 1;
       return -1;
     } else if(((((input == 1) && (( a29 <= -144 && (a2==2)) || (( ((-16 < a29) && (43 >= a29)) && (a2==1)) || ((a2==1) && 43 < a29 )))) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) )){
      a0 = ((((a0 * 10)/ 6) * 5) + -500106);
      a29 = (((a29 / 5) + 469185) + 438);
       a2 = 2;
       return 21;
     } else if(((( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && (input == 3))) && (a2==5)) && 43 < a29 )){
      a4 = (((a4 - 205078) * 2) + -14481);
      a29 = (((((a29 % 299928)+ -300071) + -41059) * 10)/ 9);
       a2 = 1;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 5)) && a0 <= -147 )) && (a2==3))){
      a4 = ((((a4 * 21)/ 10) + -45471) - 243489);
      a29 = (((a29 / 5) - -107734) + 61057);
       a2 = 5;
       return -1;
     } else if(((a2==2) && ((((input == 3) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 ))){
      a29 = ((((a29 % 299978)- -300021) - -1) + 0);
       return 26;
     } else if(((( ((-86 < a4) && (-42 >= a4)) && ( ((-147 < a0) && (-98 >= a0)) && (input == 2))) && (a2==5)) && a29 <= -144 )){
      a4 = (((a4 + 50595) + -107412) + -84938);
      a0 = (((((a0 % 18)- 61) - 8) + -274611) - -274610);
      a29 = ((((((a29 * 9)/ 10) / 5) * 5) % 29)+ 42);
       a2 = 2;
       return -1;
     } else if((( -61 < a0 && ((input == 5) && ((((a2==1) && 43 < a29 ) || ((a2==2) && a29 <= -144 )) || ( ((-144 < a29) && (-16 >= a29)) && (a2==2))))) && a4 <= -86 )){
      a0 = (((((a0 % 299926)- 300072) * 1) / 5) + -364241);
      a29 = ((((a29 % 299928)+ -300071) * 1) + -2);
       a2 = 1;
       return -1;
     } else if(((a2==1) && ((((input == 1) && ( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) ))){
      a4 = ((((a4 * 10)/ 4) * 5) / 5);
      a29 = ((((a29 % 299928)+ -300071) + 0) * 1);
       a2 = 3;
       return -1;
     } else if(((( ((-147 < a0) && (-98 >= a0)) && ((a2==2) && (input == 6))) && ((-86 < a4) && (-42 >= a4)) ) && ((-16 < a29) && (43 >= a29)) )){
      a4 = (((a4 / 5) + 304026) - 427802);
      a0 = (((a0 * 5) - 577550) * 1);
       a2 = 3;
       return -1;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ( 43 < a29 && (((a2==2) && (input == 2)) && ((-86 < a4) && (-42 >= a4)) )))){
      if((a2==3)){
       a2 = 1;
      } else{
       a0 = ((((a0 + -367017) - -366972) + -502345) + 502343);
       a29 = ((((a29 * 9)/ 10) - 582444) - 2215);
       a2 = 1;
      } return -1;
     } else if(((((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 3)) && ((-86 < a4) && (-42 >= a4)) ) && ((-98 < a0) && (-61 >= a0)) ) && (a2==3))){
      a4 = (((a4 + 359989) / 5) + -145327);
      a29 = (((((a29 % 63)+ -80) - 1) * 9)/ 10);
       a2 = 1;
       return -1;
     } else if(( ((-147 < a0) && (-98 >= a0)) && (( ((-86 < a4) && (-42 >= a4)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 4))) && (a2==3)))){
      a4 = ((((a4 * 5) * 10)/ 9) - 472916);
      a0 = (((a0 * 5) + -199603) + -185614);
      a29 = ((((a29 % 299928)- 300071) + -1) * 1);
       a2 = 1;
       return -1;
     } else if(((a2==1) && (((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 6)) && a4 <= -86 ) && -61 < a0 ))){
      a0 = ((((a0 * 9)/ 10) - 587044) + -1747);
      a29 = (((a29 - 138235) - 4077) / 5);
       return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && (((input == 5) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) )) && (a2==1))))){
      a0 = (((((a0 % 299926)- 300072) - 3) + 505433) - 505432);
      a29 = (((a29 - 76359) - 240588) * 1);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((((input == 5) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && ((-98 < a0) && (-61 >= a0)) ) && (a2==4)))){
      if( ((-16 < a29) && (43 >= a29)) ){
      a4 = (((a4 + -550870) - 30700) + -8946);
      a0 = (((a0 - 347957) - -538641) + 141803);
      a29 = ((((((a29 * 9)/ 10) % 29)- -38) + 300246) + -300253);
       a2 = 1;
      } else{
       a29 = ((((a29 / 5) % 29)- -23) + -10);
       a2 = 3;
      } return -1;
     } else if((( a0 <= -147 && (((input == 1) && ((-86 < a4) && (-42 >= a4)) ) && (a2==1))) && ((-16 < a29) && (43 >= a29)) )){
      a29 = (((a29 + 573320) + 18246) * 1);
       a2 = 4;
       return 22;
     } else if((( -61 < a0 && ((((a2==5) && ((-144 < a29) && (-16 >= a29)) ) || (( 43 < a29 && (a2==4)) || ((a2==5) && a29 <= -144 ))) && (input == 6))) && a4 <= -86 )){
      a0 = ((((a0 % 299926)+ -300072) / 5) + -390280);
      a29 = (((((a29 % 299928)+ -300071) / 5) * 5) - 4);
       a2 = 1;
       return -1;
     } else if(( ((-147 < a0) && (-98 >= a0)) && ((a2==5) && (((input == 4) && ( 43 < a29 || ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) )))){
      a0 = (((((a0 * 10)/ 6) + 363321) * -1)/ 10);
      a29 = ((((a29 % 299978)- -300021) - 439759) - -439760);
       a2 = 4;
       return 22;
     } else if((( a0 <= -147 && (((input == 4) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) )) && (a2==4))){
      if( a0 <= -147 ){
      a0 = (((((a0 / 5) - 10779) * 4) % 24)- 116);
      a29 = (((((a29 % 63)- 78) * 1) - 400269) - -400266);
       a2 = 5;
      } else{
       a29 = (((((a29 / 5) - -358331) - 904415) * -1)/ 10);
      } return 22;
     } else if(((((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 6)) && a4 <= -86 ) && (a2==3)) && -61 < a0 )){
      a0 = ((((a0 % 299926)- 300072) + -2) + -1);
      a29 = ((((a29 - 117398) + 20287) * 10)/ 9);
       a2 = 1;
       return -1;
     } else if((((((input == 6) && a29 <= -144 ) && ((-86 < a4) && (-42 >= a4)) ) && (a2==5)) && ((-147 < a0) && (-98 >= a0)) )){
      a0 = ((((a0 * 15)/ 10) * 5) * 5);
      a29 = (((((((a29 % 29)- -32) * 9)/ 10) * 5) % 29)+ 5);
       a2 = 2;
       return -1;
     } else if((((((input == 4) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) ) && (a2==5)) && a0 <= -147 )){
      a4 = ((((a4 / 5) - 475134) * 10)/ 9);
      a0 = (((a0 + 600138) + 8) * 1);
      a29 = ((((a29 % 299978)- -300021) * 1) * 1);
       a2 = 2;
       return 22;
     } else if(( -61 < a0 && (((a2==3) && ( a4 <= -86 && (input == 1))) && 43 < a29 ))){
      a4 = ((((a4 % 21)- 60) - 76016) + 76016);
      a0 = ((((a0 + 0) * 9)/ 10) - 595384);
      a29 = (((((a29 * 9)/ 10) + -532371) % 29)+ 13);
       a2 = 1;
       return 21;
     } else if((( ((-86 < a4) && (-42 >= a4)) && (((input == 6) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )) && (a2==5))) && a0 <= -147 )){
      a29 = (((((a29 % 29)- -14) + -387824) + 752212) + -364388);
       return 22;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((a2==4) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 4)))) && ((-147 < a0) && (-98 >= a0)) )){
      a0 = ((((a0 - 283784) + -203187) * 10)/ 9);
      a29 = ((((a29 * 9)/ 10) - 36588) - -616793);
       a2 = 5;
       return 22;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 5)) && ((-98 < a0) && (-61 >= a0)) )) && (a2==3))){
      if( a0 <= -147 ){
      a4 = (((a4 - 538200) * 1) + -6027);
      a0 = (((((a0 + 338124) + -338172) * 5) % 24)- 116);
      a29 = (((((a29 + 217515) * 1) * 1) % 29)- -13);
       a2 = 4;
      } else{
       a4 = (((a4 + -350456) * 1) + -153833);
       a0 = (((a0 - 245704) + 245659) - -1);
       a29 = ((((a29 - 0) / 5) % 63)+ -53);
       a2 = 5;
      } return -1;
     } else if(( a4 <= -86 && ((((((a2==1) && 43 < a29 ) || ((a2==2) && a29 <= -144 )) || ( ((-144 < a29) && (-16 >= a29)) && (a2==2))) && (input == 4)) && -61 < a0 ))){
      a29 = ((((a29 % 299978)- -300021) - 0) + 0);
       a2 = 3;
       return 21;
     } else if((((a2==3) && (((input == 5) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && ((-86 < a4) && (-42 >= a4)) )) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = ((((a4 * 10)/ 4) + -494230) / 5);
      a29 = ((((a29 + -416279) % 29)- -14) - 1);
       a2 = 2;
       return 21;
     } else if(( ((-98 < a0) && (-61 >= a0)) && (((a2==3) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 6))) && ((-86 < a4) && (-42 >= a4)) ))){
      if( -61 < a0 ){
      a0 = ((((a0 + 145127) + 195081) * 10)/ -9);
      a29 = ((((a29 + -380697) % 299978)- -300021) * 1);
       a2 = 5;
      } else{
       a0 = ((((a0 + 207710) - 207755) + 233903) + -233904);
       a29 = ((((a29 % 29)- -14) / 5) + 7);
       a2 = 1;
      } return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-147 < a0) && (-98 >= a0)) && ((a2==2) && ( ((-144 < a29) && (-16 >= a29)) && (input == 5)))))){
      a4 = (((a4 - 7082) / 5) * 5);
      a0 = (((a0 / 5) + -422618) - 20096);
      a29 = ((((a29 * 5) * -6)/ 10) * 5);
       a2 = 5;
       return -1;
     } else if(((((((a2==3) && ((-144 < a29) && (-16 >= a29)) ) || (((a2==2) && 43 < a29 ) || ((a2==3) && a29 <= -144 ))) && (input == 6)) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) )){
      if( ((-147 < a0) && (-98 >= a0)) ){
      a29 = (((((a29 - 0) + 0) + 0) % 299978)+ 300021);
       a2 = 2;
      } else{
       a0 = (((a0 + -433671) / 5) * 5);
       a29 = (((((a29 + 0) % 63)- 80) / 5) + -92);
       a2 = 5;
      } return 22;
     } else if(((a2==3) && ( ((-147 < a0) && (-98 >= a0)) && ((( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 6)) && ((-86 < a4) && (-42 >= a4)) )))){
      a4 = ((((a4 * 5) * 5) * 10)/ 9);
      a0 = ((((a0 / 5) * 78)/ 10) - 489010);
      a29 = ((((a29 * 9)/ 10) - 579679) * 1);
       a2 = 1;
       return -1;
     } else if(((((( ((-16 < a29) && (43 >= a29)) || ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && (input == 1)) && (a2==3)) && ((-86 < a4) && (-42 >= a4)) ) && a0 <= -147 )){
      a4 = (((a4 * 5) + -32547) * 5);
      a0 = ((((a0 / 5) % 18)- 77) - 2);
      a29 = ((((a29 + 577364) % 299928)- 300071) + -2);
       return -1;
     } else if(((a2==2) && (( ((-98 < a0) && (-61 >= a0)) && ((input == 5) && ( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ))){
      a29 = ((((((a29 % 63)- 80) * 5) * 5) % 63)+ -45);
       a2 = 3;
       return -1;
     } else if(( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && ((a2==1) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 5)))))){
      a4 = (((a4 / 5) + -69516) / 5);
      a0 = (((((a0 % 24)- 100) / 5) * 61)/ 10);
      a29 = ((((a29 + 0) % 29)- -25) / 5);
       a2 = 5;
       return -1;
     } else if(((((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 1)) && ((-147 < a0) && (-98 >= a0)) ) && ((-86 < a4) && (-42 >= a4)) ) && (a2==4))){
      a29 = ((((a29 % 299928)- 144) + -181525) + 96009);
       a2 = 1;
       return 26;
     } else if((((((input == 6) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) ) && (a2==5)) && ((-98 < a0) && (-61 >= a0)) )){
      a0 = (((((a0 * 10)/ 4) * 10)/ 9) - 507512);
      a29 = (((((a29 / 5) - 91161) / 5) % 63)- 80);
       return 22;
     } else if((( a0 <= -147 && ((input == 3) && ((( 43 < a29 && (a2==1)) || ( a29 <= -144 && (a2==2))) || ((a2==2) && ((-144 < a29) && (-16 >= a29)) )))) && ((-86 < a4) && (-42 >= a4)) )){
      a0 = ((((a0 - -170985) - 169742) % 24)+ -121);
      a29 = (((((a29 + 0) % 63)- 80) - -45522) + -45522);
       a2 = 1;
       return 21;
     } else if(( -61 < a0 && (((input == 4) && (( ((-144 < a29) && (-16 >= a29)) && (a2==5)) || (((a2==4) && 43 < a29 ) || ((a2==5) && a29 <= -144 )))) && a4 <= -86 ))){
      a0 = ((((a0 % 299926)+ -300072) / 5) - 264648);
      a29 = ((((a29 + 0) % 299928)- 300071) - 0);
       a2 = 1;
       return -1;
     } else if(((a2==4) && ( ((-147 < a0) && (-98 >= a0)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 5)) && ((-86 < a4) && (-42 >= a4)) )))){
      a4 = ((((a4 * 10)/ 4) - 249415) - 6157);
      a0 = ((((a0 * 10)/ 6) / 5) + -139723);
      a29 = ((((a29 + 0) % 299928)- 144) * 1);
       a2 = 1;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-98 < a0) && (-61 >= a0)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 1)) && (a2==4))))){
      a4 = (((a4 + -3562) - 172744) + -275564);
      a0 = (((a0 + -141190) + -295915) / 5);
      a29 = (((((a29 % 63)+ -63) + 12) - -297123) - 297094);
       a2 = 2;
       return -1;
     } else if((((( ((-86 < a4) && (-42 >= a4)) && (input == 5)) && ((-98 < a0) && (-61 >= a0)) ) && (a2==2)) && 43 < a29 )){
      a4 = (((a4 * 5) * 5) + -392587);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==2) && (( 43 < a29 && (input == 1)) && ((-98 < a0) && (-61 >= a0)) )))){
      a4 = ((((a4 * 10)/ 4) * 5) + -539534);
      a0 = (((a0 / 5) + 96252) / 5);
      a29 = (((((a29 / 5) + 107358) * 2) % 63)+ -112);
       return 22;
     } else if(((a2==5) && ( ((-86 < a4) && (-42 >= a4)) && ( ((-98 < a0) && (-61 >= a0)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 6)))))){
      a4 = (((((a4 - -92469) / 5) / 5) * -1)/ 10);
      a29 = (((((a29 % 299978)- -300021) + -100467) / 5) - -264530);
       a2 = 3;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==5) && ( ((-98 < a0) && (-61 >= a0)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 1)))))){
      a4 = ((((a4 + -469882) * 10)/ 9) - 73224);
      a29 = (((a29 / 5) - 149597) + -40814);
       a2 = 3;
       return 22;
     } else if(( ((-147 < a0) && (-98 >= a0)) && (((a2==1) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 1))) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 + -119083) / 5) - 259714);
      a0 = (((((a0 * 15)/ 10) * 10)/ 9) + -14455);
      a29 = (((a29 / 5) + -325971) * 1);
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((((((a2==2) && 43 < a29 ) || ((a2==3) && a29 <= -144 )) || ((a2==3) && ((-144 < a29) && (-16 >= a29)) )) && (input == 3)) && ((-147 < a0) && (-98 >= a0)) ))){
      a4 = (((a4 + -513094) + -85153) - 1529);
      a0 = ((((a0 % 18)- 68) - -263551) - 263549);
      a29 = ((((a29 % 299928)+ -300071) * 1) - 1);
       a2 = 1;
       return -1;
     } else if(( a0 <= -147 && ((((a2==1) && (input == 4)) && ((-86 < a4) && (-42 >= a4)) ) && ((-16 < a29) && (43 >= a29)) ))){
      a4 = (((a4 - 467094) - -9544) * 1);
      a0 = (((a0 - -542155) - -57832) + 130);
      a29 = ((((a29 - 101) / 5) + 573816) - 573849);
       a2 = 2;
       return 26;
     } else if(( ((-16 < a29) && (43 >= a29)) && ( ((-147 < a0) && (-98 >= a0)) && ((a2==2) && ((input == 2) && ((-86 < a4) && (-42 >= a4)) ))))){
      a4 = ((((a4 * 10)/ 4) / 5) - 538737);
      a0 = (((a0 / 5) + -413860) + 135682);
      a29 = (((((a29 + -84) + 101720) * 5) % 63)- 111);
       a2 = 1;
       return -1;
     } else if((((a2==1) && ((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 2)) && a4 <= -86 )) && -61 < a0 )){
      a29 = ((((a29 - -384948) * -1)/ 10) * 5);
       a2 = 2;
       return 21;
     } else if(((a2==4) && (( ((-86 < a4) && (-42 >= a4)) && ((input == 6) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 ))) && ((-147 < a0) && (-98 >= a0)) ))){
      a4 = ((((a4 * 21)/ 10) * 5) / 5);
      a0 = (((((a0 / 5) * 78)/ 10) / 5) + -577837);
      a29 = (((((a29 % 29)+ 13) / 5) + 56090) - 56081);
       a2 = 3;
       return -1;
     } else if((( a0 <= -147 && (((input == 6) && ((-86 < a4) && (-42 >= a4)) ) && (a2==1))) && ((-16 < a29) && (43 >= a29)) )){
      a4 = (((((a4 * 10)/ 4) * 5) - -461601) - 1009325);
      a29 = (((a29 - 154537) * 3) / 5);
       return -1;
     } else if(( a4 <= -86 && (((((a2==3) && a29 <= -144 ) || (((a2==2) && ((-16 < a29) && (43 >= a29)) ) || ( 43 < a29 && (a2==2)))) && (input == 4)) && -61 < a0 ))){
      if((a2==1)){
      a4 = ((((((a4 - 0) % 21)+ -46) / 5) * 59)/ 10);
      a0 = (((((a0 % 24)+ -121) + -1) / 5) + -107);
      a29 = (((((a29 % 299928)+ -300071) * 1) + 266435) - 266436);
       a2 = 4;
      } else{
       a29 = (((((a29 * 9)/ 10) / 5) % 29)- -13);
       a2 = 5;
      } return 26;
     } else if(( ((-144 < a29) && (-16 >= a29)) && ((a2==2) && (( ((-86 < a4) && (-42 >= a4)) && (input == 6)) && ((-147 < a0) && (-98 >= a0)) )))){
      a4 = ((((a4 * 5) - -277812) + 281460) + -586903);
      a0 = (((a0 + -590086) + -3070) * 1);
      a29 = ((((a29 - -298590) % 29)- -11) + 1);
       a2 = 3;
       return -1;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ( ((-147 < a0) && (-98 >= a0)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 3)) && (a2==4))))){
      a0 = (((a0 * 5) * 5) + -226030);
      a29 = (((((a29 % 29)- -31) + -437215) + -100009) + 537223);
       a2 = 5;
       return 22;
     } else if(( ((-86 < a4) && (-42 >= a4)) && ((a2==5) && (((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 1)) && a0 <= -147 )))){
      a4 = ((((((a4 * 10)/ 4) - 219251) + 313842) * -1)/ 10);
      a0 = (((((a0 % 24)+ -114) * 5) % 24)+ -100);
      a29 = (((((a29 % 299978)- -300021) + 0) / 5) - -56448);
       a2 = 4;
       return -1;
     } else if(((( ((-16 < a29) && (43 >= a29)) && ( ((-86 < a4) && (-42 >= a4)) && (input == 2))) && a0 <= -147 ) && (a2==1))){
      a4 = (((a4 / 5) - 423836) / 5);
      a29 = (((a29 / 5) + -232495) + -191727);
       return -1;
     } else if((( ((-147 < a0) && (-98 >= a0)) && (( ((-16 < a29) && (43 >= a29)) && (input == 3)) && (a2==2))) && ((-86 < a4) && (-42 >= a4)) )){
      a0 = (((a0 - 182793) - 17271) + -5363);
      a29 = ((((a29 + -61) - -1) / 5) - 18);
       a2 = 3;
       return -1;
     } else if(((a2==3) && ( ((-98 < a0) && (-61 >= a0)) && ( ((-86 < a4) && (-42 >= a4)) && ((input == 1) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )))))){
      if((a2==4)){
      a4 = ((((a4 + -299499) - 63850) * 10)/ 9);
      a29 = (((a29 / 5) + -305253) * 1);
      } else{
       a4 = ((((((a4 * 21)/ 10) + 263628) / 5) * -1)/ 10);
       a0 = (((((a0 * 10)/ 4) * 5) - -456731) - 842965);
       a29 = ((((a29 - 0) + 0) % 299978)+ 300021);
       a2 = 2;
      } return -1;
     } else if(( a4 <= -86 && (( -61 < a0 && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 6))) && (a2==4)))){
      a0 = (((((a0 + 0) % 299926)+ -300072) + 120564) - 120564);
      a29 = (((((a29 % 299928)- 300071) + 122297) * 1) - 122298);
       a2 = 1;
       return -1;
     } else if(( a4 <= -86 && ( ((-16 < a29) && (43 >= a29)) && (( -61 < a0 && (input == 2)) && (a2==5))))){
      a0 = ((((a0 * 9)/ 10) + 1586) - 558159);
      a29 = ((((a29 - -259897) * 10)/ -9) * 2);
       a2 = 1;
       return -1;
     } else if((((a2==1) && ((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) && (input == 4)) && a4 <= -86 )) && -61 < a0 )){
      a29 = (((a29 / 5) / 5) + 4459);
       a2 = 2;
       return 22;
     } else if((( ((-16 < a29) && (43 >= a29)) && ( a4 <= -86 && ( -61 < a0 && (input == 1)))) && (a2==5))){
      a4 = ((((((a4 % 21)- 54) - 6) / 5) * 49)/ 10);
      a0 = (((((a0 % 24)- 122) - 1) + -244070) + 244070);
      a29 = ((((a29 - 83) * 10)/ 9) + 25);
       a2 = 1;
       return 26;
     } else if(( ((-98 < a0) && (-61 >= a0)) && ( ((-86 < a4) && (-42 >= a4)) && (((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )) && (a2==5))))){
      a4 = (((a4 - 3094) + -312684) - 267039);
      a0 = (((a0 - 345188) * 1) - -345143);
      a29 = (((((a29 % 29)- -13) + 0) - 546639) - -546639);
       a2 = 2;
       return -1;
     }
     return calculate_output2(input);
 }
 int calculate_output2(int input) {
     if(((( ((-86 < a4) && (-42 >= a4)) && ((input == 3) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && (a2==4)) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((((a4 * 10)/ 4) * 10)/ 9) - 397224);
      a0 = (((a0 - 215873) - 88181) - 261733);
      a29 = (((((a29 / 5) + -97608) / 5) % 63)+ -45);
       a2 = 5;
       return -1;
     } else if((((a2==3) && ( ((-86 < a4) && (-42 >= a4)) && ((input == 6) && (( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) )))) && a0 <= -147 )){
      a4 = ((((a4 / 5) + -351472) * 10)/ 9);
      a29 = ((((a29 % 29)+ 13) - -213179) + -213178);
       return -1;
     } else if(( -61 < a0 && ( a4 <= -86 && (( 43 < a29 && (input == 6)) && (a2==3))))){
      a0 = ((((a0 % 299926)- 300072) + -3) + 0);
      a29 = (((a29 / 5) - 393067) + -7867);
       a2 = 1;
       return -1;
     } else if(( a0 <= -147 && ((((((a2==3) && 43 < a29 ) || ((a2==4) && a29 <= -144 )) || ( ((-144 < a29) && (-16 >= a29)) && (a2==4))) && (input == 3)) && ((-86 < a4) && (-42 >= a4)) ))){
      a4 = (((a4 * 5) - 228549) * 2);
      a0 = ((((a0 - -354541) / 5) % 24)+ -121);
      a29 = (((((a29 + 0) % 299928)- 300071) / 5) - 431072);
       a2 = 2;
       return -1;
     } else if(((a2==2) && ( ((-144 < a29) && (-16 >= a29)) && ( ((-86 < a4) && (-42 >= a4)) && ((input == 3) && ((-147 < a0) && (-98 >= a0)) ))))){
      if( ((-98 < a0) && (-61 >= a0)) ){
      } else{
       a0 = (((a0 - 548873) + -8551) - 28143);
       a29 = ((((a29 * 91)/ 10) + -24030) * 5);
       a2 = 3;
      } return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((a2==4) && ((input == 2) && ( ((-16 < a29) && (43 >= a29)) || 43 < a29 )))) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = (((a4 - 284947) + -248704) / 5);
      a0 = (((a0 - 252835) * 2) + -2618);
      a29 = (((((a29 + 0) - 575700) * 1) % 63)- 79);
       a2 = 1;
       return -1;
     } else if((((((input == 4) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) )) && ((-86 < a4) && (-42 >= a4)) ) && (a2==3)) && ((-98 < a0) && (-61 >= a0)) )){
      a4 = (((a4 - 252198) / 5) * 5);
      a0 = (((a0 - 552451) * 1) + -37368);
      a29 = ((((a29 - 0) - -265598) % 299978)- -300021);
       return 26;
     } else if((( ((-98 < a0) && (-61 >= a0)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) && (input == 3)) && ((-86 < a4) && (-42 >= a4)) )) && (a2==3))){
      a29 = ((((a29 % 29)- -28) - 5) - 3);
       return 26;
     } else if(( ((-98 < a0) && (-61 >= a0)) && (((a2==5) && ((input == 5) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ))){
      if( ((-144 < a29) && (-16 >= a29)) ){
      a0 = (((((a0 - 391159) / 5) + 474417) * -1)/ 10);
      a29 = ((((a29 + 321043) - 44655) % 299928)+ -300071);
       a2 = 2;
      } else{
       a4 = ((((a4 * 10)/ 4) / 5) - 33144);
       a0 = ((((a0 / 5) * 123)/ 10) * 5);
       a29 = (((((a29 * 9)/ 10) + 432860) + -149935) - 317631);
       a2 = 3;
      } return 26;
     } else if((( ((-147 < a0) && (-98 >= a0)) && ((input == 2) && (((a2==3) && ((-144 < a29) && (-16 >= a29)) ) || (((a2==2) && 43 < a29 ) || ( a29 <= -144 && (a2==3)))))) && ((-86 < a4) && (-42 >= a4)) )){
      a4 = ((((a4 / 5) / 5) / 5) + -458972);
      a0 = (((((a0 * 15)/ 10) + -283184) * 10)/ 9);
      a29 = (((a29 / 5) - 94068) + -91929);
       a2 = 3;
       return -1;
     } else if((( ((-86 < a4) && (-42 >= a4)) && ((a2==5) && ((( ((-144 < a29) && (-16 >= a29)) || ((-16 < a29) && (43 >= a29)) ) || 43 < a29 ) && (input == 3)))) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = (((a4 - 65033) - 174567) * 2);
      a29 = (((((a29 * 9)/ 10) % 29)- -14) + -1);
       a2 = 2;
       return -1;
     } else if(((((a2==4) && ((input == 6) && ( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ))) && ((-86 < a4) && (-42 >= a4)) ) && ((-147 < a0) && (-98 >= a0)) )){
      a4 = (((a4 + 416590) + -672129) * 2);
      a0 = (((a0 + -331324) + -72862) + -9547);
      a29 = ((((a29 + 0) / 5) / 5) + -415155);
       a2 = 1;
       return -1;
     } else if((((a2==5) && ( ((-86 < a4) && (-42 >= a4)) && ((( a29 <= -144 || ((-144 < a29) && (-16 >= a29)) ) || ((-16 < a29) && (43 >= a29)) ) && (input == 5)))) && a0 <= -147 )){
      a4 = (((a4 * 5) + -29347) + -97982);
      a0 = (((((a0 % 18)+ -74) / 5) * 49)/ 10);
      a29 = ((((a29 - -237985) % 299978)+ 300021) * 1);
       a2 = 3;
       return -1;
     } else if(((a2==4) && ( a0 <= -147 && ( ((-86 < a4) && (-42 >= a4)) && (( ((-16 < a29) && (43 >= a29)) || 43 < a29 ) && (input == 3)))))){
      a4 = (((a4 / 5) + -251576) * 2);
      a0 = (((((a0 + 0) % 24)+ -113) / 5) - 105);
      a29 = (((((a29 / 5) - -479587) - -287) % 29)+ 3);
       a2 = 2;
       return -1;
     }
     return -2;
 }
int input, output;
int main()
{
    output = -1;
    while(1)
    {
        input = __VERIFIER_nondet_int();
  __VERIFIER_assume(input >= 1 && input <= 6);
        output = calculate_output(input);
    }
}
