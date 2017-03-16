
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
  int a24 = 1;
  int a21 = 124;
  int a26 = 222;
  int a14 = -79;
int calculate_output2(int input);
  int a28 = 111;
 int calculate_output(int input) {
 if((((( ((-182 < a14) && (-114 >= a14)) && 217 < a26 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_52: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_35: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_31: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && 217 < a26 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_50: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_46: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && 217 < a26 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_55: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && a26 <= -68 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_9: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && 217 < a26 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_54: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && 217 < a26 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_53: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && 217 < a26 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_49: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_33: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && 217 < a26 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_57: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_37: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_34: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && a26 <= -68 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_4: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_23: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_40: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_25: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_30: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_16: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_20: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && a26 <= -68 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_7: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_26: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && a26 <= -68 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  globalError: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && a26 <= -68 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_13: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && a26 <= -68 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_6: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && 217 < a26 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_59: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && a26 <= -68 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_12: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_41: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_44: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_15: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && 217 < a26 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_51: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_17: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && a26 <= -68 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_10: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_42: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_27: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_19: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && 217 < a26 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_48: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && 217 < a26 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_47: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && 217 < a26 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_58: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && a26 <= -68 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_1: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && a26 <= -68 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_14: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_32: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && a26 <= -68 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_3: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_45: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_22: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_38: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && a26 <= -68 ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_2: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && a26 <= -68 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_0: __VERIFIER_assume(0);
  }
  if((((( a14 <= -182 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && 300 < a28 ) && a21 <= 127 )){
  error_18: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && a26 <= -68 ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_11: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_36: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && a26 <= -68 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_8: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_21: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_24: __VERIFIER_assume(0);
  }
  if((((( ((-182 < a14) && (-114 >= a14)) && a26 <= -68 ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_5: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_43: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && ((124 < a26) && (217 >= a26)) ) && (a24==1)) && a28 <= 37 ) && a21 <= 127 )){
  error_39: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_28: __VERIFIER_assume(0);
  }
  if((((( -84 < a14 && ((-68 < a26) && (124 >= a26)) ) && (a24==1)) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
  error_29: __VERIFIER_assume(0);
  }
  if((((( ((-114 < a14) && (-84 >= a14)) && 217 < a26 ) && (a24==1)) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
  error_56: __VERIFIER_assume(0);
  }
     if((( a21 <= 127 && (( a26 <= -68 && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 3))) && a14 <= -182 )) && (a24==3))){
      a26 = ((((a26 * 9)/ 10) + 599163) - -451);
      a28 = ((((((a28 % 48)- -77) * 5) - -355922) % 48)+ 68);
       a24 = 2;
       return 21;
     } else if((((a24==3) && ( ((-68 < a26) && (124 >= a26)) && ((input == 4) && (( a14 <= -182 && 300 < a28 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 ))))) && a21 <= 127 )){
      a14 = ((((a14 + 0) + 0) % 299909)+ -182);
      a26 = (((a26 + 438366) - -32811) + -5838);
      a28 = ((((a28 + 0) + 0) % 48)- -86);
       a24 = 2;
       return 21;
     } else if(( -84 < a14 && ( a21 <= 127 && ( a26 <= -68 && ((a24==2) && ((input == 6) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))))))){
      a14 = (((((a14 - 0) * 9)/ 10) - 448076) - 127606);
      a28 = (((a28 / 5) / 5) / -5);
       a24 = 1;
       return -1;
     } else if((((a24==2) && ((((input == 3) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )) && a14 <= -182 )){
      a28 = ((((a28 % 299849)- -301) - -68377) - -1150);
       return 21;
     } else if(((a24==3) && ((( a21 <= 127 && (( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 1))) && a14 <= -182 ) && ((-68 < a26) && (124 >= a26)) ))){
      a14 = ((((a14 + 216203) % 14)+ -98) - 2);
      a26 = (((((a26 + -316495) % 46)- -214) - 357980) + 357948);
      a28 = (((((a28 / 5) % 48)- -86) - 283409) - -283409);
       a24 = 2;
       return -1;
     } else if((((((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 4)) && 217 < a26 ) && a21 <= 127 ) && -84 < a14 ) && (a24==1))){
      a14 = ((((a14 % 299909)- 300090) + 0) - 0);
      a26 = (((a26 + -600088) / 5) - 377912);
      a28 = (((a28 + -600036) / 5) / 5);
       return -1;
     } else if(( a21 <= 127 && ((((input == 5) && (( a14 <= -182 && 300 < a28 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))) && 217 < a26 ) && (a24==2)))){
      a14 = (((((((a14 * 9)/ 10) % 33)- 138) * 5) % 33)+ -139);
      a28 = ((((((a28 * 9)/ 10) * 1) - -10862) % 82)- -216);
       a24 = 1;
       return -1;
     } else if((((((input == 1) && ((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 )) || ( -84 < a14 && ((37 < a28) && (134 >= a28)) ))) && ((124 < a26) && (217 >= a26)) ) && (a24==2)) && a21 <= 127 )){
      a14 = ((((a14 * 9)/ 10) - -57076) + -651983);
      a26 = ((((a26 * -6)/ 10) * 5) - 355073);
      a28 = (((a28 / 5) - -352351) - 552393);
       a24 = 1;
       return -1;
     } else if(((( ((-182 < a14) && (-114 >= a14)) && ( a28 <= 37 && ((a24==3) && (input == 5)))) && a26 <= -68 ) && a21 <= 127 )){
      a14 = ((((a14 - 88839) % 14)+ -84) - 6);
      a26 = (((((a26 + 0) % 95)- -32) + 580006) - 579947);
       a24 = 1;
       return -1;
     } else if(( a28 <= 37 && ( ((-68 < a26) && (124 >= a26)) && (( a21 <= 127 && ((input == 2) && (a24==2))) && a14 <= -182 )))){
      a26 = (((a26 - -478961) + -415672) + 258271);
      a28 = ((((a28 % 299849)- -300149) + 2) * 1);
       return 26;
     } else if((((((( ((-68 < a26) && (124 >= a26)) && -84 < a14 ) && 300 < a28 ) || (( ((124 < a26) && (217 >= a26)) && a14 <= -182 ) && a28 <= 37 )) && (input == 2)) && a21 <= 127 ) && (a24==3))){
      a14 = (((((a14 / 5) * 4) * 1) % 14)+ -97);
      a26 = (((a26 - -551133) + -790475) + 800306);
      a28 = ((((a28 % 299849)+ 300149) / 5) + 283071);
       a24 = 1;
       return -1;
     } else if((( a28 <= 37 && ( a21 <= 127 && ((a24==3) && ( ((-114 < a14) && (-84 >= a14)) && (input == 3))))) && ((124 < a26) && (217 >= a26)) )){
      if((a24==2)){
      a14 = (((a14 * -5) + 352770) * 1);
      a26 = (((a26 / 5) - 41) + -2);
      a28 = (((((a28 % 48)- -85) * 5) % 48)- -73);
       a24 = 2;
      } else{
       a14 = ((((a14 - 493422) * 1) * 10)/ 9);
       a26 = (((((a26 * -6)/ 10) + -298400) * 10)/ 9);
       a28 = (((((a28 + 0) * 9)/ 10) * 1) + 544228);
       a24 = 2;
      } return 25;
     } else if(((( a21 <= 127 && ((( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 ))) && (input == 3))) && (a24==2)) && ((124 < a26) && (217 >= a26)) )){
      a14 = ((((a14 % 299909)- 300090) + -1) + -1);
      a26 = (((a26 + -346229) + -71563) - 89097);
      a28 = (((((a28 + 0) - 0) - 0) % 300018)+ -299980);
       a24 = 1;
       return -1;
     } else if((((a24==3) && ( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 2))))) && ((124 < a26) && (217 >= a26)) )){
      a14 = ((((a14 - 581619) - 9324) % 14)+ -99);
      a26 = (((a26 - -238897) - 564200) * 1);
      a28 = ((((a28 - 0) % 82)+ 216) + 0);
       a24 = 2;
       return 21;
     } else if(( ((-68 < a26) && (124 >= a26)) && ( a14 <= -182 && ((((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 4)) && (a24==2)) && a21 <= 127 )))){
      a14 = ((((a14 % 33)- 115) - -1) + -3);
      a26 = (((a26 / 5) + -326056) - -786683);
      a28 = (((a28 / 5) + -202529) / 5);
       return 25;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ((a24==3) && ((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 5)) && a21 <= 127 ))) && ((124 < a26) && (217 >= a26)) )){
      a14 = (((a14 - -71996) - 86067) / 5);
      a26 = (((a26 - -207896) + -580801) + -103307);
      a28 = (((((a28 - 236320) % 82)+ 216) + -112070) + 112072);
       a24 = 1;
       return 25;
     } else if(( ((124 < a26) && (217 >= a26)) && (( a21 <= 127 && (((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 6)) && a14 <= -182 )) && (a24==3)))){
      a26 = (((a26 / 5) - -382315) + -382302);
      a28 = (((((a28 % 299849)+ 301) - -30372) * 10)/ 9);
       a24 = 1;
       return 25;
     } else if(( a26 <= -68 && (( a21 <= 127 && ((a24==2) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 6)))) && a14 <= -182 ))){
      a14 = (((((a14 * 9)/ 10) + -48560) % 14)+ -98);
      a28 = ((((a28 - 0) + 0) % 82)+ 217);
       return 25;
     } else if(( 217 < a26 && (( a21 <= 127 && ((a24==1) && ((input == 6) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )))) && -84 < a14 ))){
      a14 = ((((a14 % 299909)- 300090) + 0) + -1);
      a26 = ((((a26 * 9)/ 10) - 554854) * 1);
      a28 = ((((a28 * 9)/ 10) * 1) - 589002);
       a24 = 2;
       return 25;
     } else if(( a21 <= 127 && ((a24==2) && ( ((124 < a26) && (217 >= a26)) && ( ((-114 < a14) && (-84 >= a14)) && ((input == 2) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))))))){
      a28 = (((((a28 % 48)+ 86) + 1) + -137006) + 137005);
       a24 = 1;
       return -1;
     } else if((((( ((-68 < a26) && (124 >= a26)) && ((input == 6) && ((-182 < a14) && (-114 >= a14)) )) && 300 < a28 ) && (a24==3)) && a21 <= 127 )){
      a14 = ((((a14 + -85645) * 10)/ 9) - 306500);
      a26 = ((((a26 - -243065) % 46)+ 129) - -21);
      a28 = ((((a28 + -267607) + -170138) / 5) - 57279);
       a24 = 1;
       return -1;
     } else if(( ((-68 < a26) && (124 >= a26)) && (((((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 )) || ( ((37 < a28) && (134 >= a28)) && -84 < a14 )) && (input == 2)) && (a24==3)) && a21 <= 127 ))){
      a14 = (((((a14 * 9)/ 10) % 14)+ -98) - 1);
      a26 = ((((a26 / 5) + 512390) * 10)/ -9);
      a28 = ((((a28 % 299849)+ 300149) / 5) - -333944);
       return 21;
     } else if(((a24==2) && (( ((-68 < a26) && (124 >= a26)) && (( -84 < a14 && (input == 3)) && a28 <= 37 )) && a21 <= 127 ))){
      a14 = ((((a14 + -475750) % 299909)- 300090) + -1);
      a26 = (((a26 - 455257) + -62382) - 67001);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && (((a24==3) && ((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 5)) && a14 <= -182 )) && ((124 < a26) && (217 >= a26)) ))){
      a14 = ((((a14 + 599950) + 55) + -503643) - -503583);
      a26 = (((((a26 + -130392) - 369422) - -968854) * -1)/ 10);
      a28 = (((((a28 % 82)+ 159) + 238415) + 42361) + -280772);
       a24 = 1;
       return 21;
     } else if((( a21 <= 127 && ((((a24==2) && (input == 5)) && ((134 < a28) && (300 >= a28)) ) && -84 < a14 )) && ((124 < a26) && (217 >= a26)) )){
      a14 = ((((a14 * 9)/ 10) + -242531) + -341470);
      a26 = ((((a26 / 5) * 5) * 10)/ -9);
      a28 = ((((a28 * 5) - 225145) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if(((((( 217 < a26 && (input == 2)) && a28 <= 37 ) && a21 <= 127 ) && (a24==3)) && ((-182 < a14) && (-114 >= a14)) )){
      if((a24==4)){
      a14 = (((a14 - 409105) + -13315) * 1);
      a26 = (((((a26 - 41044) / 5) * 5) % 95)+ 28);
       a24 = 1;
      } else{
       a14 = (((a14 - 131383) - -375563) + 311393);
       a24 = 1;
      } return -1;
     } else if(( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && (((input == 3) && (( 300 < a28 && a14 <= -182 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))) && (a24==3))))){
      a14 = (((((a14 - -410570) + -47255) - 281823) % 33)- 148);
      a26 = (((a26 - 316562) * 1) + -205758);
      a28 = ((((((a28 * 9)/ 10) - 23937) + 76800) % 48)- -86);
       a24 = 1;
       return -1;
     } else if(( ((134 < a28) && (300 >= a28)) && ((( a21 <= 127 && ((a24==2) && (input == 6))) && -84 < a14 ) && ((124 < a26) && (217 >= a26)) ))){
      a14 = ((((((a14 % 299909)+ -300090) + -2) * 9)/ 10) - 39680);
      a26 = (((a26 / 5) - 192649) + -45568);
      a28 = (((a28 - 492422) * 1) + -79879);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((a24==3) && ( ((124 < a26) && (217 >= a26)) && ((input == 6) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))))) && -84 < a14 )){
      a14 = (((((a14 / 5) - -108920) - 504409) % 14)+ -84);
      a26 = (((a26 * 5) - -397942) + 137140);
      a28 = (((a28 - 0) / 5) + 564252);
       a24 = 1;
       return 21;
     } else if((( a14 <= -182 && ((a24==2) && ( a21 <= 127 && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 5))))) && ((-68 < a26) && (124 >= a26)) )){
      a26 = (((a26 / 5) + -531106) - 53515);
      a28 = ((((a28 + -599998) - 29) - -153488) + -153473);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((( ((124 < a26) && (217 >= a26)) && ((input == 6) && -84 < a14 )) && (a24==3)) && 300 < a28 ))){
      if( -84 < a14 ){
      a14 = (((((a14 % 14)+ -97) / 5) - -319615) + -319696);
      a28 = ((((a28 / -5) + -80052) + 520802) - 508297);
      } else{
       a14 = ((((a14 - 0) + 0) % 14)+ -99);
       a26 = ((((a26 * 10)/ -9) - 495687) + -63837);
       a28 = ((((a28 - 0) / 5) % 48)- -76);
       a24 = 1;
      } return 26;
     } else if(( a21 <= 127 && ((a24==3) && ( a26 <= -68 && (((input == 5) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && a14 <= -182 ))))){
      a14 = (((a14 - -600042) + 70) * 1);
      a26 = ((((a26 % 46)- -176) / 5) - -150);
      a28 = (((((a28 % 48)+ 41) - 112205) / 5) + 22545);
       a24 = 2;
       return 21;
     } else if(( 217 < a26 && ( a28 <= 37 && ( ((-182 < a14) && (-114 >= a14)) && (((input == 3) && (a24==3)) && a21 <= 127 ))))){
      a28 = (((((a28 % 82)- -217) / 5) * 51)/ 10);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((a24==2) && ( -84 < a14 && ( a26 <= -68 && ((input == 3) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))))))){
      a14 = (((a14 / 5) + -522665) * 1);
      a26 = (((((a26 % 299891)+ 300108) * 10)/ 9) * 1);
      a28 = (((((a28 * 9)/ 10) * 1) % 82)+ 210);
       return 26;
     } else if((((a24==2) && ( a21 <= 127 && ((input == 5) && (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 ))))) && a26 <= -68 )){
      a14 = ((((a14 * 9)/ 10) - 573805) + -11573);
      a28 = ((((a28 * 9)/ 10) / 5) + -225074);
       a24 = 1;
       return -1;
     } else if(((a24==3) && (( ((-68 < a26) && (124 >= a26)) && (((input == 6) && ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && a21 <= 127 )) && ((-182 < a14) && (-114 >= a14)) ))){
      a14 = (((a14 - 214083) / 5) / 5);
      a26 = (((a26 - 222685) + -365872) - 4166);
      a28 = (((a28 * 5) / 5) / -5);
       a24 = 1;
       return -1;
     } else if(((( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 1)))) && (a24==2)) && ((-68 < a26) && (124 >= a26)) )){
      a14 = ((((a14 * 10)/ 6) / 5) - 142048);
      a26 = (((a26 - 62191) + -155885) * 2);
      a28 = (((((a28 + 0) * 9)/ 10) - -105728) - 164653);
       return 25;
     } else if(( ((-68 < a26) && (124 >= a26)) && (( ((-114 < a14) && (-84 >= a14)) && ( a21 <= 127 && ((input == 3) && ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && (a24==2)))){
      a14 = ((((a14 * 22)/ 10) / 5) - 595776);
      a26 = (((a26 + -488321) - 72223) * 1);
      a28 = (((a28 + -402973) - -770888) - 446227);
       a24 = 1;
       return -1;
     } else if(((a24==2) && (( ((-114 < a14) && (-84 >= a14)) && ( a26 <= -68 && (( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 4)))) && a21 <= 127 ))){
      a14 = (((a14 / 5) - 46740) - -32098);
      a26 = ((((a26 - 0) % 46)- -199) + -16);
      a28 = ((((a28 * 9)/ 10) + -35946) + -1966);
       return 25;
     } else if(( a14 <= -182 && (( a26 <= -68 && ((a24==3) && ((input == 2) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )))) && a21 <= 127 ))){
      a28 = (((a28 - 599977) - 37) + -3);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((((( a14 <= -182 && a26 <= -68 ) && (a24==3)) && a28 <= 37 ) || ((((a24==2) && ( -84 < a14 && 217 < a26 )) && ((134 < a28) && (300 >= a28)) ) || (((a24==2) && ( -84 < a14 && 217 < a26 )) && 300 < a28 ))) && (input == 3)))){
      a14 = (((a14 / 5) + 364792) * 1);
      a26 = ((((a26 + 0) % 46)- -170) * 1);
      a28 = (((((a28 % 82)- -218) * 5) % 82)+ 203);
       a24 = 2;
       return 25;
     } else if(((((((input == 3) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )) && 217 < a26 ) && (a24==3)) && a14 <= -182 ) && a21 <= 127 )){
      a26 = (((((a26 % 46)+ 142) * 10)/ 9) - 13);
      a28 = ((((((a28 % 48)+ 65) * 9)/ 10) + 182147) - 182155);
       return -1;
     } else if((((a24==2) && ( -84 < a14 && ( ((37 < a28) && (134 >= a28)) && ( ((-68 < a26) && (124 >= a26)) && (input == 4))))) && a21 <= 127 )){
      a14 = (((a14 / 5) / 5) + -231196);
      a26 = ((((a26 + -474360) * 1) * 10)/ 9);
      a28 = ((((a28 * -5) / 5) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if((((( ((124 < a26) && (217 >= a26)) && ((input == 5) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && (a24==2)) && a21 <= 127 ) && a14 <= -182 )){
      a26 = (((a26 + -496055) - -804201) / 5);
      a28 = ((((a28 / 5) / 5) % 48)- -86);
       return 21;
     } else if(( a21 <= 127 && ((a24==3) && ( ((-68 < a26) && (124 >= a26)) && ((input == 6) && (( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 ))))))){
      a14 = ((((a14 % 14)- 95) + 546665) - 546654);
      a26 = (((((a26 % 46)- -171) * 5) % 46)- -162);
      a28 = ((((a28 % 300018)+ -299980) + -1) * 1);
       a24 = 2;
       return 26;
     } else if(( ((-68 < a26) && (124 >= a26)) && ((((( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 ))) && (input == 3)) && a21 <= 127 ) && (a24==3)))){
      a14 = ((((a14 * 9)/ 10) + 41492) + 9550);
      a26 = (((a26 - 542665) + -37833) - 17315);
      a28 = ((((a28 % 299849)- -300149) + 0) * 1);
       return 21;
     } else if(((a24==2) && ( 217 < a26 && (((input == 4) && (( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 )))) && a21 <= 127 )))){
      a14 = ((((a14 % 300041)+ 299957) + 1) + 1);
      a26 = ((((a26 * 9)/ 10) + -586269) - 3434);
      a28 = (((((a28 % 48)+ 85) + 571055) + -459687) - 111367);
       return 25;
     } else if(( a21 <= 127 && ((( ((-114 < a14) && (-84 >= a14)) && ( ((124 < a26) && (217 >= a26)) && (input == 2))) && (a24==3)) && a28 <= 37 ))){
      a14 = (((a14 - 588497) + -6940) + -2646);
      a26 = ((((a26 * -1)/ 10) * 5) / 5);
      a28 = (((((a28 + 0) + 291300) - 156304) % 48)- -86);
       a24 = 1;
       return 26;
     } else if((((((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 4)) && (a24==3)) && a21 <= 127 ) && ((-182 < a14) && (-114 >= a14)) ) && ((124 < a26) && (217 >= a26)) )){
      a14 = (((((a14 % 14)- 96) * 9)/ 10) - 9);
      a26 = ((((a26 * 5) % 95)- 33) + -14);
      a28 = ((((((a28 * 9)/ 10) + 556798) / 5) % 48)+ 60);
       a24 = 2;
       return 21;
     } else if(( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && ((a24==3) && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 1)) && ((-114 < a14) && (-84 >= a14)) ))))){
      if( ((-114 < a14) && (-84 >= a14)) ){
      a26 = ((((a26 + -145116) * 4) - -1143556) - 1159008);
      a28 = ((((a28 * 9)/ 10) / 5) - 377807);
      } else{
       a14 = ((((a14 + -62) / 5) - 455969) + 455834);
       a26 = ((((a26 - -352329) % 46)- -140) - 4);
       a28 = ((((a28 / 5) + 499957) - 632655) - -358378);
       a24 = 1;
      } return 21;
     } else if(((((a24==3) && ( a21 <= 127 && ((input == 1) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )))) && a14 <= -182 ) && 217 < a26 )){
      a28 = ((((a28 + -89948) % 82)+ 218) - -1);
       return -1;
     } else if(( a21 <= 127 && (((((input == 3) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (a24==2)) && ((-68 < a26) && (124 >= a26)) ) && ((-182 < a14) && (-114 >= a14)) ))){
      a26 = (((a26 + 270287) + -547491) / 5);
      a28 = ((((a28 % 48)+ 86) / 5) - -54);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((a24==3) && ((( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )) && (input == 5)))) && ((-68 < a26) && (124 >= a26)) )){
      a14 = (((((a14 + 299726) % 14)+ -99) - 237902) - -237901);
      a28 = (((((a28 * 9)/ 10) % 300018)- 299980) + -1);
       a24 = 1;
       return -1;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ((((input == 6) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && a21 <= 127 ) && (a24==2))) && ((124 < a26) && (217 >= a26)) )){
      if((a24==3)){
      a14 = ((((a14 / 5) * 5) * 15)/ 10);
      a26 = (((a26 - 276769) + -61164) + -111264);
      a28 = ((((a28 % 299849)+ 300149) - 0) + 2);
       a24 = 3;
      } else{
       a26 = (((((a26 * 10)/ -9) * 5) * 10)/ 9);
       a28 = ((((a28 % 299849)- -300149) - 0) - -2);
      } return 21;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ((((a24==3) && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 4))) && a26 <= -68 ) && a21 <= 127 ))){
      a14 = (((((a14 * 16)/ 10) * 10)/ 9) + -499692);
      a26 = (((((a26 - -81213) * 1) - -413395) % 46)+ 170);
      a28 = (((a28 / 5) - -154851) * 2);
       a24 = 2;
       return 21;
     } else if((((a24==2) && (((input == 2) && ((( ((134 < a28) && (300 >= a28)) && ((-182 < a14) && (-114 >= a14)) ) || ( ((-182 < a14) && (-114 >= a14)) && 300 < a28 )) || ( a28 <= 37 && ((-114 < a14) && (-84 >= a14)) ))) && a21 <= 127 )) && ((-68 < a26) && (124 >= a26)) )){
      a14 = (((((a14 % 14)+ -87) - 532544) + 608349) - 75814);
      a26 = ((((((a26 - 325255) % 46)- -173) / 5) * 55)/ 10);
      a28 = ((((a28 % 300018)+ -299980) - 1) / 5);
       return 21;
     } else if((((( -84 < a14 && ((input == 2) && a21 <= 127 )) && a26 <= -68 ) && (a24==2)) && ((37 < a28) && (134 >= a28)) )){
      a14 = ((((a14 % 299909)- 300090) / 5) + -207775);
      a28 = (((a28 - 263388) - -80788) * 3);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((a24==3) && ((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 2)) && ((-182 < a14) && (-114 >= a14)) ))) && a26 <= -68 )){
      a14 = (((a14 - 565984) * 1) * 1);
      a28 = ((((a28 * 9)/ 10) * -1) + -40435);
       a24 = 1;
       return -1;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ( a21 <= 127 && (((input == 3) && ((-68 < a26) && (124 >= a26)) ) && 300 < a28 ))) && (a24==2))){
      a14 = (((a14 / 5) + 161937) - -152247);
      a26 = (((((a26 % 46)- -170) / 5) / 5) - -189);
      a28 = (((((a28 / 5) + -421018) - -430946) % 82)+ 186);
       return 25;
     } else if((( ((134 < a28) && (300 >= a28)) && ( a21 <= 127 && (((a24==2) && (input == 1)) && ((124 < a26) && (217 >= a26)) ))) && -84 < a14 )){
      a14 = ((((((a14 % 14)- 98) * 1) * 5) % 14)+ -91);
      a26 = ((((a26 - 247436) - -632553) - -109715) - 495006);
      a28 = ((((a28 + 574624) / 5) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if(((((a24==2) && ((input == 6) && (( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )))) && a26 <= -68 ) && a21 <= 127 )){
      a14 = (((((a14 - -113223) + -74409) * 1) % 299909)+ -300090);
      a26 = ((((a26 % 95)+ 39) + 32) - 25);
      a28 = (((((a28 * 9)/ 10) * 1) % 300018)+ -299980);
       return 21;
     } else if((((((a24==2) && ( ((134 < a28) && (300 >= a28)) && (input == 2))) && 217 < a26 ) && a14 <= -182 ) && a21 <= 127 )){
      if( a21 <= 127 ){
      a14 = (((a14 - -567872) - -32231) + 52);
      a28 = (((((a28 % 48)+ 43) - -505188) / 5) + -100951);
      } else{
       a26 = (((((a26 - 0) * 9)/ 10) * -4)/ 10);
      } return 25;
     } else if(( a28 <= 37 && (( 217 < a26 && ((a24==3) && ((input == 3) && a14 <= -182 ))) && a21 <= 127 ))){
      if((a24==1)){
      a14 = ((((a14 + 0) % 33)- 116) - -1);
      a26 = ((((a26 / 5) + -369210) - -303100) + -113132);
      a28 = ((((a28 / 5) / 5) % 48)+ 85);
       a24 = 1;
      } else{
       a14 = ((((a14 % 33)- 145) - -3) - -16);
       a26 = ((((a26 + 0) - 461723) % 46)- -170);
       a28 = ((((a28 % 299849)- -300149) + 2) * 1);
      } return 26;
     } else if(( a21 <= 127 && (((a24==3) && (((input == 4) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && a14 <= -182 )) && a26 <= -68 ))){
      a14 = (((a14 + 599951) - -104) - -51);
      a26 = (((((a26 % 46)- -197) - 513053) - 51289) + 564358);
      a28 = ((((((a28 % 299849)- -301) - 451296) + -84365) * -1)/ 10);
       a24 = 2;
       return 21;
     } else if((( a21 <= 127 && ( ((124 < a26) && (217 >= a26)) && ( a14 <= -182 && ((input == 1) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))))) && (a24==2))){
      if( 399 < a21 ){
      a14 = (((a14 / 5) / -5) * 5);
      a26 = ((((a26 + -297043) * -1)/ 10) * 5);
      a28 = ((((a28 % 48)+ 71) * 5) / 5);
      } else{
       a26 = ((((a26 - -282890) * 10)/ -9) - 210427);
       a28 = (((((a28 / 5) % 82)+ 136) / 5) + 130);
      } return 25;
     } else if((((a24==2) && ( a21 <= 127 && ((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 6)) && a14 <= -182 ))) && ((-68 < a26) && (124 >= a26)) )){
      a26 = (((a26 - -173811) - 692406) / 5);
      a28 = ((((a28 / -5) + -419853) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if(((((((a24==3) && (input == 5)) && 217 < a26 ) && a28 <= 37 ) && a14 <= -182 ) && a21 <= 127 )){
      a14 = ((((a14 - 0) % 33)+ -129) + 14);
      a26 = ((((((a26 % 46)- -149) * 10)/ 9) * 9)/ 10);
      a28 = ((((a28 % 48)- -85) - 543532) + 543533);
       a24 = 2;
       return 21;
     } else if(((( a21 <= 127 && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 2)) && (a24==3))) && ((-68 < a26) && (124 >= a26)) ) && a14 <= -182 )){
      a26 = (((a26 * 5) - 235208) * 2);
      a28 = ((((a28 % 82)- -218) - 2) + 3);
       a24 = 2;
       return 25;
     } else if(( 217 < a26 && (((((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 4)) && a21 <= 127 ) && (a24==2)) && ((-114 < a14) && (-84 >= a14)) ))){
      a14 = (((a14 * 5) + -508814) - 38899);
      a26 = ((((((a26 % 95)+ 10) * 5) + -55692) % 95)+ 55);
      a28 = (((((a28 * 9)/ 10) % 48)+ 85) + 0);
       a24 = 1;
       return -1;
     } else if((((a24==3) && ( ((-182 < a14) && (-114 >= a14)) && ( ((-68 < a26) && (124 >= a26)) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 2))))) && a21 <= 127 )){
      a14 = ((((a14 - -176605) % 14)+ -99) * 1);
      a26 = (((((a26 % 46)+ 171) + -599345) + 810493) - 211147);
      a28 = ((((a28 - -177828) / 5) / 5) + -509888);
       a24 = 2;
       return 25;
     } else if((((( ((-114 < a14) && (-84 >= a14)) && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 5))) && a26 <= -68 ) && a21 <= 127 ) && (a24==2))){
      a14 = (((a14 + 307179) + -355622) * 5);
      a28 = (((a28 / 5) * 4) + -35670);
       a24 = 1;
       return -1;
     } else if(((((a24==2) && ((( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )) && (input == 5))) && a21 <= 127 ) && a26 <= -68 )){
      a14 = (((((a14 + 2403) % 299909)+ -300090) + 492418) + -492418);
      a28 = (((((a28 % 300018)+ -299980) + 264820) / 5) + -289566);
       a24 = 1;
       return -1;
     } else if(( ((37 < a28) && (134 >= a28)) && ( a21 <= 127 && ((( 217 < a26 && (input == 3)) && a14 <= -182 ) && (a24==2))))){
      a14 = (((a14 / -5) + 209000) + 129249);
      a26 = (((((a26 - 390752) - -126915) / 5) % 95)+ 29);
      a28 = (((a28 - -390078) * 1) + 42716);
       a24 = 1;
       return -1;
     } else if(((( ((134 < a28) && (300 >= a28)) && ( a21 <= 127 && ( -84 < a14 && (input == 2)))) && ((-68 < a26) && (124 >= a26)) ) && (a24==3))){
      if( ((-68 < a26) && (124 >= a26)) ){
      a14 = ((((a14 + -140752) * 1) % 299909)+ -300090);
      a26 = (((a26 + -452663) - 74934) - 3809);
      a28 = (((((a28 * 10)/ 4) + 492713) - 674594) + 613189);
       a24 = 1;
      } else{
       a14 = (((((a14 / 5) % 14)+ -97) / 5) - 81);
       a24 = 1;
      } return 21;
     } else if(((a24==3) && (( ((124 < a26) && (217 >= a26)) && ( -84 < a14 && ( 300 < a28 && (input == 3)))) && a21 <= 127 ))){
      a14 = (((((a14 % 299909)- 300090) - 1) / 5) + -14610);
      a26 = ((((a26 / 5) + 577082) * 1) - 577130);
      a28 = (((((a28 - 0) - 165728) * 1) % 48)- -86);
       return 21;
     } else if((((((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 3)) && a26 <= -68 ) && (a24==2)) && a21 <= 127 ) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = (((a14 + -319610) + -181575) - 2782);
      a28 = ((((a28 / -5) * 10)/ 9) + -90894);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( a21 <= 127 && (((input == 5) && ((( ((134 < a28) && (300 >= a28)) && ((-182 < a14) && (-114 >= a14)) ) || ( 300 < a28 && ((-182 < a14) && (-114 >= a14)) )) || ( ((-114 < a14) && (-84 >= a14)) && a28 <= 37 ))) && ((-68 < a26) && (124 >= a26)) )))){
      if( ((-114 < a14) && (-84 >= a14)) ){
      a14 = ((((a14 % 14)+ -91) - -106187) - 106193);
      a26 = ((((a26 * 5) - -172324) - 434184) - -336187);
      a28 = (((((a28 % 82)+ 218) * 5) % 82)+ 173);
      } else{
       a14 = (((a14 * 5) - 64405) - -60802);
       a26 = (((a26 * 5) + 139314) * 4);
       a28 = ((((((a28 % 48)+ 86) - -1) * 5) % 48)+ 67);
      } return 25;
     } else if(( a21 <= 127 && (( ((-114 < a14) && (-84 >= a14)) && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 1)) && a26 <= -68 )) && (a24==2)))){
      a14 = (((a14 * 5) * 5) + -510943);
      a28 = ((((a28 * 9)/ 10) * 1) - 32652);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((( 300 < a28 && ( -84 < a14 && ((-68 < a26) && (124 >= a26)) )) || (( ((124 < a26) && (217 >= a26)) && a14 <= -182 ) && a28 <= 37 )) && (input == 5))) && (a24==3))){
      if( a14 <= -182 ){
      a14 = (((((a14 % 14)+ -97) * 1) + 6540) - 6542);
      a26 = (((((a26 % 95)- -27) + 0) + 41255) - 41253);
      a28 = ((((a28 % 300018)+ -299980) - 2) - 0);
      } else{
       a14 = ((((((a14 % 299909)+ -300090) / 5) - -237591) * -1)/ 10);
       a26 = ((((a26 % 95)+ 27) - -312425) + -312422);
       a28 = (((((a28 * 9)/ 10) * 1) % 299849)+ 300149);
       a24 = 2;
      } return -1;
     } else if(((a24==3) && ( ((-114 < a14) && (-84 >= a14)) && ( a28 <= 37 && (((input == 5) && a21 <= 127 ) && ((124 < a26) && (217 >= a26)) ))))){
      a28 = ((((a28 / 5) - -260312) % 82)+ 208);
       a24 = 2;
       return -1;
     } else if(( a21 <= 127 && ( ((124 < a26) && (217 >= a26)) && ((a24==2) && (((input == 3) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && ((-182 < a14) && (-114 >= a14)) ))))){
      a26 = (((((a26 / 5) * 5) - -151147) * -1)/ 10);
      a28 = ((((((a28 * 9)/ 10) - 286611) + 235636) % 48)- -85);
       a24 = 3;
       return 21;
     } else if(((((a24==3) && (((input == 2) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && ((-114 < a14) && (-84 >= a14)) )) && a21 <= 127 ) && ((-68 < a26) && (124 >= a26)) )){
      if( a14 <= -182 ){
      a14 = ((((a14 - 190298) * 10)/ 9) - 210885);
      a28 = ((((((a28 % 48)- -85) * 5) - 461112) % 48)- -123);
       a24 = 1;
      } else{
       a14 = ((((a14 * 22)/ 10) / 5) - 113110);
       a26 = (((a26 * 5) - 491392) / 5);
       a28 = (((((a28 - -407954) % 299849)+ 300149) / 5) + 17022);
       a24 = 1;
      } return 25;
     } else if(((a24==2) && (( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && ((input == 4) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )))) && ((-68 < a26) && (124 >= a26)) ))){
      if( a14 <= -182 ){
      a14 = ((((a14 * 5) % 14)- 99) + 7);
      a26 = (((a26 + -279175) - -550480) - -112957);
      a28 = (((((a28 % 48)- -86) * 1) - 596800) + 596800);
      } else{
       a14 = (((a14 + -515263) * 1) - 75117);
       a26 = (((a26 + 364987) - -93136) - 60628);
       a28 = ((((a28 / 5) % 48)+ 85) - 0);
      } return 21;
     } else if(( a26 <= -68 && ( a21 <= 127 && ((a24==2) && ((( a14 <= -182 && 300 < a28 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )) && (input == 2)))))){
      a14 = (((((a14 % 33)+ -142) - -4) + -282598) - -282592);
      a26 = ((((a26 % 95)- -83) + -28) + 38);
      a28 = ((((a28 + 0) / 5) % 48)+ 85);
       return 26;
     } else if((((( ((37 < a28) && (134 >= a28)) && ( ((-68 < a26) && (124 >= a26)) && (input == 6))) && -84 < a14 ) && (a24==2)) && a21 <= 127 )){
      a14 = ((((((a14 % 14)- 99) + -1) * 5) % 14)+ -90);
      a26 = (((((a26 % 46)+ 170) / 5) - -254664) - 254546);
      a28 = (((a28 * -5) + -171377) - 183523);
       return 21;
     } else if((((( -84 < a14 && ( a21 <= 127 && (input == 3))) && a26 <= -68 ) && 300 < a28 ) && (a24==3))){
      a14 = (((((a14 % 33)+ -146) / 5) / 5) + -147);
      a28 = ((((a28 - 393264) % 48)- -86) * 1);
       a24 = 1;
       return -1;
     } else if(((a24==3) && ( ((-68 < a26) && (124 >= a26)) && ( a21 <= 127 && ((( -84 < a14 && ((37 < a28) && (134 >= a28)) ) || (( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 ))) && (input == 1)))))){
      a14 = ((((a14 % 299909)- 300090) - 2) + 0);
      a28 = (((((a28 * 9)/ 10) % 299849)+ 300149) + 1);
       a24 = 1;
       return 21;
     } else if(( ((-68 < a26) && (124 >= a26)) && ( ((37 < a28) && (134 >= a28)) && ((((input == 5) && a21 <= 127 ) && (a24==2)) && -84 < a14 )))){
      a14 = ((((a14 % 299909)+ -300090) - 2) - 0);
      a26 = (((((a26 + -82778) * 10)/ 9) * 10)/ 9);
      a28 = (((a28 / -5) * 5) - 280617);
       a24 = 1;
       return -1;
     } else if((((a24==3) && ((((input == 4) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && ((-68 < a26) && (124 >= a26)) ) && ((-114 < a14) && (-84 >= a14)) )) && a21 <= 127 )){
      a14 = (((a14 - -517743) / 5) * 5);
      a26 = ((((a26 / 5) / 5) + 473437) + -473245);
      a28 = (((((a28 / 5) - -104086) + 278547) % 82)- -142);
       a24 = 2;
       return 25;
     } else if(((((((input == 6) && -84 < a14 ) && a26 <= -68 ) && (a24==3)) && a21 <= 127 ) && 300 < a28 )){
      a14 = ((((a14 % 14)- 98) - -253917) - 253917);
      a26 = ((((a26 + 0) % 46)- -187) - 16);
      a28 = (((((a28 % 82)- -183) + 18) + 308875) - 308898);
       a24 = 2;
       return 26;
     } else if(( a21 <= 127 && ((a24==2) && ( ((124 < a26) && (217 >= a26)) && (((input == 4) && a28 <= 37 ) && ((-182 < a14) && (-114 >= a14)) ))))){
      a14 = (((a14 * -5) - 313798) - -720257);
      a28 = (((((a28 - -127421) * 1) + -12489) % 299849)+ 300149);
       a24 = 1;
       return -1;
     } else if(( ((-114 < a14) && (-84 >= a14)) && ((( a26 <= -68 && ((input == 5) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )))) && (a24==3)) && a21 <= 127 ))){
      a14 = (((a14 - -175856) + 95063) * 2);
      a28 = (((((a28 * 9)/ 10) - -555628) - 480983) + 470839);
       a24 = 2;
       return 26;
     } else if(((((a24==2) && ((input == 6) && (( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 )))) && a21 <= 127 ) && a26 <= -68 )){
      a14 = (((((a14 + 0) * 9)/ 10) % 14)- 97);
      a26 = ((((a26 / 5) % 46)- -174) * 1);
      a28 = ((((a28 % 48)+ 85) * 1) + 2);
       return 26;
     } else if(( a21 <= 127 && ( a26 <= -68 && ((a24==3) && ( -84 < a14 && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 6))))))){
      a14 = ((((a14 - 0) % 299909)+ -300090) - 0);
      a28 = (((a28 + -428573) + -33374) - 11398);
       a24 = 1;
       return -1;
     } else if((( a14 <= -182 && (( ((37 < a28) && (134 >= a28)) && ((input == 5) && (a24==2))) && 217 < a26 )) && a21 <= 127 )){
      if( 300 < a28 ){
      a26 = (((a26 - 600207) * 1) + -2);
      a28 = ((((a28 * 10)/ 1) / 5) - -336880);
       a24 = 3;
      } else{
       a14 = ((((a14 * 9)/ 10) + 580904) - -7448);
       a26 = (((a26 + -600122) - 27) - 4);
      } return -1;
     } else if((((a24==2) && ( a21 <= 127 && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 5)) && 217 < a26 ))) && ((-114 < a14) && (-84 >= a14)) )){
      if( ((124 < a26) && (217 >= a26)) ){
      a14 = (((a14 + -574990) * 1) * 1);
      a26 = (((a26 + -600175) + -8) + -24);
      a28 = ((((a28 % 299849)- -300149) - -2) - 0);
       a24 = 3;
      } else{
       a14 = ((((a14 / -5) + 322149) * 10)/ 9);
       a26 = (((((a26 * 9)/ 10) * 1) / 5) + -214006);
       a28 = ((((a28 - -51778) + 332066) % 48)+ 86);
      } return -1;
     } else if((( a21 <= 127 && ( a14 <= -182 && (( ((134 < a28) && (300 >= a28)) && (input == 3)) && (a24==2)))) && 217 < a26 )){
      a26 = ((((a26 * 9)/ 10) + -553324) + -9063);
      a28 = (((a28 / 5) - -220684) / -5);
       a24 = 1;
       return -1;
     } else if(((((a24==2) && ( a28 <= 37 && ( ((-68 < a26) && (124 >= a26)) && (input == 4)))) && -84 < a14 ) && a21 <= 127 )){
      a14 = (((((a14 % 299909)- 300090) - -339514) + -230857) + -108658);
      a26 = ((((a26 + 180288) * -1)/ 10) + -226743);
       a24 = 1;
       return -1;
     } else if(((((a24==3) && ( ((124 < a26) && (217 >= a26)) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 6)))) && a21 <= 127 ) && ((-182 < a14) && (-114 >= a14)) )){
      a28 = (((((a28 - -91867) % 300018)- 299980) + 145673) - 145674);
       return -1;
     } else if(( a21 <= 127 && (( a14 <= -182 && ( ((124 < a26) && (217 >= a26)) && ((input == 6) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )))) && (a24==2)))){
      a26 = (((((a26 * -6)/ 10) / 5) - -252695) - 326755);
      a28 = (((a28 / 5) / 5) + -596739);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && (( ((-182 < a14) && (-114 >= a14)) && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 1))) && ((124 < a26) && (217 >= a26)) )) && (a24==2))){
      a26 = (((((((a26 * 18)/ 10) * 10)/ 9) - 386356) * -1)/ 10);
      a28 = (((((a28 % 82)+ 206) - 61) - -277865) - 277844);
       return 21;
     } else if(((( ((-68 < a26) && (124 >= a26)) && ( ((-182 < a14) && (-114 >= a14)) && ((input == 5) && ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && (a24==3)) && a21 <= 127 )){
      a14 = ((((a14 * 10)/ 6) - 497311) / 5);
      a26 = (((((a26 - -387677) / 5) + -267123) * -1)/ 10);
      a28 = ((((a28 - 83359) + -47254) % 48)+ 95);
       a24 = 2;
       return 21;
     } else if(( a21 <= 127 && (((((input == 4) && a26 <= -68 ) && (a24==3)) && -84 < a14 ) && 300 < a28 ))){
      a14 = (((((a14 + 0) - 549378) * 1) % 299909)- 300090);
      a26 = ((((a26 % 299891)- -300108) / 5) - -94227);
      a28 = (((((a28 + -577276) % 48)- -85) - 392664) - -392664);
       a24 = 2;
       return 21;
     } else if(((a24==2) && (( ((-182 < a14) && (-114 >= a14)) && ( a26 <= -68 && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 6)))) && a21 <= 127 ))){
      if( ((37 < a28) && (134 >= a28)) ){
      a14 = (((a14 - 190584) + 372103) - 729880);
      a28 = (((a28 - 208015) + -392012) + -8);
       a24 = 3;
      } else{
       a14 = ((((a14 + -598168) % 14)+ -94) + -5);
       a26 = (((((a26 + 148735) * 1) / 5) % 95)+ 29);
       a28 = (((a28 / 5) * 4) - -53558);
      } return 26;
     } else if(( 217 < a26 && ( a28 <= 37 && ((((input == 4) && a21 <= 127 ) && a14 <= -182 ) && (a24==3))))){
      a14 = ((((a14 % 33)- 121) / 5) + -119);
      a26 = (((a26 - 600198) - 3) + -14);
       return -1;
     } else if((( -84 < a14 && ( a21 <= 127 && ( a28 <= 37 && ((input == 1) && ((-68 < a26) && (124 >= a26)) )))) && (a24==2))){
      a14 = ((((a14 % 299909)+ -300090) + -2) - 0);
      a26 = (((a26 / 5) / 5) - 598152);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( a28 <= 37 && ((( ((-114 < a14) && (-84 >= a14)) && (input == 4)) && ((124 < a26) && (217 >= a26)) ) && (a24==3))))){
      if( a26 <= -68 ){
      a26 = (((((a26 + 79833) + 426275) + -1000258) * -1)/ 10);
      a28 = ((((a28 % 48)- -85) + 584898) + -584897);
       a24 = 1;
      } else{
       a14 = (((((a14 * 10)/ 4) - 35718) * 10)/ 9);
       a26 = ((((a26 + -387213) - -482378) - 452794) - -824057);
       a28 = ((((a28 % 82)- -216) - -1) + 2);
      } return -1;
     } else if(((( a28 <= 37 && (( a21 <= 127 && (input == 5)) && ((124 < a26) && (217 >= a26)) )) && ((-182 < a14) && (-114 >= a14)) ) && (a24==2))){
      a14 = ((((a14 / 5) * 83)/ 10) + -324840);
      a26 = ((((a26 + 123598) / 5) * 10)/ 9);
      a28 = ((((a28 % 48)+ 86) - -1) - 2);
       return 26;
     } else if(((a24==2) && (( ((-68 < a26) && (124 >= a26)) && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 2)) && ((-114 < a14) && (-84 >= a14)) )) && a21 <= 127 ))){
      a26 = ((((a26 % 46)+ 170) + 0) - -1);
      a28 = (((((((a28 % 82)+ 157) * 9)/ 10) / 5) * 49)/ 10);
       return 25;
     } else if((( a21 <= 127 && ((( a28 <= 37 && (input == 2)) && (a24==2)) && ((124 < a26) && (217 >= a26)) )) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = (((a14 + -83189) * 5) - 109971);
      a26 = (((a26 + 352826) + 179334) + 34059);
      a28 = (((a28 / 5) / 5) + 159465);
       a24 = 1;
       return -1;
     } else if((( a26 <= -68 && ((a24==2) && ((( a14 <= -182 && 300 < a28 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) )) && (input == 3)))) && a21 <= 127 )){
      a14 = ((((a14 % 299909)+ -182) - 160118) + -63249);
      a28 = ((((a28 % 300018)- 299980) + 182601) + -182602);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((input == 6) && ((( ((134 < a28) && (300 >= a28)) && ((a24==2) && ( -84 < a14 && 217 < a26 ))) || ( 300 < a28 && ((a24==2) && ( 217 < a26 && -84 < a14 )))) || (((a24==3) && ( a26 <= -68 && a14 <= -182 )) && a28 <= 37 ))))){
      a14 = ((((a14 + 0) % 300041)- -299957) * 1);
      a26 = (((((a26 % 46)- -171) / 5) - -272225) - 272089);
      a28 = ((((a28 % 48)- -86) + -1) + 0);
       a24 = 2;
       return 21;
     } else if(( 217 < a26 && ((((a24==3) && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 4))) && a14 <= -182 ) && a21 <= 127 ))){
      a14 = (((((a14 / 5) + -108885) * 2) % 33)+ -142);
      a26 = ((((a26 + 0) - 0) % 95)- 29);
      a28 = (((((a28 % 48)- -71) - 59820) - 43993) - -103819);
       a24 = 1;
       return 21;
     } else if(((((((input == 3) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && a26 <= -68 ) && a21 <= 127 ) && ((-114 < a14) && (-84 >= a14)) ) && (a24==3))){
      a14 = ((((a14 / -5) + 306231) * 10)/ 9);
      a28 = (((((a28 % 82)- -218) / 5) * 10)/ 2);
       a24 = 2;
       return -1;
     } else if(( a14 <= -182 && ((((a24==2) && ((input == 2) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && a26 <= -68 ) && a21 <= 127 ))){
      a28 = ((((a28 % 299849)- -300149) - 506398) - -506401);
       return 26;
     } else if(((( 300 < a28 && (((input == 2) && ((-182 < a14) && (-114 >= a14)) ) && a21 <= 127 )) && ((-68 < a26) && (124 >= a26)) ) && (a24==3))){
      a14 = (((a14 - 487149) * 1) / 5);
      a26 = (((a26 - -427158) + 168406) * 1);
       a24 = 1;
       return -1;
     } else if(((a24==2) && (( a21 <= 127 && ((input == 5) && (( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 ))))) && 217 < a26 ))){
      a14 = ((((a14 - 526766) - -474026) % 299909)+ -300090);
      a26 = (((a26 + -77282) - 317152) - 205692);
      a28 = (((((a28 - 0) * 9)/ 10) / 5) + -289060);
       a24 = 1;
       return -1;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ( ((-68 < a26) && (124 >= a26)) && ((((input == 4) && ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && a21 <= 127 ) && (a24==3))))){
      a14 = ((((a14 * 10)/ 6) * 5) - 534789);
      a26 = (((a26 + -583423) - 746) + -10786);
      a28 = (((a28 + -210158) / 5) - 502446);
       a24 = 1;
       return -1;
     } else if((( ((-114 < a14) && (-84 >= a14)) && (( ((124 < a26) && (217 >= a26)) && ((input == 1) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))) && (a24==2))) && a21 <= 127 )){
      a26 = (((a26 * 5) - -358448) / 5);
      a28 = ((((a28 % 299849)+ 300149) - -2) - 0);
       return 25;
     } else if((( ((-68 < a26) && (124 >= a26)) && ((((input == 6) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && a21 <= 127 ) && (a24==3))) && a14 <= -182 )){
      a26 = (((a26 / 5) - 312781) / 5);
      a28 = (((((a28 % 82)+ 218) - 165719) - 412947) - -578665);
       a24 = 2;
       return -1;
     } else if((( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && ((a24==3) && ((input == 1) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))))) && ((124 < a26) && (217 >= a26)) )){
      a26 = (((((a26 / 5) * 9)/ 10) + -168283) - -168323);
      a28 = ((((a28 % 300018)- 299980) / 5) - 126527);
       a24 = 2;
       return 21;
     } else if(((a24==2) && ( 217 < a26 && ( a21 <= 127 && ((input == 6) && (( 300 < a28 && a14 <= -182 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))))))){
      a14 = (((((a14 * 9)/ 10) / 5) + 19843) - -250158);
      a26 = ((((a26 - 156646) + 132807) + 16180) - 592439);
      a28 = (((((a28 % 299849)- -300149) - -1) / 5) - -150493);
       return 26;
     } else if((( -84 < a14 && (((a24==3) && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 1))) && a21 <= 127 )) && ((124 < a26) && (217 >= a26)) )){
      if((a24==1)){
      a14 = (((((a14 + -267597) % 299909)+ -300090) / 5) + -232598);
      a28 = (((((a28 % 299849)- -300149) * 1) / 5) - -364010);
       a24 = 2;
      } else{
       a26 = (((((a26 * 5) * 10)/ 9) - 550549) - -1020629);
       a28 = ((((a28 * 9)/ 10) + 385814) + -431177);
       a24 = 1;
      } return -1;
     } else if(((( 217 < a26 && (((a24==3) && (input == 2)) && a14 <= -182 )) && a21 <= 127 ) && a28 <= 37 )){
      a26 = ((((((a26 % 95)- -14) + 20350) * 5) % 95)- 31);
      a28 = ((((a28 % 299849)- -300149) - 520507) + 520509);
       a24 = 1;
       return 25;
     } else if(((((a24==3) && ( a21 <= 127 && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 2)))) && ((124 < a26) && (217 >= a26)) ) && ((-182 < a14) && (-114 >= a14)) )){
      a26 = ((((a26 * -1)/ 10) * 5) / 5);
      a28 = ((((a28 % 299849)+ 301) * 1) * 1);
       a24 = 1;
       return 21;
     } else if(( ((-68 < a26) && (124 >= a26)) && (( a21 <= 127 && (((input == 6) && (a24==2)) && a28 <= 37 )) && -84 < a14 ))){
      a26 = (((((a26 - 251433) * 2) * 1) % 46)+ 211);
      a28 = ((((a28 % 82)- -217) - 1) + 0);
       return 21;
     } else if(( ((124 < a26) && (217 >= a26)) && ((a24==3) && ( -84 < a14 && (( 300 < a28 && (input == 2)) && a21 <= 127 ))))){
      a26 = ((((a26 * 5) % 95)- -15) / 5);
      a28 = (((a28 + -485617) + -2487) - 112187);
       a24 = 1;
       return -1;
     } else if(((( a28 <= 37 && (((a24==3) && (input == 3)) && a26 <= -68 )) && a21 <= 127 ) && -84 < a14 )){
      a26 = ((((((a26 * 9)/ 10) % 46)+ 196) - 131059) + 131066);
      a28 = ((((a28 % 82)- -216) * 5) / 5);
       a24 = 2;
       return 26;
     } else if((( ((-182 < a14) && (-114 >= a14)) && ((a24==3) && ( a21 <= 127 && ((input == 3) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))))) && ((124 < a26) && (217 >= a26)) )){
      a14 = ((((a14 + 113328) + -340798) % 14)+ -85);
      a26 = ((((a26 - 170) - -158472) - 755026) - -596573);
      a28 = (((((a28 % 48)+ 85) / 5) / 5) + 60);
       a24 = 2;
       return -1;
     } else if(((((((input == 4) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && ((124 < a26) && (217 >= a26)) ) && (a24==2)) && a21 <= 127 ) && ((-114 < a14) && (-84 >= a14)) )){
      a26 = (((a26 / 5) + 69) - -10);
      a28 = ((((a28 + 20984) / 5) % 82)- -216);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && (((input == 6) && ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && ((-114 < a14) && (-84 >= a14)) ))))){
      a14 = (((a14 * 5) - -356251) - 823914);
      a26 = ((((a26 / 5) + -466083) * 10)/ 9);
      a28 = ((((a28 / -5) * 5) - -229660) * -2);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && (( ((134 < a28) && (300 >= a28)) && (((input == 3) && (a24==2)) && -84 < a14 )) && ((124 < a26) && (217 >= a26)) ))){
      a26 = (((a26 - 260890) - 47933) + -121418);
       a24 = 1;
       return -1;
     } else if(( ((-182 < a14) && (-114 >= a14)) && (( ((-68 < a26) && (124 >= a26)) && ( 300 < a28 && ((input == 3) && (a24==3)))) && a21 <= 127 ))){
      a14 = (((a14 + 474379) + 2837) - -46014);
      a26 = ((((a26 + 449902) + 29250) % 46)- -155);
      a28 = ((((a28 / 5) % 82)+ 216) + -6);
       a24 = 2;
       return 26;
     } else if(( a21 <= 127 && ( ((37 < a28) && (134 >= a28)) && ((a24==3) && (((input == 1) && 217 < a26 ) && a14 <= -182 ))))){
      a14 = (((a14 + 320729) - -279262) * 1);
      a28 = (((a28 / 5) - -93488) + -664969);
       a24 = 1;
       return 26;
     } else if(((a24==3) && ((( a26 <= -68 && ( -84 < a14 && (input == 1))) && a21 <= 127 ) && 300 < a28 ))){
      a14 = (((((a14 + 0) % 299909)- 300090) / 5) - 124796);
      a28 = ((((((a28 % 48)- -60) * 5) * 5) % 48)+ 41);
       a24 = 2;
       return 25;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ( a28 <= 37 && ((a24==3) && (((input == 6) && 217 < a26 ) && a21 <= 127 ))))){
      a26 = (((((a26 * 9)/ 10) * 1) * 1) - 570350);
      a28 = (((((a28 % 299849)+ 300149) + 2) / 5) - -172923);
       a24 = 1;
       return -1;
     } else if(((( ((-182 < a14) && (-114 >= a14)) && ((a24==2) && ((input == 2) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))))) && a21 <= 127 ) && 217 < a26 )){
      a14 = (((a14 - -62668) - 204030) + -63138);
      a26 = (((((a26 - 58572) + -541553) / 5) * 28)/ 10);
      a28 = ((((a28 * 9)/ 10) + -585001) - 3230);
       a24 = 1;
       return -1;
     } else if((((((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 3)) && -84 < a14 ) && a21 <= 127 ) && (a24==3)) && a26 <= -68 )){
      a14 = (((((a14 % 299909)+ -300090) + -2) / 5) - 59987);
      a28 = (((a28 / 5) + -490514) / 5);
       a24 = 1;
       return -1;
     } else if(( ((-114 < a14) && (-84 >= a14)) && (((((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 1)) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 ) && (a24==3)))){
      a26 = (((a26 + -535040) * 1) + 534850);
      a28 = ((((a28 - 458911) + 150456) / 5) - -419981);
       a24 = 1;
       return -1;
     } else if(((( a26 <= -68 && ( ((134 < a28) && (300 >= a28)) && ((input == 1) && a21 <= 127 ))) && (a24==2)) && a14 <= -182 )){
      a14 = (((((a14 % 33)+ -131) + -52911) / 5) - -10461);
       a24 = 3;
       return 21;
     } else if(( a14 <= -182 && ( ((134 < a28) && (300 >= a28)) && (( a21 <= 127 && ((input == 1) && 217 < a26 )) && (a24==2))))){
      a14 = ((((a14 % 14)+ -96) - 481357) - -481353);
      a26 = (((((a26 - 192808) + 143479) * 1) % 46)- -170);
      a28 = (((a28 - 485508) - 38822) * 1);
       return -1;
     } else if(((a24==2) && ( a21 <= 127 && (((input == 2) && (( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 ))) && 217 < a26 )))){
      a14 = ((((a14 / 5) * 4) % 14)- 91);
      a26 = (((a26 - 0) - 600188) - 13);
      a28 = ((((a28 % 82)+ 218) + 87723) + -87723);
       a24 = 1;
       return -1;
     } else if(( -84 < a14 && ((a24==3) && ((((input == 5) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 ) && ((-68 < a26) && (124 >= a26)) )))){
      a26 = (((a26 + -288975) * 2) - 20049);
       return -1;
     } else if(((a24==2) && ( ((124 < a26) && (217 >= a26)) && ( a21 <= 127 && ((input == 2) && ((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 )) || ( ((37 < a28) && (134 >= a28)) && -84 < a14 ))))))){
      a14 = (((((a14 % 299909)- 300090) - 1) + 598064) - 598064);
      a26 = (((a26 + -471538) / 5) * 5);
      a28 = ((((a28 % 300018)- 299980) + -3) - 0);
       a24 = 1;
       return -1;
     } else if(( a26 <= -68 && ( -84 < a14 && ((a24==3) && ( a21 <= 127 && ((input == 5) && 300 < a28 )))))){
      a14 = ((((a14 / 5) + 96871) % 14)- 105);
      a26 = (((((((a26 * 9)/ 10) % 95)+ 111) * 5) % 95)+ -63);
      a28 = (((a28 / -5) * 4) * 1);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((( ((-68 < a26) && (124 >= a26)) && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 2))) && (a24==2)) && -84 < a14 ))){
      a14 = ((((a14 * 9)/ 10) + -555577) - 25485);
      a26 = ((((a26 * 5) - -317534) * 1) + -584522);
      a28 = (((a28 - 600023) * 1) + -10);
       a24 = 1;
       return -1;
     } else if(( ((-68 < a26) && (124 >= a26)) && ( ((-182 < a14) && (-114 >= a14)) && ((((input == 4) && 300 < a28 ) && (a24==3)) && a21 <= 127 )))){
      a14 = ((((a14 * 5) * 5) * 5) * -5);
      a26 = ((((a26 % 46)+ 171) + 1) + -1);
       a24 = 1;
       return -1;
     } else if(( ((-68 < a26) && (124 >= a26)) && ((a24==2) && ( a14 <= -182 && ( a21 <= 127 && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 1))))))){
      a14 = (((((a14 % 14)+ -92) - 312770) * 1) + 312775);
      a26 = ((((a26 - 381650) - -543989) * 3) - 761073);
      a28 = ((((((a28 * 9)/ 10) % 48)+ 44) * 10)/ 9);
       a24 = 3;
       return 21;
     } else if((( a21 <= 127 && ( a26 <= -68 && ((input == 4) && (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 ))))) && (a24==2))){
      a14 = ((((a14 % 299909)+ -300090) - 2) + 0);
      a26 = ((((((a26 * 9)/ 10) % 46)+ 176) - 517205) + 517220);
      a28 = (((((a28 % 299849)- -300149) - -2) - 526339) - -526339);
       return 21;
     } else if((( a21 <= 127 && (((a24==3) && ((input == 5) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && ((-182 < a14) && (-114 >= a14)) )) && ((124 < a26) && (217 >= a26)) )){
      if( ((134 < a28) && (300 >= a28)) ){
      a14 = (((((a14 / 5) * 9)/ 10) * 5) + 454059);
      a28 = (((((a28 * 9)/ 10) % 48)+ 86) + 1);
       a24 = 2;
      } else{
       a14 = ((((a14 * 16)/ 10) - 266555) * 2);
       a26 = ((((a26 + -171) + -312098) - -484950) - 172869);
       a28 = (((((a28 + 0) / 5) * 4) % 48)- -85);
       a24 = 2;
      } return -1;
     } else if((((( ((-182 < a14) && (-114 >= a14)) && ( a21 <= 127 && (input == 6))) && (a24==2)) && a28 <= 37 ) && ((124 < a26) && (217 >= a26)) )){
      a14 = (((((a14 + -21002) / 5) - -262267) * -1)/ 10);
       a24 = 1;
       return -1;
     } else if((( ((-68 < a26) && (124 >= a26)) && ( a21 <= 127 && ((a24==3) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 1))))) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = (((a14 + -298760) - 124868) / 5);
      a26 = (((a26 - -363418) - -96778) * 1);
      a28 = (((a28 * 5) / 5) + -160943);
       a24 = 2;
       return 25;
     } else if(( ((-114 < a14) && (-84 >= a14)) && ( 300 < a28 && ( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && ((a24==2) && (input == 5))))))){
      a14 = (((((a14 * 22)/ 10) - -256716) / 5) - 346439);
      a26 = ((((a26 * 5) + -272828) * 10)/ 9);
      a28 = (((a28 + -600129) / 5) / 5);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( ((124 < a26) && (217 >= a26)) && ( a14 <= -182 && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 2)) && a21 <= 127 ))))){
      a14 = ((((a14 % 14)- 89) + 4) + -12);
      a28 = ((((a28 + -600007) + 533056) + 39168) + -572325);
       return 25;
     } else if(( a26 <= -68 && ((a24==2) && ((((input == 4) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )) && a21 <= 127 ) && -84 < a14 )))){
      if( ((-182 < a14) && (-114 >= a14)) ){
      a14 = (((((a14 % 14)- 97) * 5) % 14)- 99);
      a28 = (((((a28 * 9)/ 10) / 5) % 82)+ 217);
       a24 = 3;
      } else{
       a14 = (((((a14 % 33)+ -148) - 140044) - 142644) + 282687);
       a26 = ((((((a26 % 299891)+ 300108) - 484968) / 5) * -1)/ 10);
       a28 = ((((a28 % 48)+ 49) + 33) - -3);
      } return 21;
     } else if((( a26 <= -68 && ((a24==3) && ( a21 <= 127 && ( a28 <= 37 && (input == 6))))) && -84 < a14 )){
      a14 = (((((a14 % 299909)- 300090) / 5) * 5) - 3);
      a26 = (((((((a26 % 46)- -190) * 9)/ 10) * 5) % 46)+ 128);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((input == 5) && (( a28 <= 37 && ((a24==3) && ( a26 <= -68 && a14 <= -182 ))) || (( ((134 < a28) && (300 >= a28)) && ((a24==2) && ( 217 < a26 && -84 < a14 ))) || (((a24==2) && ( -84 < a14 && 217 < a26 )) && 300 < a28 )))))){
      a14 = ((((a14 % 299909)- 300090) - 2) - 0);
      a26 = ((((a26 % 299966)+ -300033) / 5) - 264062);
      a28 = ((((a28 % 300018)- 299980) / 5) + -108599);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((a24==2) && (((( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 )) || ( -84 < a14 && ((37 < a28) && (134 >= a28)) )) && (input == 3)))) && 217 < a26 )){
      a14 = (((((a14 % 300041)+ 299957) / 5) - 530177) * -1);
      a26 = (((a26 - 600195) * 1) * 1);
      a28 = ((((((a28 * 9)/ 10) + 58602) - -677) % 82)- -217);
       return 26;
     } else if(((( a28 <= 37 && ( a21 <= 127 && ((a24==2) && (input == 2)))) && ((-68 < a26) && (124 >= a26)) ) && -84 < a14 )){
      a14 = ((((a14 - 391701) % 299909)+ -300090) + -2);
      a26 = (((a26 - 476734) * 1) * 1);
       a24 = 1;
       return -1;
     } else if(((a24==2) && (((((( ((134 < a28) && (300 >= a28)) && ((-182 < a14) && (-114 >= a14)) ) || ( 300 < a28 && ((-182 < a14) && (-114 >= a14)) )) || ( ((-114 < a14) && (-84 >= a14)) && a28 <= 37 )) && (input == 1)) && a21 <= 127 ) && ((-68 < a26) && (124 >= a26)) ))){
      a14 = (((((a14 * 22)/ 10) * 10)/ 9) + -72468);
      a26 = (((((a26 + 57291) - 630469) - 10325) * -1)/ 10);
      a28 = (((((a28 % 82)- -217) - -3474) / 5) - 549);
       a24 = 1;
       return -1;
     } else if((( ((-182 < a14) && (-114 >= a14)) && (((a24==2) && ((input == 5) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ))) && 217 < a26 )) && a21 <= 127 )){
      a14 = (((a14 - 478432) + 950696) + 107906);
      a26 = ((((((a26 * -4)/ 10) * 10)/ 9) - -222749) + -355038);
      a28 = ((((a28 + -103775) % 82)+ 217) + 2);
       return 26;
     } else if(( a14 <= -182 && ( a21 <= 127 && ((a24==2) && (((input == 5) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && a26 <= -68 ))))){
      a28 = (((a28 / 5) * 4) / 5);
       a24 = 1;
       return -1;
     } else if(((a24==3) && (( ((124 < a26) && (217 >= a26)) && ( a21 <= 127 && ((input == 1) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))))) && a14 <= -182 ))){
      a14 = ((((a14 % 14)+ -97) - -6) + -2);
      a26 = (((a26 + 36288) * 5) * 3);
      a28 = (((((a28 + 0) - 0) + -294774) % 299849)+ 300149);
       a24 = 2;
       return 25;
     } else if((( ((-68 < a26) && (124 >= a26)) && ((a24==2) && (( a21 <= 127 && (input == 3)) && ((37 < a28) && (134 >= a28)) ))) && -84 < a14 )){
      a14 = ((((a14 % 299909)- 300090) - 1) * 1);
      a26 = (((a26 - 307563) / 5) + -94106);
      a28 = (((a28 * 5) / -5) * 5);
       return 25;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ( ((-68 < a26) && (124 >= a26)) && ((((input == 5) && a21 <= 127 ) && 300 < a28 ) && (a24==3))))){
      a14 = (((((a14 * 5) * 5) + 232368) * -1)/ 10);
      a26 = ((((a26 + 218034) + 60386) * 10)/ 9);
      a28 = ((((a28 % 48)- -54) / 5) + 63);
       a24 = 2;
       return 26;
     } else if(( ((-68 < a26) && (124 >= a26)) && (((((input == 1) && a21 <= 127 ) && ((-182 < a14) && (-114 >= a14)) ) && 300 < a28 ) && (a24==3)))){
      a14 = (((((a14 % 14)- 98) / 5) + -48356) + 48265);
      a26 = (((a26 - 443768) + -95684) + 2569);
       a24 = 2;
       return 25;
     } else if(( ((-182 < a14) && (-114 >= a14)) && (( a21 <= 127 && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 5)) && (a24==2))) && ((-68 < a26) && (124 >= a26)) ))){
      a14 = (((((a14 % 14)- 89) * 5) % 14)+ -95);
      a28 = ((((a28 % 300018)- 299980) / 5) - 311547);
       a24 = 1;
       return -1;
     } else if(((((a24==3) && ( a14 <= -182 && ((input == 1) && a28 <= 37 ))) && 217 < a26 ) && a21 <= 127 )){
      a14 = ((((a14 - -207809) * 1) % 33)- 146);
       return 25;
     } else if(( a21 <= 127 && (( ((-68 < a26) && (124 >= a26)) && ((( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 ))) && (input == 6))) && (a24==3)))){
      a14 = ((((a14 % 299909)- 300090) - 1) + 0);
      a26 = (((((a26 % 46)+ 171) + 586731) + -778760) - -192029);
      a28 = (((((a28 % 300018)+ -299980) - 3) - -267547) + -267546);
       a24 = 2;
       return -1;
     } else if(((((a24==2) && ( -84 < a14 && ( ((-68 < a26) && (124 >= a26)) && (input == 1)))) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 )){
      a26 = ((((a26 / 5) / 5) * 5) - -148);
      a28 = ((((a28 - -99) + -476766) - -263996) - -212799);
       return 25;
     } else if((((( ((134 < a28) && (300 >= a28)) && ((input == 5) && a14 <= -182 )) && (a24==2)) && a21 <= 127 ) && a26 <= -68 )){
      a28 = (((a28 + -155557) + 578830) - 889585);
       a24 = 1;
       return -1;
     } else if(( 300 < a28 && (((((a24==3) && (input == 1)) && ((-114 < a14) && (-84 >= a14)) ) && a21 <= 127 ) && a26 <= -68 ))){
      a14 = (((a14 - 217645) - 127850) + 209788);
      a28 = (((a28 / -5) / 5) + -406897);
       a24 = 2;
       return 25;
     } else if(( a21 <= 127 && (((a24==2) && (((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 1)) && ((-182 < a14) && (-114 >= a14)) )) && a26 <= -68 ))){
      if( ((-114 < a14) && (-84 >= a14)) ){
      a26 = ((((a26 - -303459) + 282095) % 95)+ 28);
      a28 = ((((a28 % 48)- -44) + -98566) - -98604);
       a24 = 3;
      } else{
       a14 = (((((a14 % 14)- 91) * 5) % 14)+ -94);
       a26 = ((((((a26 % 95)- -35) + 13) * 5) % 95)- -29);
       a28 = ((((((a28 + 0) * 9)/ 10) - 373470) % 48)+ 86);
      } return 21;
     } else if(( ((-68 < a26) && (124 >= a26)) && (( -84 < a14 && (((input == 3) && (a24==3)) && a21 <= 127 )) && ((134 < a28) && (300 >= a28)) ))){
      a14 = ((((a14 % 33)- 146) - -231813) + -231815);
      a26 = (((a26 - -277492) * 2) * 1);
      a28 = (((a28 / 5) - -156245) + -156222);
       a24 = 1;
       return -1;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ((((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 5)) && a21 <= 127 ) && ((-68 < a26) && (124 >= a26)) )) && (a24==3))){
      a26 = ((((a26 - 280632) + -95725) % 46)+ 186);
      a28 = (((((a28 % 82)- -218) + -401117) / 5) + 80371);
       a24 = 1;
       return 25;
     } else if(((a24==3) && (( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 4)))) && ((124 < a26) && (217 >= a26)) ))){
      a14 = (((a14 * 5) + 123936) * 4);
      a26 = ((((a26 * -1)/ 10) + 253331) + -253205);
      a28 = (((a28 - 600009) / 5) - 52994);
       a24 = 1;
       return 25;
     } else if(( a21 <= 127 && ((((input == 1) && (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 ))) && a26 <= -68 ) && (a24==2)))){
      a14 = (((((a14 + -67151) / 5) / 5) % 33)+ -146);
      a26 = (((((a26 % 46)- -198) / 5) - -217810) - 217675);
      a28 = (((((a28 % 82)- -218) - -1) + 550201) + -550202);
       return 21;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ((((input == 3) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )) && a21 <= 127 ) && ((124 < a26) && (217 >= a26)) )) && (a24==3))){
      if((a24==3)){
      a14 = (((a14 * 5) + -343422) * 1);
      a26 = (((((a26 * 5) + -193919) / 5) * -1)/ 10);
      a28 = ((((a28 % 299849)- -301) * 1) - -209641);
       a24 = 1;
      } else{
       a14 = (((((a14 * 14)/ 10) / 5) - -416748) - 416891);
       a28 = (((((a28 * 9)/ 10) * 1) + 27131) * -1);
       a24 = 2;
      } return -1;
     } else if((((a24==3) && (( ((124 < a26) && (217 >= a26)) && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 3))) && a21 <= 127 )) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = (((a14 + 261227) - -112879) + 216570);
      a28 = (((a28 - 600084) + -44) * 1);
       a24 = 1;
       return 25;
     } else if(( a26 <= -68 && ((((a24==3) && ((input == 2) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )))) && a21 <= 127 ) && ((-114 < a14) && (-84 >= a14)) ))){
      a14 = (((a14 - 288458) + -56542) * 1);
      a28 = ((((a28 % 300018)- 299980) / 5) + -218963);
       a24 = 1;
       return -1;
     } else if(((a24==3) && (( a26 <= -68 && (( -84 < a14 && (input == 2)) && a21 <= 127 )) && 300 < a28 ))){
      a14 = ((((a14 % 299909)+ -300090) + 20521) + -20522);
      a26 = ((((((a26 - 0) * 9)/ 10) - -5006) % 46)+ 170);
       a24 = 1;
       return -1;
     } else if(( 217 < a26 && ( a21 <= 127 && ((a24==3) && ( a28 <= 37 && ( ((-182 < a14) && (-114 >= a14)) && (input == 5))))))){
      if( ((124 < a26) && (217 >= a26)) ){
      a28 = ((((a28 % 82)- -218) + -1) - -2);
       a24 = 1;
      } else{
       a14 = ((((a14 + 119455) + 328376) * 10)/ 9);
       a28 = (((((a28 % 82)+ 217) * 5) % 82)+ 195);
       a24 = 1;
      } return 21;
     } else if(((a24==2) && (( ((-68 < a26) && (124 >= a26)) && ((( ((-114 < a14) && (-84 >= a14)) && a28 <= 37 ) || (( ((134 < a28) && (300 >= a28)) && ((-182 < a14) && (-114 >= a14)) ) || ( ((-182 < a14) && (-114 >= a14)) && 300 < a28 ))) && (input == 4))) && a21 <= 127 ))){
      a14 = ((((a14 - 135125) / 5) / 5) - -5288);
      a26 = ((((a26 - -515837) / 5) / 5) + -20439);
      a28 = (((((a28 * 9)/ 10) % 82)- -218) + 1);
       a24 = 1;
       return -1;
     } else if((( 217 < a26 && ((a24==3) && (((input == 5) && ((37 < a28) && (134 >= a28)) ) && a21 <= 127 ))) && a14 <= -182 )){
      if((a24==1)){
      a14 = ((((a14 % 33)+ -126) + 38868) - 38889);
      a28 = (((a28 - 361320) + -95708) * 1);
       a24 = 1;
      } else{
       a28 = (((a28 - -575166) * 1) - 429445);
       a24 = 2;
      } return -1;
     } else if((( ((-114 < a14) && (-84 >= a14)) && ((((input == 1) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && 217 < a26 ) && a21 <= 127 )) && (a24==2))){
      a14 = ((((a14 * 5) + -361087) + 460017) - 558491);
      a28 = (((((a28 * 9)/ 10) + -11298) % 48)- -122);
       return -1;
     } else if(( a21 <= 127 && (((((input == 4) && -84 < a14 ) && ((124 < a26) && (217 >= a26)) ) && (a24==3)) && 300 < a28 ))){
      if( ((203 < a21) && (399 >= a21)) ){
      a14 = ((((a14 % 33)+ -148) / 5) * 5);
      a26 = (((((a26 * -6)/ 10) + -234053) * 10)/ 9);
      a28 = (((a28 - 599974) - 137) * 1);
      } else{
       a14 = (((((a14 * 9)/ 10) % 33)- 146) * 1);
       a26 = (((a26 + -166556) * 3) - -866771);
       a28 = ((((a28 % 48)- -46) - -373193) + -373159);
       a24 = 1;
      } return 26;
     } else if(((a24==2) && ( ((37 < a28) && (134 >= a28)) && ((((input == 6) && -84 < a14 ) && a26 <= -68 ) && a21 <= 127 )))){
      a26 = (((((a26 - -377067) % 46)+ 170) - -516657) + -516655);
      a28 = ((((a28 + -13942) - -14102) * 9)/ 10);
       return 25;
     } else if(((((( 300 < a28 && (input == 4)) && a21 <= 127 ) && (a24==2)) && ((-68 < a26) && (124 >= a26)) ) && ((-114 < a14) && (-84 >= a14)) )){
      a14 = ((((a14 - -282795) - -310075) * 1) - 902533);
      a26 = ((((a26 + -123096) + -349255) * 10)/ 9);
      a28 = (((a28 - 398868) / 5) + -390344);
       a24 = 1;
       return -1;
     } else if((((((input == 2) && (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 ))) && a26 <= -68 ) && (a24==2)) && a21 <= 127 )){
      a14 = ((((a14 % 299909)+ -300090) * 1) + -2);
      a28 = (((((a28 % 300018)- 299980) + 209705) / 5) + -378252);
       a24 = 1;
       return -1;
     } else if((( ((-68 < a26) && (124 >= a26)) && ((((input == 2) && -84 < a14 ) && (a24==2)) && a21 <= 127 )) && ((37 < a28) && (134 >= a28)) )){
      a14 = ((((a14 % 299909)+ -300090) * 1) + -1);
      a26 = ((((a26 - -476528) - -54423) * 10)/ 9);
      a28 = (((((a28 + 136381) + 63820) + -434425) * -1)/ 10);
       return 25;
     } else if(((((a24==2) && ( ((-182 < a14) && (-114 >= a14)) && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 4)))) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )){
      a28 = (((a28 + -600023) - -146322) + -146275);
       a24 = 1;
       return -1;
     } else if(( ((124 < a26) && (217 >= a26)) && ((a24==2) && ( a21 <= 127 && (((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 )) || ( -84 < a14 && ((37 < a28) && (134 >= a28)) )) && (input == 6)))))){
      a14 = ((((a14 % 299909)- 300090) - 1) + 0);
      a26 = (((a26 + -351032) * 1) - 191650);
      a28 = ((((a28 % 300018)- 299980) * 1) * 1);
       a24 = 1;
       return -1;
     } else if((((a24==2) && (( a21 <= 127 && ((input == 1) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))) && -84 < a14 )) && ((-68 < a26) && (124 >= a26)) )){
      a14 = (((((a14 % 299909)+ -300090) - 1) / 5) - 204515);
      a26 = (((a26 + 373131) + -442855) + -413854);
      a28 = ((((a28 * 9)/ 10) * -1) - 996);
       a24 = 1;
       return -1;
     } else if((((a24==3) && (((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 1)) && a26 <= -68 ) && ((-114 < a14) && (-84 >= a14)) )) && a21 <= 127 )){
      a14 = (((a14 + -396035) / 5) + -79326);
      a28 = ((((a28 % 300018)- 299980) - 1) / 5);
       a24 = 1;
       return -1;
     } else if(((a24==2) && (((( a21 <= 127 && (input == 2)) && 217 < a26 ) && ((37 < a28) && (134 >= a28)) ) && a14 <= -182 ))){
      a14 = ((((a14 / -5) * 10)/ 9) * 4);
       return 25;
     } else if(( a21 <= 127 && ((a24==2) && ( ((-68 < a26) && (124 >= a26)) && ((( ((-114 < a14) && (-84 >= a14)) && a28 <= 37 ) || (( ((134 < a28) && (300 >= a28)) && ((-182 < a14) && (-114 >= a14)) ) || ( 300 < a28 && ((-182 < a14) && (-114 >= a14)) ))) && (input == 6)))))){
      a14 = ((((a14 + -340583) - -856359) - -75420) - 1151050);
      a26 = (((((a26 / 5) - -150) / 5) * 49)/ 10);
      a28 = ((((a28 % 82)- -216) - -412026) - 412025);
       a24 = 1;
       return -1;
     } else if((( 217 < a26 && ((((( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 )) || ( ((37 < a28) && (134 >= a28)) && -84 < a14 )) && (input == 6)) && a21 <= 127 )) && (a24==2))){
      a14 = ((((a14 - 312950) % 299909)- 300090) * 1);
      a26 = (((((a26 * -4)/ 10) - -250378) * 2) - 586797);
      a28 = (((((a28 * 9)/ 10) % 300018)+ -299980) * 1);
       a24 = 1;
       return -1;
     } else if(( a14 <= -182 && ( a21 <= 127 && (((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 3)) && ((-68 < a26) && (124 >= a26)) ) && (a24==2))))){
      a26 = (((a26 - 587998) - 6171) / 5);
      a28 = ((((a28 / 5) / -5) + 70330) * -5);
       a24 = 1;
       return -1;
     } else if(((( a21 <= 127 && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 5)) && a26 <= -68 )) && (a24==2)) && -84 < a14 )){
      a14 = (((((a14 * 9)/ 10) + 18444) * 1) - 597139);
      a26 = ((((a26 * 9)/ 10) / 5) + 449884);
      a28 = ((((a28 % 299849)+ 301) * 1) + 18642);
       return 26;
     } else if(( ((-114 < a14) && (-84 >= a14)) && ( a21 <= 127 && (( a26 <= -68 && ((input == 2) && 300 < a28 )) && (a24==3))))){
      a14 = (((a14 - 584972) + -14678) + 284227);
      a26 = ((((a26 / 5) % 46)- -198) - -14);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( ((-182 < a14) && (-114 >= a14)) && (( ((124 < a26) && (217 >= a26)) && ((input == 5) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && (a24==2))))){
      a14 = (((((a14 % 14)+ -85) / 5) * 51)/ 10);
      a28 = (((((a28 / 5) % 82)+ 173) * 9)/ 10);
       return 25;
     } else if((( a26 <= -68 && ( -84 < a14 && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 2)) && a21 <= 127 ))) && (a24==2))){
      a14 = ((((a14 + 0) % 299909)+ -300090) * 1);
      a28 = (((a28 + -600062) * 1) + -25);
       a24 = 1;
       return -1;
     } else if((((a24==2) && ((((input == 1) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && a21 <= 127 ) && 217 < a26 )) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = ((((a14 * 10)/ 6) - 103799) / 5);
      a26 = ((((a26 - 600073) - -243258) - -155152) - 398457);
      a28 = ((((a28 / 5) * 4) / 5) + -551154);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( ((-68 < a26) && (124 >= a26)) && (( a21 <= 127 && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 2))) && ((-182 < a14) && (-114 >= a14)) )))){
      a14 = (((((a14 * 16)/ 10) * 5) * 10)/ 9);
      a26 = ((((a26 - -114763) % 46)+ 128) * 1);
      a28 = ((((a28 % 299849)- -300149) * 1) * 1);
       a24 = 1;
       return -1;
     } else if(((( a14 <= -182 && ( ((37 < a28) && (134 >= a28)) && ( a21 <= 127 && (input == 1)))) && 217 < a26 ) && (a24==2))){
      if( ((124 < a26) && (217 >= a26)) ){
      a14 = ((((a14 - -427583) % 14)+ -99) - 1);
      } else{
      } return -1;
     } else if(((((( a21 <= 127 && (input == 6)) && a26 <= -68 ) && (a24==2)) && a14 <= -182 ) && ((134 < a28) && (300 >= a28)) )){
      a28 = (((a28 + 350922) - 361070) * 5);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && (( ((-114 < a14) && (-84 >= a14)) && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 6))) && ((-68 < a26) && (124 >= a26)) )) && (a24==3))){
      a14 = ((((a14 + 132510) * 10)/ -9) + -154894);
      a26 = ((((a26 % 46)+ 171) / 5) * 5);
      a28 = (((((a28 % 300018)- 299980) - 1) - -509927) + -509928);
       a24 = 1;
       return 21;
     } else if(((((( a21 <= 127 && (input == 2)) && a14 <= -182 ) && (a24==3)) && ((37 < a28) && (134 >= a28)) ) && 217 < a26 )){
      a14 = (((((a14 - 0) * 9)/ 10) % 14)+ -91);
      a26 = (((((a26 + 0) * 9)/ 10) % 95)- -19);
      a28 = (((a28 + 145008) / -5) + -31906);
       a24 = 1;
       return 25;
     } else if(((((((input == 2) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && a14 <= -182 ) && ((124 < a26) && (217 >= a26)) ) && (a24==2)) && a21 <= 127 )){
      a26 = (((a26 - 203112) + -391744) + -1984);
      a28 = (((((a28 % 300018)- 299980) / 5) * 10)/ 9);
       return 21;
     } else if(( a14 <= -182 && ((a24==2) && ( 217 < a26 && ( ((37 < a28) && (134 >= a28)) && ( a21 <= 127 && (input == 6))))))){
      if( a28 <= 37 ){
      a14 = ((((a14 % 14)+ -93) + -478471) - -478472);
      a28 = (((a28 - -326050) - 78801) * 2);
      } else{
       a26 = ((((a26 + -291107) - 309073) + 394043) - 393946);
       a28 = ((((a28 + 109) - -522801) * 1) - 522765);
      } return -1;
     } else if(( ((-68 < a26) && (124 >= a26)) && ( a21 <= 127 && (((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 1)) && ((-114 < a14) && (-84 >= a14)) ) && (a24==2))))){
      a14 = (((a14 + -535354) + -35401) + -564);
      a26 = (((a26 / 5) * 5) - -231681);
      a28 = ((((a28 / -5) - -291549) + 294080) - 919932);
       return 25;
     } else if(( ((124 < a26) && (217 >= a26)) && (((a24==2) && ( a14 <= -182 && ((input == 4) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )))) && a21 <= 127 ))){
      a28 = ((((a28 * 9)/ 10) + 48993) + 6553);
       return 21;
     } else if(( a21 <= 127 && ((( a14 <= -182 && ((input == 4) && a28 <= 37 )) && (a24==2)) && ((-68 < a26) && (124 >= a26)) ))){
      a26 = (((a26 + -331419) + 600956) - 599236);
       a24 = 1;
       return -1;
     } else if(((a24==3) && ( a21 <= 127 && ( -84 < a14 && (((input == 3) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && ((124 < a26) && (217 >= a26)) ))))){
      if( a14 <= -182 ){
      a14 = ((((((a14 % 33)+ -147) + -1) * 5) % 33)+ -117);
      a26 = ((((a26 + 246226) - 4331) * 10)/ 9);
      a28 = ((((((a28 / 5) % 82)- -218) * 5) % 82)- -164);
       a24 = 1;
      } else{
       a14 = ((((a14 - 0) * 9)/ 10) - 599697);
       a28 = (((((a28 % 82)+ 218) - 2) + 242606) + -242604);
       a24 = 1;
      } return -1;
     } else if(( ((124 < a26) && (217 >= a26)) && ((a24==3) && (( a28 <= 37 && ((input == 1) && a21 <= 127 )) && ((-114 < a14) && (-84 >= a14)) )))){
      a26 = ((((a26 * 5) / 5) * 5) + -574058);
       a24 = 2;
       return 25;
     } else if((( a26 <= -68 && ( a21 <= 127 && (( 300 < a28 && (input == 4)) && (a24==3)))) && ((-114 < a14) && (-84 >= a14)) )){
      a14 = (((a14 + 507598) - 675101) * 3);
      a26 = (((((a26 + 345366) - -182099) - 501524) % 299891)+ 300108);
      a28 = ((((((a28 + -229670) % 48)- -86) * 5) % 48)- -85);
       a24 = 2;
       return 21;
     } else if((((a24==2) && (( 217 < a26 && ((input == 4) && a21 <= 127 )) && ((134 < a28) && (300 >= a28)) )) && a14 <= -182 )){
      a26 = ((((a26 / 5) * 4) - -20422) + -540543);
      a28 = (((a28 - 593499) + -5083) + -1301);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((((input == 3) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && ((-68 < a26) && (124 >= a26)) ) && (a24==3))) && a14 <= -182 )){
      a26 = ((((a26 - 296413) * 10)/ 9) / 5);
      a28 = ((((a28 + 319596) + -255453) / 5) + -461170);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( a26 <= -68 && (((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 3)) && (a24==2)) && a14 <= -182 )))){
      a14 = (((((a14 + 0) / 5) + -424186) % 33)- 120);
      a28 = (((((a28 % 48)+ 85) / 5) - -586728) - 586653);
       return 26;
     } else if(( a21 <= 127 && ((a24==2) && (((( 300 < a28 && a14 <= -182 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) )) && (input == 1)) && 217 < a26 )))){
      a14 = ((((((a14 % 14)- 91) + 7) * 5) % 14)+ -92);
      a28 = (((((a28 % 300018)+ -299980) - -529138) + 57460) + -586599);
       a24 = 1;
       return -1;
     }
     return calculate_output2(input);
 }
 int calculate_output2(int input) {
     if(( a21 <= 127 && ((( -84 < a14 && ((input == 3) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && (a24==1)) && 217 < a26 ))){
      a14 = (((((a14 + -573739) % 299909)+ -300090) / 5) - 395532);
      a26 = ((((a26 * -4)/ 10) + -324259) - 5837);
      a28 = (((a28 + 0) / -5) * 4);
       return -1;
     } else if(((( ((124 < a26) && (217 >= a26)) && ((input == 5) && (( -84 < a14 && ((37 < a28) && (134 >= a28)) ) || (( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( -84 < a14 && a28 <= 37 ))))) && a21 <= 127 ) && (a24==2))){
      a14 = ((((a14 % 299909)- 300090) * 1) * 1);
      a26 = ((((((a26 * -6)/ 10) - -338538) + 11563) * -1)/ 10);
      a28 = ((((((a28 + 0) % 82)- -218) * 5) % 82)+ 154);
       return 25;
     } else if((( -84 < a14 && (((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 5)) && (a24==2)) && a21 <= 127 )) && ((-68 < a26) && (124 >= a26)) )){
      a26 = ((((a26 * 5) / 5) % 46)+ 171);
      a28 = (((((a28 * 9)/ 10) % 48)- -46) - 7);
       return 21;
     } else if(( ((-182 < a14) && (-114 >= a14)) && (( ((124 < a26) && (217 >= a26)) && ((a24==3) && ((input == 6) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )))) && a21 <= 127 ))){
      a14 = (((a14 / 5) + 492183) + 47631);
      a26 = (((((a26 / 5) + -216781) - -435488) * -1)/ 10);
      a28 = (((((a28 - 38261) / 5) / 5) % 48)+ 85);
       a24 = 1;
       return 25;
     } else if((((a24==3) && ((input == 4) && (( 300 < a28 && ( -84 < a14 && ((-68 < a26) && (124 >= a26)) )) || ( a28 <= 37 && ( ((124 < a26) && (217 >= a26)) && a14 <= -182 ))))) && a21 <= 127 )){
      a14 = (((a14 / 5) + -269330) / 5);
      a26 = (((a26 + 167622) / 5) * 5);
      a28 = ((((a28 % 299849)+ 300149) + 0) * 1);
       a24 = 1;
       return 26;
     } else if(( a21 <= 127 && ((a24==2) && ((input == 3) && (( 300 < a28 && ( ((124 < a26) && (217 >= a26)) && -84 < a14 )) || ( a28 <= 37 && ( a14 <= -182 && 217 < a26 ))))))){
      a14 = (((((a14 / 5) % 14)+ -99) - 251012) + 251013);
      a26 = ((((a26 % 46)- -161) / 5) - -128);
      a28 = ((((a28 % 82)- -216) - -3) + -2);
       return -1;
     } else if((((((( ((-68 < a26) && (124 >= a26)) && -84 < a14 ) && 300 < a28 ) || (( ((124 < a26) && (217 >= a26)) && a14 <= -182 ) && a28 <= 37 )) && (input == 1)) && (a24==3)) && a21 <= 127 )){
      if( ((203 < a21) && (399 >= a21)) ){
      a14 = ((((((a14 * 9)/ 10) + -1126) - 12238) % 14)+ -97);
      a26 = (((a26 - 286006) / 5) / 5);
      a28 = (((a28 / 5) + 326737) - -69076);
      } else{
       a14 = ((((a14 % 14)- 99) - -1) + -1);
       a26 = (((((a26 / 5) + -45) * 5) % 95)+ 93);
       a28 = (((((a28 % 82)- -216) + 1) - 69576) - -69577);
       a24 = 2;
      } return -1;
     } else if((( a21 <= 127 && (((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 3)) && (a24==2)) && ((-114 < a14) && (-84 >= a14)) )) && a26 <= -68 )){
      a14 = (((a14 * 5) + -331004) + -231106);
      a28 = ((((a28 / 5) + -326923) + 491246) * -3);
       a24 = 1;
       return -1;
     } else if((((( 217 < a26 && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 4))) && ((-182 < a14) && (-114 >= a14)) ) && (a24==2)) && a21 <= 127 )){
      a14 = ((((a14 * 10)/ 6) * 5) / 5);
      a26 = ((((a26 + -600121) - 39) + 249367) - 249353);
      a28 = (((a28 + -600005) * 1) - 28);
       a24 = 1;
       return -1;
     } else if(( -84 < a14 && ((a24==3) && ( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && ( ((134 < a28) && (300 >= a28)) && (input == 1))))))){
      if((a24==1)){
      a14 = ((((a14 % 14)- 98) * 1) + 1);
      a26 = (((((a26 / 5) * 5) - 82394) % 46)- -200);
      a28 = (((((a28 % 48)- -43) + 437170) + -496922) + 59747);
       a24 = 1;
      } else{
       a14 = ((((((a14 * 9)/ 10) + -382087) - -319194) % 33)+ -147);
       a28 = (((a28 / 5) + 247589) * 2);
      } return 21;
     } else if((((a24==2) && ( a26 <= -68 && ( a21 <= 127 && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 4))))) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = (((a14 + 572607) * 1) - -3198);
      a26 = ((((((a26 + 0) % 95)+ 69) * 5) % 95)+ 29);
      a28 = (((((a28 - 0) / 5) * 4) % 48)- -61);
       return 21;
     } else if((( a14 <= -182 && ( a26 <= -68 && ((a24==3) && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 6))))) && a21 <= 127 )){
      a14 = (((a14 / 5) * -4) - -115663);
      a26 = ((((a26 + 0) % 46)- -183) - -24);
      a28 = ((((a28 % 82)+ 204) + -7) - -18);
       a24 = 2;
       return 25;
     } else if((( ((-182 < a14) && (-114 >= a14)) && ( a28 <= 37 && ( a26 <= -68 && ((input == 1) && a21 <= 127 )))) && (a24==3))){
      a14 = ((((a14 + 144777) + 318163) + 32845) - 946945);
       a24 = 2;
       return 25;
     } else if(((((a24==3) && ( a14 <= -182 && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 2)))) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )){
      a14 = ((((a14 % 33)+ -118) - -4) + -31);
      a28 = (((a28 + -600012) * 1) - 1);
       a24 = 2;
       return 26;
     } else if(( a21 <= 127 && (( a14 <= -182 && ((a24==2) && ( ((134 < a28) && (300 >= a28)) && (input == 6)))) && 217 < a26 ))){
      a14 = ((((a14 - -599960) - 5473) + 4813) - -646);
      a28 = ((((((a28 % 48)+ 78) - -3) / 5) * 39)/ 10);
       return -1;
     } else if((( -84 < a14 && ( ((134 < a28) && (300 >= a28)) && (((input == 2) && (a24==2)) && a21 <= 127 ))) && ((124 < a26) && (217 >= a26)) )){
      a14 = (((((a14 % 299909)+ -300090) - 2) / 5) + -168281);
      a26 = ((((a26 - -194863) * 10)/ -9) + -363965);
       return 25;
     } else if(( a14 <= -182 && ((a24==3) && (( ((124 < a26) && (217 >= a26)) && ((input == 3) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && a21 <= 127 )))){
      a14 = ((((a14 % 14)+ -94) + 343086) - 343083);
      a26 = ((((((a26 * 10)/ 5) - -349578) + -367205) * -1)/ 10);
      a28 = (((((a28 - 448829) / 5) * 5) % 48)+ 86);
       a24 = 1;
       return -1;
     } else if(((((input == 6) && ((( ((124 < a26) && (217 >= a26)) && -84 < a14 ) && 300 < a28 ) || ( a28 <= 37 && ( a14 <= -182 && 217 < a26 )))) && a21 <= 127 ) && (a24==2))){
      a14 = ((((a14 % 33)+ -148) / 5) * 5);
      a26 = ((((((a26 * 9)/ 10) - -14252) * 1) % 95)- 10);
      a28 = (((((a28 % 48)- -86) * 5) % 48)+ 40);
       a24 = 1;
       return -1;
     } else if((((a24==3) && ( a28 <= 37 && ( a21 <= 127 && ( a26 <= -68 && (input == 5))))) && -84 < a14 )){
      a14 = ((((a14 % 299909)- 300090) - 2) - 0);
      a26 = ((((a26 % 299891)- -300108) + -564825) - -861686);
      a28 = ((((a28 - -494215) % 48)- -86) - 1);
       a24 = 2;
       return 26;
     } else if(( a21 <= 127 && ( 217 < a26 && (((input == 1) && (( -84 < a14 && ((37 < a28) && (134 >= a28)) ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 )))) && (a24==2))))){
      a14 = (((((a14 % 33)+ -148) + -260080) - 171020) + 431100);
      a26 = (((a26 + -600086) - -48664) + -48785);
      a28 = ((((a28 % 48)+ 86) + 541397) - 541397);
       a24 = 3;
       return 21;
     } else if(((( a21 <= 127 && ( a26 <= -68 && (( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 6)))) && ((-182 < a14) && (-114 >= a14)) ) && (a24==3))){
      a14 = ((((a14 % 14)+ -91) + 4) + -9);
      a26 = (((((a26 % 46)+ 170) - -54152) + -345817) + 291696);
      a28 = (((((a28 % 82)- -159) * 5) % 82)- -147);
       a24 = 2;
       return 26;
     } else if(( ((-114 < a14) && (-84 >= a14)) && ( a21 <= 127 && ((a24==3) && (((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 6)) && a26 <= -68 ))))){
      a14 = (((((a14 * 22)/ 10) - -275392) * -1)/ 10);
      a26 = ((((a26 + 68884) % 299891)- -300108) * 1);
      a28 = (((a28 / 5) - 340041) + -3956);
       a24 = 2;
       return -1;
     } else if((((a24==3) && ( -84 < a14 && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 5)) && a21 <= 127 ))) && ((124 < a26) && (217 >= a26)) )){
      if( ((127 < a21) && (203 >= a21)) ){
      a14 = (((((a14 * 9)/ 10) - -12352) % 33)+ -159);
      a28 = ((((a28 - 0) % 48)- -86) * 1);
       a24 = 1;
      } else{
       a14 = ((((a14 - 0) % 33)+ -146) + -2);
       a28 = ((((a28 % 82)- -218) * 1) + -1);
      } return 21;
     } else if(((( ((-182 < a14) && (-114 >= a14)) && ((a24==2) && ( a28 <= 37 && (input == 1)))) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )){
      a26 = (((((a26 / 5) + -348752) - -495822) * -1)/ 10);
      a28 = ((((a28 / 5) % 82)- -216) - -3);
       a24 = 3;
       return 25;
     } else if(( a21 <= 127 && ( ((-114 < a14) && (-84 >= a14)) && ( 300 < a28 && ( ((-68 < a26) && (124 >= a26)) && ((a24==2) && (input == 2))))))){
      a14 = (((a14 / 5) + -75728) * 5);
      a26 = (((a26 / 5) - 382336) * 1);
      a28 = ((((a28 + -600069) + -15) - -562943) + -563004);
       return 21;
     } else if((( ((124 < a26) && (217 >= a26)) && (((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 1)) && a21 <= 127 ) && a14 <= -182 )) && (a24==2))){
      a26 = ((((a26 * 10)/ -9) / 5) + -113859);
      a28 = (((((a28 % 300018)+ -299980) - 1) - -476944) + -476945);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && (((a24==3) && (((input == 1) && 300 < a28 ) && ((124 < a26) && (217 >= a26)) )) && -84 < a14 ))){
      if( ((134 < a28) && (300 >= a28)) ){
      a14 = (((((a14 % 33)+ -148) - -2) / 5) + -93);
      a26 = ((((a26 - 150747) * 10)/ 9) + -421463);
       a24 = 1;
      } else{
       a14 = (((((a14 - 208847) / 5) * 5) % 299909)+ -300090);
       a26 = ((((a26 * -6)/ 10) + -344460) * 1);
       a28 = (((a28 / 5) - 131548) * 4);
       a24 = 2;
      } return -1;
     } else if((((a24==3) && (( a21 <= 127 && ((input == 4) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && ((-114 < a14) && (-84 >= a14)) )) && ((124 < a26) && (217 >= a26)) )){
      a14 = (((((a14 * 14)/ 10) / 5) - 537659) - -537547);
      a28 = (((a28 - 600018) / 5) * 5);
       a24 = 2;
       return -1;
     } else if(( a26 <= -68 && (( a21 <= 127 && ((( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )) && (input == 4))) && (a24==2)))){
      a14 = (((((((a14 % 33)- 141) * 9)/ 10) * 5) % 33)+ -135);
      a26 = ((((a26 % 95)+ 77) + -37) - 10);
      a28 = ((((a28 * 9)/ 10) / 5) + 307707);
       return 25;
     } else if((( a26 <= -68 && ((a24==2) && (( -84 < a14 && (input == 5)) && a21 <= 127 ))) && ((37 < a28) && (134 >= a28)) )){
      a26 = ((((a26 + 406326) % 46)+ 171) - -1);
       return 21;
     } else if(((a24==2) && (((( 300 < a28 && ( ((124 < a26) && (217 >= a26)) && -84 < a14 )) || (( a14 <= -182 && 217 < a26 ) && a28 <= 37 )) && (input == 4)) && a21 <= 127 ))){
      a14 = ((((a14 + 0) % 299909)- 300090) - 1);
      a26 = ((((a26 - 600101) + 446740) - -98110) + -544822);
      a28 = (((((a28 * 9)/ 10) % 299849)- -300149) + 0);
       a24 = 3;
       return 25;
     } else if(((a24==3) && ( a14 <= -182 && ( ((37 < a28) && (134 >= a28)) && (((input == 3) && 217 < a26 ) && a21 <= 127 ))))){
      a14 = ((((((a14 % 14)- 99) * 9)/ 10) - 26828) + 26832);
      a26 = ((((a26 - 567555) - -124062) % 95)+ 29);
       a24 = 1;
       return -1;
     } else if(((a24==3) && ( -84 < a14 && (( 300 < a28 && ( a21 <= 127 && (input == 5))) && ((124 < a26) && (217 >= a26)) )))){
      if( 300 < a28 ){
      a26 = (((a26 * 5) + -208329) + 181135);
      a28 = (((a28 + -5328) + -594705) + -80);
      } else{
       a26 = (((a26 + -84253) + 84101) + 15);
       a28 = (((((a28 * 9)/ 10) - 179743) + -159854) + -228575);
       a24 = 1;
      } return 21;
     } else if((((input == 2) && ((((a24==3) && ( a14 <= -182 && a26 <= -68 )) && a28 <= 37 ) || ((((a24==2) && ( 217 < a26 && -84 < a14 )) && ((134 < a28) && (300 >= a28)) ) || (((a24==2) && ( 217 < a26 && -84 < a14 )) && 300 < a28 )))) && a21 <= 127 )){
      a14 = ((((a14 % 299909)- 300090) / 5) + -122480);
      a26 = ((((a26 % 299966)+ -300033) * 1) - 2);
      a28 = (((((a28 % 48)- -86) + -1) + -506689) + 506690);
       a24 = 2;
       return 21;
     } else if((((( ((-68 < a26) && (124 >= a26)) && ((input == 4) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))) && (a24==3)) && a21 <= 127 ) && a14 <= -182 )){
      a26 = (((a26 - 75942) * 5) - -42988);
      a28 = ((((a28 % 300018)- 299980) - 2) * 1);
       a24 = 1;
       return -1;
     } else if(( a14 <= -182 && ((( 217 < a26 && ((input == 5) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))) && (a24==3)) && a21 <= 127 ))){
      a14 = (((((a14 % 33)- 126) * 10)/ 9) + -2);
      a26 = (((a26 - 600095) + -92) - 11);
      a28 = (((a28 - 0) - 600066) - 52);
       a24 = 1;
       return 21;
     } else if(((a24==3) && ((( a26 <= -68 && ((input == 4) && a28 <= 37 )) && ((-182 < a14) && (-114 >= a14)) ) && a21 <= 127 ))){
      a14 = (((a14 + 326288) + -584141) + -213561);
      a26 = (((((a26 % 299891)+ 300108) + 245413) + -782818) - -676242);
      a28 = (((((a28 * 9)/ 10) + 108829) % 48)- -86);
       a24 = 2;
       return 21;
     } else if(( a14 <= -182 && ( a21 <= 127 && ((a24==3) && (((input == 1) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )) && a26 <= -68 ))))){
      a28 = (((a28 - 233422) - -185772) + -552348);
       a24 = 1;
       return -1;
     } else if((((((a24==2) && ((input == 2) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ))) && a21 <= 127 ) && a26 <= -68 ) && ((-182 < a14) && (-114 >= a14)) )){
      a14 = ((((a14 * 16)/ 10) - 324243) * 1);
      a28 = (((a28 / -5) * 4) * 1);
       a24 = 1;
       return -1;
     } else if(((( -84 < a14 && (((a24==2) && (input == 4)) && ((124 < a26) && (217 >= a26)) )) && ((134 < a28) && (300 >= a28)) ) && a21 <= 127 )){
      if( 399 < a21 ){
      a14 = (((((a14 % 299909)+ -300090) - -368972) * 1) - 368972);
      a26 = (((a26 + 80622) + -133314) + -175810);
       a24 = 3;
      } else{
       a26 = (((a26 * 5) - 163628) + -52262);
       a28 = (((((a28 % 48)+ 86) - 46) + 197564) + -197529);
      } return -1;
     } else if((( a14 <= -182 && ( a21 <= 127 && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 4)) && (a24==2)))) && ((124 < a26) && (217 >= a26)) )){
      a26 = ((((a26 * 10)/ -9) * 5) + -176510);
      a28 = ((((a28 % 300018)- 299980) - 2) - 1);
       a24 = 1;
       return -1;
     } else if(((((( ((37 < a28) && (134 >= a28)) && (input == 4)) && (a24==2)) && a14 <= -182 ) && 217 < a26 ) && a21 <= 127 )){
      a26 = ((((((a26 % 95)- -13) * 5) * 5) % 95)- -18);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && (((((input == 3) && ((37 < a28) && (134 >= a28)) ) && -84 < a14 ) && (a24==2)) && a26 <= -68 ))){
      a14 = ((((a14 / 5) + 37014) % 14)+ -100);
      a26 = ((((a26 - -36260) - -320315) % 299891)+ 300108);
      a28 = ((((a28 * -5) * 10)/ 9) + -585792);
       return 21;
     } else if(( ((-68 < a26) && (124 >= a26)) && ((a24==3) && ( a21 <= 127 && ((( ((37 < a28) && (134 >= a28)) && -84 < a14 ) || (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 ))) && (input == 4)))))){
      if( ((203 < a21) && (399 >= a21)) ){
      a14 = (((a14 - 39317) / 5) - -217237);
      a26 = ((((a26 * 5) % 46)+ 171) + -1);
      a28 = (((((a28 % 48)+ 86) - 1) + -494265) + 494266);
       a24 = 1;
      } else{
       a14 = ((((((a14 / 5) % 14)+ -97) * 5) % 14)- 84);
       a28 = ((((((a28 - 0) * 9)/ 10) / 5) % 82)+ 217);
       a24 = 1;
      } return -1;
     } else if(( a26 <= -68 && ((a24==2) && (( a21 <= 127 && (( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 2))) && ((-114 < a14) && (-84 >= a14)) )))){
      a14 = (((a14 + -277459) + 739320) - -23319);
      a26 = ((((a26 % 95)+ 107) + -61) - -37);
      a28 = (((((a28 % 299849)+ 300149) - 0) - 243307) + 243309);
       return 21;
     } else if(( a26 <= -68 && ((a24==2) && ( ((37 < a28) && (134 >= a28)) && (( -84 < a14 && (input == 1)) && a21 <= 127 ))))){
      a14 = ((((a14 + -460442) - 37642) % 299909)+ -300090);
      a28 = ((((a28 + -436128) * 10)/ 9) + -20593);
       a24 = 1;
       return -1;
     } else if(((( a21 <= 127 && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 2)) && (a24==3))) && -84 < a14 ) && a26 <= -68 )){
      a14 = (((((a14 % 14)- 97) + -3) / 5) - 74);
      a26 = ((((((a26 % 46)+ 197) * 5) * 5) % 46)+ 149);
      a28 = ((((a28 % 82)+ 157) - -45) - 43);
       a24 = 2;
       return 25;
     } else if(( 217 < a26 && (( a14 <= -182 && ( ((37 < a28) && (134 >= a28)) && ( a21 <= 127 && (input == 6)))) && (a24==3)))){
      if( a28 <= 37 ){
      a14 = (((a14 / -5) / 5) * 5);
      a26 = ((((a26 / 5) * 4) * 10)/ -9);
      a28 = (((a28 * 5) * 5) + 146574);
       a24 = 2;
      } else{
       a14 = (((a14 / -5) * 4) * 1);
       a26 = (((((a26 % 95)+ 29) - -1) - 240644) + 240595);
       a28 = (((a28 - -160) + -345513) - -345487);
      } return -1;
     } else if(((((a24==2) && ( 217 < a26 && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 6)))) && a21 <= 127 ) && ((-114 < a14) && (-84 >= a14)) )){
      a14 = (((a14 * 5) / 5) / -5);
      a28 = ((((a28 * 9)/ 10) + -13314) / 5);
       return -1;
     } else if(((a24==2) && ( a21 <= 127 && ((input == 1) && (( 300 < a28 && ( -84 < a14 && ((124 < a26) && (217 >= a26)) )) || (( 217 < a26 && a14 <= -182 ) && a28 <= 37 )))))){
      a14 = ((((a14 % 300041)- -299957) - 0) + 0);
      a26 = ((((((a26 - 0) * 9)/ 10) / 5) % 46)+ 148);
      a28 = ((((a28 % 299849)+ 300149) * 1) + 0);
       return 21;
     } else if((((a24==3) && ( a21 <= 127 && ((input == 1) && (( a14 <= -182 && 300 < a28 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))))) && ((-68 < a26) && (124 >= a26)) )){
      a14 = ((((a14 % 299909)- 182) - 84384) - 101323);
      a26 = ((((a26 * 5) * 5) / 5) + -124356);
      a28 = ((((a28 + 0) + 0) % 300018)- 299980);
       a24 = 2;
       return 25;
     } else if(((((((input == 3) && a21 <= 127 ) && ((-182 < a14) && (-114 >= a14)) ) && ((124 < a26) && (217 >= a26)) ) && a28 <= 37 ) && (a24==2))){
      a14 = ((((a14 / 5) - 156256) * 3) * -1);
      a28 = ((((a28 % 82)+ 216) + 0) - -1);
       return 26;
     } else if((((a24==3) && ( a21 <= 127 && (((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 )) || ( -84 < a14 && ((37 < a28) && (134 >= a28)) )) && (input == 5)))) && ((-68 < a26) && (124 >= a26)) )){
      a14 = (((((a14 % 14)+ -99) - -359615) / 5) + -72004);
      a26 = (((((a26 * 5) % 46)+ 170) / 5) + 166);
      a28 = ((((a28 + 0) - 0) % 82)- -216);
       a24 = 1;
       return -1;
     } else if(((((((input == 5) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && 217 < a26 ) && (a24==1)) && -84 < a14 ) && a21 <= 127 )){
      a14 = ((((a14 * 9)/ 10) * 1) - 549809);
      a26 = (((a26 - 600204) + -9) + -5);
      a28 = ((((a28 + -456412) - 143578) + 107177) + -107209);
       return -1;
     } else if(( ((-68 < a26) && (124 >= a26)) && ((a24==2) && ( a21 <= 127 && ( a28 <= 37 && ((input == 6) && a14 <= -182 )))))){
       return 21;
     } else if(((( a26 <= -68 && (((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 5)) && ((-182 < a14) && (-114 >= a14)) )) && (a24==3)) && a21 <= 127 )){
      a14 = (((a14 - 156013) - 145655) + 73089);
      a28 = ((((a28 + -472891) / 5) + 226171) * -2);
       a24 = 1;
       return -1;
     } else if(( ((-114 < a14) && (-84 >= a14)) && (( a21 <= 127 && ((a24==3) && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 6)))) && ((124 < a26) && (217 >= a26)) ))){
      a14 = (((a14 + -563964) / 5) + -300729);
      a28 = ((((a28 * 9)/ 10) / -5) * 5);
       return -1;
     } else if(( a21 <= 127 && (( ((37 < a28) && (134 >= a28)) && ( a14 <= -182 && ( 217 < a26 && (input == 4)))) && (a24==3)))){
      if( ((-68 < a26) && (124 >= a26)) ){
      a14 = (((((a14 * 9)/ 10) % 33)- 135) + 12);
      a26 = ((((a26 % 95)- 44) + 58) - 7);
      a28 = ((((a28 / 5) / 5) + 212181) - 212037);
      } else{
       a26 = ((((a26 + -600157) + -25) / 5) + -476203);
       a28 = ((((a28 / 5) + 128481) / 5) * -5);
       a24 = 2;
      } return 25;
     } else if(((a24==2) && ( a21 <= 127 && (((( a28 <= 37 && ((-114 < a14) && (-84 >= a14)) ) || (( ((-182 < a14) && (-114 >= a14)) && ((134 < a28) && (300 >= a28)) ) || ( ((-182 < a14) && (-114 >= a14)) && 300 < a28 ))) && (input == 3)) && ((-68 < a26) && (124 >= a26)) )))){
      a14 = ((((a14 + -9667) - 27742) % 14)- 95);
      a26 = (((a26 / 5) - -417532) / 5);
      a28 = ((((a28 % 82)+ 218) + -1) + 1);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((a24==3) && ( -84 < a14 && (( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 2))))) && ((124 < a26) && (217 >= a26)) )){
      a14 = ((((a14 % 299909)+ -300090) - 1) - 1);
      a26 = ((((a26 + 60457) - 597562) * 10)/ 9);
      a28 = ((((a28 - -579083) % 82)+ 217) * 1);
       return 25;
     } else if(( a21 <= 127 && ((( ((-68 < a26) && (124 >= a26)) && ((input == 5) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))) && (a24==3)) && a14 <= -182 ))){
      a14 = ((((((a14 % 14)+ -85) - 5) * 5) % 14)+ -89);
      a26 = ((((a26 % 46)+ 171) + -1) - 0);
      a28 = (((((a28 * 9)/ 10) % 82)- -218) - -1);
       a24 = 2;
       return -1;
     } else if((((( a21 <= 127 && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 3))) && ((-182 < a14) && (-114 >= a14)) ) && ((-68 < a26) && (124 >= a26)) ) && (a24==3))){
      a14 = (((a14 + -41266) - 433471) / 5);
      a26 = (((a26 + -17008) - 205443) + -290548);
      a28 = (((a28 * -5) + -583664) + -11318);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( 217 < a26 && (((input == 4) && (( a14 <= -182 && 300 < a28 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))) && a21 <= 127 )))){
      a14 = ((((((a14 + 0) * 9)/ 10) + -27775) % 33)+ -126);
      a28 = ((((a28 % 299849)+ 300149) - -1) - 0);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ((((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 4)) && -84 < a14 ) && a26 <= -68 ) && (a24==3)))){
      a14 = ((((a14 / 5) * 4) - -104805) + -696272);
      a28 = ((((a28 / -5) / 5) - -68650) + -362388);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( a14 <= -182 && (( a26 <= -68 && ((input == 4) && ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && (a24==2))))){
      a28 = ((((a28 % 300018)- 299980) * 1) - 0);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ((( ((-68 < a26) && (124 >= a26)) && (input == 5)) && a28 <= 37 ) && (a24==2))) && -84 < a14 )){
      if( ((-114 < a14) && (-84 >= a14)) ){
      a14 = (((((a14 % 14)- 99) - -1) / 5) - 82);
      a26 = (((a26 + -232163) - 174746) * 1);
      a28 = (((((a28 * 9)/ 10) / 5) % 82)- -217);
       a24 = 3;
      } else{
       a14 = ((((a14 % 33)+ -146) + -353152) - -353149);
       a26 = (((a26 + 469043) * 1) + 85319);
       a28 = (((((a28 % 82)- -217) - -207925) + 349762) + -557687);
      } return 25;
     } else if(((a24==3) && ((( a28 <= 37 && ( a21 <= 127 && (input == 6))) && ((-182 < a14) && (-114 >= a14)) ) && a26 <= -68 ))){
      a14 = (((a14 - 115796) / 5) + 23095);
      a26 = ((((a26 % 46)- -213) + -39) * 1);
       a24 = 2;
       return 26;
     } else if(((a24==2) && ( a26 <= -68 && (( a14 <= -182 && ((input == 3) && a21 <= 127 )) && ((134 < a28) && (300 >= a28)) )))){
      a14 = (((a14 - -600159) * 1) - -11);
       return 26;
     } else if((( ((-68 < a26) && (124 >= a26)) && ((a24==3) && ( ((-114 < a14) && (-84 >= a14)) && ((input == 3) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ))))) && a21 <= 127 )){
      a14 = (((a14 + 290620) * 2) + 3330);
      a28 = (((((a28 * 9)/ 10) + -51870) - -523533) + -508352);
       a24 = 2;
       return 26;
     } else if(( a21 <= 127 && ( ((-114 < a14) && (-84 >= a14)) && ( 217 < a26 && ((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 2)) && (a24==2)))))){
      a14 = (((a14 - -144997) * 4) / 5);
      a28 = (((((a28 + 534307) % 48)- -86) / 5) - -60);
       return 25;
     } else if(((a24==3) && ( ((-182 < a14) && (-114 >= a14)) && (((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 3)) && a21 <= 127 ) && a26 <= -68 )))){
      if((a24==3)){
      a26 = ((((a26 % 95)+ 102) - 14804) + 14765);
      a28 = ((((a28 % 299849)- -301) - -116285) - -107165);
      } else{
       a14 = (((a14 - -353831) * 1) + 36539);
       a28 = ((((a28 * 9)/ 10) / 5) + -164381);
      } return 25;
     } else if(( ((-68 < a26) && (124 >= a26)) && (( a14 <= -182 && (((a24==2) && (input == 3)) && a21 <= 127 )) && a28 <= 37 ))){
      a26 = ((((a26 - 533451) * 10)/ 9) / 5);
       a24 = 1;
       return -1;
     } else if((((input == 4) && ((( ((134 < a28) && (300 >= a28)) && ((a24==2) && ( 217 < a26 && -84 < a14 ))) || ( 300 < a28 && ((a24==2) && ( -84 < a14 && 217 < a26 )))) || (((a24==3) && ( a14 <= -182 && a26 <= -68 )) && a28 <= 37 ))) && a21 <= 127 )){
      a14 = (((((a14 % 299909)+ -300090) - -24268) * 1) - 24268);
      a26 = ((((a26 + 0) % 299966)+ -300033) * 1);
      a28 = ((((a28 % 300018)+ -299980) - 1) - 1);
       a24 = 1;
       return -1;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ( 217 < a26 && ( a21 <= 127 && ((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 6)) && (a24==2)))))){
      a14 = (((a14 + -272224) + 620977) + -638863);
      a28 = (((a28 / 5) / -5) + -225803);
       return -1;
     } else if((((( a14 <= -182 && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 5))) && (a24==2)) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )){
      a26 = ((((a26 + -384287) + 531004) / 5) + -447630);
      a28 = (((((a28 * 9)/ 10) / 5) - 36302) + -337872);
       a24 = 1;
       return -1;
     } else if((( a26 <= -68 && ((a24==2) && ( a14 <= -182 && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 1))))) && a21 <= 127 )){
      a28 = (((((a28 % 300018)+ -299980) + -2) + 527117) - 527115);
       a24 = 1;
       return -1;
     } else if(( ((-114 < a14) && (-84 >= a14)) && (( ((-68 < a26) && (124 >= a26)) && ( 300 < a28 && ((input == 1) && (a24==2)))) && a21 <= 127 ))){
      a14 = (((a14 - -203406) - 732624) * 1);
      a26 = (((a26 - 84312) + -320342) * 1);
      a28 = (((((a28 + 0) % 48)- -83) + -109661) + 109634);
       return 25;
     } else if((( -84 < a14 && ( a28 <= 37 && (( a26 <= -68 && (input == 2)) && a21 <= 127 ))) && (a24==3))){
      a14 = ((((a14 * 9)/ 10) + -566897) + -12093);
      a26 = (((((a26 % 299891)- -300108) * 1) * 10)/ 9);
      a28 = (((((a28 % 299849)- -300149) + 0) - 504805) + 504806);
       a24 = 1;
       return -1;
     } else if(( a26 <= -68 && ((a24==2) && (( a21 <= 127 && ((input == 5) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )))) && ((-182 < a14) && (-114 >= a14)) )))){
      a14 = ((((a14 + 151174) * 10)/ 9) * 3);
      a26 = (((((a26 * 9)/ 10) % 95)+ 69) - -10);
      a28 = (((a28 - 599967) * 1) * 1);
       return 26;
     } else if(( ((-182 < a14) && (-114 >= a14)) && (( a21 <= 127 && (((input == 6) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )) && ((124 < a26) && (217 >= a26)) )) && (a24==2)))){
      a26 = (((((a26 * 18)/ 10) * 10)/ 9) * 5);
      a28 = (((((a28 + 0) / 5) - 469686) % 48)- -85);
       a24 = 1;
       return -1;
     } else if(((( a21 <= 127 && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 3)) && (a24==2))) && -84 < a14 ) && ((-68 < a26) && (124 >= a26)) )){
      a14 = ((((a14 - 0) % 14)- 98) + 1);
      a26 = (((a26 + -577956) + -7978) - 702);
      a28 = (((a28 + -356824) + -243223) - 29);
       return 25;
     } else if(((a24==2) && (((((input == 3) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && a21 <= 127 ) && ((124 < a26) && (217 >= a26)) ) && ((-114 < a14) && (-84 >= a14)) ))){
      a26 = (((((((a26 * 10)/ -9) * 10)/ 9) - -123948) * -1)/ 10);
      a28 = (((((a28 - 0) * 9)/ 10) * 1) + 574821);
       return -1;
     } else if(( a28 <= 37 && (( a21 <= 127 && (( a26 <= -68 && (input == 1)) && -84 < a14 )) && (a24==3)))){
      a14 = (((((a14 % 14)- 97) + -10750) / 5) + 2078);
      a28 = (((((a28 % 299849)+ 300149) - -2) + -515764) - -515763);
       a24 = 2;
       return 25;
     } else if(((a24==3) && ( a21 <= 127 && ( a26 <= -68 && ( -84 < a14 && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 1))))))){
      a14 = ((((a14 % 299909)+ -300090) / 5) + -394568);
      a26 = (((a26 / 5) * 4) - -581241);
      a28 = (((a28 + -540909) * 1) - 37774);
       a24 = 2;
       return 25;
     } else if(((a24==3) && ((( ((-182 < a14) && (-114 >= a14)) && ((input == 5) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))) && a21 <= 127 ) && ((124 < a26) && (217 >= a26)) ))){
      if( ((203 < a21) && (399 >= a21)) ){
      a26 = (((a26 - 546616) - 50934) * 1);
      a28 = (((((a28 % 48)- -84) * 9)/ 10) - -5);
       a24 = 1;
      } else{
       a26 = (((((a26 * 10)/ 5) / 5) * 44)/ 10);
       a28 = ((((a28 - 0) % 82)- -148) - -29);
       a24 = 1;
      } return -1;
     } else if((((a24==3) && ( ((124 < a26) && (217 >= a26)) && ( ((-182 < a14) && (-114 >= a14)) && ((input == 1) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))))) && a21 <= 127 )){
      a26 = (((((a26 + 182512) * 10)/ 9) * 10)/ 9);
      a28 = (((((a28 * 9)/ 10) * 1) / 5) + 265006);
       a24 = 2;
       return 21;
     } else if(((((a24==3) && ( -84 < a14 && ((input == 4) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )))) && ((124 < a26) && (217 >= a26)) ) && a21 <= 127 )){
      a26 = (((a26 / 5) + -464524) + 858123);
      a28 = (((a28 + 282579) / 5) + 345679);
       a24 = 2;
       return 26;
     } else if(( ((124 < a26) && (217 >= a26)) && ( a21 <= 127 && (((a24==3) && ((input == 2) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ))) && ((-114 < a14) && (-84 >= a14)) )))){
      if( ((-68 < a26) && (124 >= a26)) ){
      a26 = (((a26 / 5) / 5) - -404033);
      a28 = (((a28 - 600031) + -3) + -2);
       a24 = 1;
      } else{
       a28 = ((((a28 * 9)/ 10) - -20516) * 1);
       a24 = 1;
      } return 25;
     } else if((((a24==2) && ( a21 <= 127 && ( a14 <= -182 && ( ((134 < a28) && (300 >= a28)) && (input == 5))))) && 217 < a26 )){
      a14 = (((((a14 % 14)+ -90) - 86004) / 5) + 17114);
      a26 = ((((a26 % 46)+ 150) - -213584) - 213606);
       return -1;
     } else if(( a21 <= 127 && ((((( a14 <= -182 && a26 <= -68 ) && (a24==3)) && a28 <= 37 ) || ((((a24==2) && ( -84 < a14 && 217 < a26 )) && ((134 < a28) && (300 >= a28)) ) || ( 300 < a28 && ((a24==2) && ( 217 < a26 && -84 < a14 ))))) && (input == 1)))){
      a14 = ((((a14 % 299909)+ -300090) * 1) * 1);
      a26 = ((((a26 % 299966)- 300033) - 1) + -1);
      a28 = ((((a28 % 300018)- 299980) + -2) * 1);
       a24 = 2;
       return 25;
     } else if(((a24==3) && (((((input == 6) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 )) && a14 <= -182 ) && a21 <= 127 ) && 217 < a26 ))){
      if( ((124 < a26) && (217 >= a26)) ){
      a14 = (((((a14 + 0) * 9)/ 10) % 33)+ -141);
      a26 = (((((a26 + 0) / 5) * 4) % 95)+ 15);
      a28 = (((a28 + -600122) + -2) + -1);
       a24 = 1;
      } else{
       a26 = ((((a26 * 9)/ 10) - -44186) + -603190);
       a28 = ((((a28 / 5) % 48)+ 41) - 1);
       a24 = 1;
      } return -1;
     } else if(((a24==3) && ( a21 <= 127 && ((( 300 < a28 && ( ((-68 < a26) && (124 >= a26)) && -84 < a14 )) || ( a28 <= 37 && ( a14 <= -182 && ((124 < a26) && (217 >= a26)) ))) && (input == 3))))){
      if( 217 < a26 ){
      a14 = ((((a14 % 33)- 147) + -100325) - -100324);
      a26 = (((a26 - 84230) - 360937) * 1);
      a28 = (((((a28 * 9)/ 10) / 5) % 82)+ 217);
       a24 = 1;
      } else{
       a14 = ((((a14 - 0) % 300041)- -299957) - -2);
       a26 = ((((((a26 % 95)- -29) - -1) * 5) % 95)+ 27);
       a28 = ((((a28 / 5) % 82)+ 217) - -2);
      } return 25;
     } else if(( a21 <= 127 && (( -84 < a14 && ((a24==1) && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 1)))) && 217 < a26 ))){
      a14 = ((((a14 % 299909)- 300090) + -1) + -1);
      a26 = ((((a26 * 9)/ 10) / 5) - 537431);
      a28 = (((((a28 - 0) % 82)- -188) / 5) + 189);
       a24 = 2;
       return 25;
     } else if(((( ((-68 < a26) && (124 >= a26)) && (( a14 <= -182 && (input == 5)) && a28 <= 37 )) && (a24==2)) && a21 <= 127 )){
      a26 = (((a26 + -492947) * 1) / 5);
       a24 = 1;
       return -1;
     } else if(( ((124 < a26) && (217 >= a26)) && ( a14 <= -182 && ((a24==3) && ( a21 <= 127 && ((input == 4) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ))))))){
      a14 = ((((a14 + 146292) % 14)- 97) - 1);
      a26 = ((((a26 * 5) % 95)- 65) - -16);
      a28 = (((a28 - 0) / 5) - -467701);
       a24 = 1;
       return -1;
     } else if(( a26 <= -68 && ( ((-114 < a14) && (-84 >= a14)) && ((a24==3) && (((input == 4) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) )) && a21 <= 127 ))))){
      a14 = ((((a14 - -412278) + 82632) * -1)/ 10);
      a28 = ((((a28 % 300018)+ -299980) - 3) - 0);
       a24 = 1;
       return -1;
     } else if((((a24==3) && ( ((-182 < a14) && (-114 >= a14)) && (((input == 1) && ( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ))) && a21 <= 127 ))) && a26 <= -68 )){
      a26 = ((((((a26 * 9)/ 10) % 46)- -195) * 10)/ 9);
      a28 = (((((a28 % 82)+ 200) * 9)/ 10) - -46);
       a24 = 2;
       return 21;
     } else if(( a26 <= -68 && ( ((-114 < a14) && (-84 >= a14)) && (((a24==3) && ( a21 <= 127 && (input == 5))) && 300 < a28 )))){
      a26 = (((((a26 * 9)/ 10) + 26433) % 95)+ 28);
      a28 = (((a28 - 600041) + -31) / 5);
       a24 = 1;
       return -1;
     } else if(((((a24==2) && (((input == 2) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )) && ((124 < a26) && (217 >= a26)) )) && ((-182 < a14) && (-114 >= a14)) ) && a21 <= 127 )){
      a14 = (((a14 / 5) + 573294) * 1);
      a28 = ((((a28 + 0) % 82)- -156) + 29);
       return 25;
     } else if(((( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && ((input == 1) && a28 <= 37 ))) && a14 <= -182 ) && (a24==2))){
      a26 = ((((a26 + 477785) * 1) * -1)/ 10);
       a24 = 1;
       return -1;
     } else if(( -84 < a14 && (( ((-68 < a26) && (124 >= a26)) && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 6)) && (a24==2))) && a21 <= 127 ))){
      a14 = (((((a14 * 9)/ 10) + -155015) % 33)- 146);
      a26 = (((a26 * 5) + 135744) + 460313);
      a28 = ((((a28 * 9)/ 10) - 349295) + -223702);
       return 21;
     } else if(( a21 <= 127 && ((((( 300 < a28 || ( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) )) && (input == 2)) && a14 <= -182 ) && (a24==2)) && ((-68 < a26) && (124 >= a26)) ))){
      a26 = ((((a26 + -121513) * 4) * 10)/ 9);
      a28 = ((((a28 - 0) / 5) + 173408) * -2);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( a26 <= -68 && ( -84 < a14 && ( ((37 < a28) && (134 >= a28)) && ((a24==2) && (input == 4))))))){
      a26 = ((((a26 + 130181) % 46)- -171) * 1);
      a28 = (((a28 + 172363) / 5) - -524270);
       return 21;
     } else if((( a21 <= 127 && ( ((-114 < a14) && (-84 >= a14)) && (( ((124 < a26) && (217 >= a26)) && (input == 6)) && (a24==3)))) && a28 <= 37 )){
      if( -84 < a14 ){
      a14 = ((((a14 - 477732) * 10)/ 9) * 1);
      a26 = ((((a26 * 10)/ -9) * 5) / 5);
      a28 = ((((a28 / 5) % 48)+ 86) * 1);
       a24 = 1;
      } else{
       a26 = (((a26 / 5) / 5) - -53);
       a28 = ((((a28 % 299849)+ 300149) * 1) * 1);
       a24 = 1;
      } return -1;
     } else if((( a21 <= 127 && ((a24==2) && ( ((124 < a26) && (217 >= a26)) && (( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 3))))) && a14 <= -182 )){
      a14 = (((a14 / 5) + 550351) * 1);
      a28 = (((((a28 % 48)- -85) + 486694) + -162552) - 324141);
       return 21;
     } else if((((((( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 )) && (input == 1)) && (a24==2)) && a21 <= 127 ) && a26 <= -68 )){
      a14 = ((((((a14 % 299909)+ -182) / 5) - -554173) * -1)/ 10);
      a26 = (((((a26 * 9)/ 10) % 95)- -45) - 11);
      a28 = (((((a28 % 48)+ 86) + -1) + -329952) + 329953);
       return 21;
     } else if(( a28 <= 37 && ((a24==3) && (( ((-182 < a14) && (-114 >= a14)) && ((input == 4) && 217 < a26 )) && a21 <= 127 )))){
      if( 217 < a26 ){
      a14 = (((a14 - 259540) - 94128) - 73803);
      a26 = ((((a26 / 5) + 398744) + 67902) - 821432);
      a28 = ((((a28 % 82)- -216) + 2) + -1);
       a24 = 1;
      } else{
       a14 = ((((a14 / 5) * 5) * 5) + 330504);
       a26 = ((((a26 % 46)- -132) + -309921) + 309938);
       a28 = (((((a28 + 0) % 48)+ 85) / 5) + 101);
      } return 25;
     } else if(((a24==2) && ( ((-68 < a26) && (124 >= a26)) && ( ((-114 < a14) && (-84 >= a14)) && ((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 4)) && a21 <= 127 ))))){
      a14 = (((a14 + -482752) - 3881) + -14635);
      a26 = (((a26 + -300594) + -181450) - 100396);
      a28 = (((a28 / 5) - -176720) - 329762);
       a24 = 1;
       return -1;
     } else if(( a14 <= -182 && (( a21 <= 127 && ( 217 < a26 && (( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 2)))) && (a24==3)))){
      a14 = (((((a14 % 14)- 93) - 367843) + 801056) - 433211);
      a26 = ((((a26 * -4)/ 10) / 5) * 5);
      a28 = ((((((a28 * 9)/ 10) / 5) * 5) % 48)+ 61);
       a24 = 1;
       return 26;
     } else if(((((a24==2) && ((( ((134 < a28) && (300 >= a28)) || 300 < a28 ) && (input == 1)) && a21 <= 127 )) && -84 < a14 ) && a26 <= -68 )){
      a14 = ((((a14 % 299909)+ -300090) - 1) + -1);
      a28 = ((((a28 / -5) + 562827) - 219920) * -1);
       a24 = 1;
       return -1;
     } else if(((((a24==2) && (((input == 6) && ( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) ))) && a21 <= 127 )) && ((-114 < a14) && (-84 >= a14)) ) && a26 <= -68 )){
      a14 = (((a14 - 79221) - 331392) / 5);
      a28 = ((((a28 / 5) + -195439) + 447529) * -2);
       a24 = 1;
       return -1;
     } else if((((((input == 4) && ((( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( a28 <= 37 && -84 < a14 )) || ( ((37 < a28) && (134 >= a28)) && -84 < a14 ))) && ((124 < a26) && (217 >= a26)) ) && (a24==2)) && a21 <= 127 )){
      a14 = (((((a14 % 300041)- -299957) - -2) + -464541) + 464541);
      a26 = ((((a26 - -110877) * 10)/ -9) - 263161);
      a28 = (((((a28 % 48)+ 85) * 5) % 48)+ 84);
       return 25;
     } else if((( -84 < a14 && (( a21 <= 127 && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 5))) && a26 <= -68 )) && (a24==3))){
      a14 = ((((a14 % 299909)+ -300090) + 347052) - 347052);
      a26 = (((a26 / 5) + 161588) * 3);
      a28 = ((((a28 + -573306) * 1) % 48)+ 86);
       a24 = 2;
       return 21;
     } else if(((((( a21 <= 127 && (input == 6)) && (a24==3)) && 217 < a26 ) && a28 <= 37 ) && a14 <= -182 )){
      if( ((124 < a26) && (217 >= a26)) ){
      a14 = (((a14 / 5) + 344904) * 1);
      a26 = (((((a26 % 95)- -21) * 5) % 95)+ 28);
      a28 = (((((a28 / 5) % 48)- -86) + 319814) - 319814);
       a24 = 2;
      } else{
       a14 = ((((a14 / 5) - -215558) * 10)/ 9);
       a26 = ((((a26 - 126036) / 5) % 46)+ 170);
       a28 = ((((a28 - 0) - 0) % 82)+ 218);
       a24 = 1;
      } return 21;
     } else if((((((input == 3) && (( 300 < a28 && ((-114 < a14) && (-84 >= a14)) ) || ( -84 < a14 && a28 <= 37 ))) && a21 <= 127 ) && (a24==2)) && a26 <= -68 )){
      if( 399 < a21 ){
      a14 = (((((a14 / 5) * 10)/ 9) * 10)/ 9);
      a28 = ((((((a28 * 9)/ 10) % 300018)+ -299980) - -90800) - 90800);
       a24 = 3;
      } else{
       a14 = (((((a14 % 33)- 148) * 1) / 5) - 93);
       a26 = ((((a26 % 95)+ 72) + 396546) - 396497);
       a28 = ((((a28 % 299849)+ 300149) / 5) - -2557);
       a24 = 3;
      } return 25;
     } else if(((((((a24==3) && (input == 3)) && ((-114 < a14) && (-84 >= a14)) ) && 300 < a28 ) && a26 <= -68 ) && a21 <= 127 )){
      a14 = ((((a14 / 5) - 160179) + 39379) + 120693);
      a28 = (((((a28 + -573486) % 48)- -86) - 478885) - -478885);
       a24 = 1;
       return -1;
     } else if(((a24==2) && ( a21 <= 127 && ((input == 2) && (( 300 < a28 && ( -84 < a14 && ((124 < a26) && (217 >= a26)) )) || ( a28 <= 37 && ( 217 < a26 && a14 <= -182 ))))))){
      a14 = (((((a14 - 0) % 14)+ -98) + -472357) + 472357);
      a26 = (((a26 + -79858) + -520218) - 37);
      a28 = (((((a28 % 300018)+ -299980) / 5) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if((( 217 < a26 && (((input == 3) && (( 300 < a28 && a14 <= -182 ) || ( ((-182 < a14) && (-114 >= a14)) && a28 <= 37 ))) && (a24==2))) && a21 <= 127 )){
      if( 300 < a28 ){
      a14 = ((((((a14 % 299909)+ -182) - -536006) / 5) * -1)/ 10);
      a26 = (((((a26 / 5) % 95)- 25) + 386296) - 386311);
      a28 = ((((((a28 + 0) % 82)+ 216) * 5) % 82)- -165);
       a24 = 3;
      } else{
       a14 = ((((a14 * 9)/ 10) + -6690) / 5);
       a28 = ((((a28 % 82)- -216) + 0) + 2);
      } return -1;
     } else if(( a26 <= -68 && (( 300 < a28 && (((input == 6) && a21 <= 127 ) && (a24==3))) && ((-114 < a14) && (-84 >= a14)) ))){
      a26 = (((((a26 % 46)+ 214) + 262262) * 2) - 524736);
      a28 = (((((a28 % 82)- -198) * 5) % 82)- -212);
       a24 = 2;
       return 26;
     } else if(((a24==3) && (((input == 6) && ((( -84 < a14 && ((-68 < a26) && (124 >= a26)) ) && 300 < a28 ) || (( a14 <= -182 && ((124 < a26) && (217 >= a26)) ) && a28 <= 37 ))) && a21 <= 127 ))){
      a14 = (((((a14 % 300041)- -299957) - 320454) / 5) + 210816);
      a26 = (((a26 + -246364) + 385521) + 393216);
      a28 = (((((a28 + 0) - 0) - 0) % 82)- -217);
       a24 = 1;
       return 25;
     } else if(( ((-68 < a26) && (124 >= a26)) && ( a21 <= 127 && (((input == 2) && (( 300 < a28 && a14 <= -182 ) || ( a28 <= 37 && ((-182 < a14) && (-114 >= a14)) ))) && (a24==3))))){
      a14 = ((((a14 % 299909)+ -182) - 241813) - 48065);
      a26 = ((((a26 % 46)+ 171) / 5) * 5);
      a28 = (((((a28 % 299849)+ 300149) * 1) / 5) - -174154);
       a24 = 1;
       return -1;
     } else if(((((( ((134 < a28) && (300 >= a28)) && (input == 4)) && -84 < a14 ) && ((-68 < a26) && (124 >= a26)) ) && a21 <= 127 ) && (a24==3))){
      a14 = ((((a14 % 299909)- 300090) * 1) - 2);
      a26 = (((a26 - 308988) / 5) - 143502);
      a28 = ((((a28 % 48)- -60) + -361970) - -361982);
       a24 = 1;
       return 26;
     } else if(((a24==2) && ( a21 <= 127 && ( ((-68 < a26) && (124 >= a26)) && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 6)) && ((-182 < a14) && (-114 >= a14)) ))))){
      a14 = ((((((a14 % 14)+ -84) + -12) / 5) * 49)/ 10);
      a26 = ((((a26 - -533792) * 1) % 46)+ 167);
      a28 = ((((a28 * 9)/ 10) * 1) - 52880);
       return 26;
     } else if(((a24==2) && ( a21 <= 127 && ( -84 < a14 && ( ((-68 < a26) && (124 >= a26)) && ((input == 4) && ( ((134 < a28) && (300 >= a28)) || 300 < a28 ))))))){
      a28 = ((((a28 / 5) - -366592) * 10)/ 9);
       return 21;
     } else if((( a21 <= 127 && (( ((-68 < a26) && (124 >= a26)) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) && (input == 5))) && ((-114 < a14) && (-84 >= a14)) )) && (a24==2))){
      a26 = (((a26 + 390814) + 27950) * 1);
      a28 = ((((a28 / -5) + 353873) / 5) - 199773);
       return 21;
     } else if(((((( a26 <= -68 && (input == 2)) && a28 <= 37 ) && ((-182 < a14) && (-114 >= a14)) ) && (a24==3)) && a21 <= 127 )){
      a14 = (((a14 - 599040) * 1) + -477);
      a26 = (((((a26 % 46)- -181) / 5) + 580927) + -580769);
      a28 = ((((a28 * 9)/ 10) + 597658) * 1);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( a26 <= -68 && ( a14 <= -182 && ((a24==2) && ((input == 4) && ((134 < a28) && (300 >= a28)) )))))){
      a28 = (((a28 - 88518) + 332612) - -185866);
       a24 = 3;
       return 25;
     } else if(((((((( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 ) && (input == 2)) && (a24==1)) && a21 <= 127 ) && 217 < a26 ) && -84 < a14 )){
      a14 = (((a14 / 5) - 359586) - 188227);
      a26 = ((((a26 / 5) * 4) * 10)/ -9);
      a28 = (((a28 + -599987) * 1) / 5);
       return -1;
     } else if(( ((-182 < a14) && (-114 >= a14)) && ( a28 <= 37 && (( 217 < a26 && ((input == 1) && (a24==3))) && a21 <= 127 )))){
      a26 = ((((a26 * -4)/ 10) + -285219) * 1);
      a28 = (((((a28 % 82)+ 217) + -534122) / 5) + 107021);
       a24 = 1;
       return 26;
     } else if((( 217 < a26 && (((( ((134 < a28) && (300 >= a28)) || ( a28 <= 37 || ((37 < a28) && (134 >= a28)) )) && (input == 3)) && (a24==2)) && a21 <= 127 )) && ((-114 < a14) && (-84 >= a14)) )){
      a14 = ((((a14 + -216626) * 2) / 5) + 593537);
      a26 = (((((a26 % 95)+ -21) - -256088) * 2) + -512198);
      a28 = (((((a28 % 299849)- -300149) / 5) - 55932) + 56534);
       a24 = 1;
       return -1;
     } else if(( a26 <= -68 && (( a21 <= 127 && (((input == 3) && a28 <= 37 ) && ((-182 < a14) && (-114 >= a14)) )) && (a24==3)))){
      a28 = ((((a28 % 48)- -86) + 428893) + -428893);
       a24 = 1;
       return -1;
     } else if((( ((-68 < a26) && (124 >= a26)) && ((((a24==2) && (input == 6)) && ((-114 < a14) && (-84 >= a14)) ) && 300 < a28 )) && a21 <= 127 )){
      a26 = (((a26 / 5) + 139) + -1);
       return 21;
     } else if(( ((-182 < a14) && (-114 >= a14)) && (( a21 <= 127 && ((a24==2) && ((input == 3) && (( ((37 < a28) && (134 >= a28)) || ((134 < a28) && (300 >= a28)) ) || 300 < a28 )))) && 217 < a26 ))){
      a14 = (((a14 + 324662) - 464981) - -345313);
      a26 = ((((a26 - 0) - 307979) / 5) - 367291);
      a28 = ((((a28 + -539020) % 82)- -218) * 1);
       return -1;
     } else if(( a21 <= 127 && (((a24==2) && ( ((134 < a28) && (300 >= a28)) && ((input == 2) && a26 <= -68 ))) && a14 <= -182 ))){
      a28 = (((a28 - -195508) + -390142) - 230776);
       a24 = 1;
       return -1;
     } else if((( a21 <= 127 && ( -84 < a14 && (((a24==3) && (input == 6)) && ((-68 < a26) && (124 >= a26)) ))) && ((134 < a28) && (300 >= a28)) )){
      if( ((127 < a21) && (203 >= a21)) ){
      a14 = (((a14 / 5) - 559557) - 19071);
      a26 = (((((a26 + -421182) % 46)+ 193) * 9)/ 10);
      a28 = ((((a28 * 10)/ 4) + 431156) + 106529);
       a24 = 1;
      } else{
       a26 = (((a26 + -74336) / 5) - 416304);
       a24 = 2;
      } return -1;
     } else if((((a24==2) && ((input == 5) && ((( -84 < a14 && ((124 < a26) && (217 >= a26)) ) && 300 < a28 ) || ( a28 <= 37 && ( a14 <= -182 && 217 < a26 ))))) && a21 <= 127 )){
      a14 = (((((a14 + 0) / 5) + 348972) * -1)/ 10);
      a26 = (((a26 / 5) + -388035) - 71649);
      a28 = ((((a28 % 82)+ 218) + 1) - 2);
       return 25;
     } else if(( a21 <= 127 && (((((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) || ((134 < a28) && (300 >= a28)) ) && (input == 5)) && (a24==2)) && ((-114 < a14) && (-84 >= a14)) ) && ((124 < a26) && (217 >= a26)) ))){
      a14 = (((a14 - 55) - -423933) + -423923);
      a26 = (((a26 + 302960) / 5) - 191496);
      a28 = ((((((a28 / 5) % 48)+ 86) * 5) % 48)- -38);
       a24 = 3;
       return 21;
     } else if((( a28 <= 37 && ((a24==3) && ( a26 <= -68 && ((input == 4) && -84 < a14 )))) && a21 <= 127 )){
      a26 = ((((a26 % 46)+ 208) + -309938) - -309907);
      a28 = (((((a28 * 9)/ 10) + 559071) + -50111) + 68264);
       a24 = 1;
       return -1;
     } else if(((a24==2) && (( ((124 < a26) && (217 >= a26)) && ((( a28 <= 37 || ((37 < a28) && (134 >= a28)) ) && (input == 6)) && a14 <= -182 )) && a21 <= 127 ))){
      a26 = (((a26 + -364117) * 1) * 1);
      a28 = (((((a28 % 300018)- 299980) / 5) * 10)/ 9);
       a24 = 1;
       return -1;
     } else if(( a21 <= 127 && ( 217 < a26 && (((input == 2) && (( -84 < a14 && ((37 < a28) && (134 >= a28)) ) || (( ((-114 < a14) && (-84 >= a14)) && 300 < a28 ) || ( a28 <= 37 && -84 < a14 )))) && (a24==2))))){
      a14 = ((((a14 + -393198) % 299909)- 300090) + -2);
      a26 = (((a26 + -600152) + -28) - 28);
      a28 = ((((a28 % 300018)- 299980) * 1) * 1);
       a24 = 1;
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
