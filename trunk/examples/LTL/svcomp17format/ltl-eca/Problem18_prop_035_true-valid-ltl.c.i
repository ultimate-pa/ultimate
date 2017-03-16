
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
  int a18 = 9;
  int a24 = 3;
  int a3 = 99;
  int a15 = 4;
int calculate_output2(int input);
int calculate_output3(int input);
 int calculate_output(int input) {
 if(((((a24==1) && (a18==9)) && (a15==4)) && a3 <= 115 )){
  error_20: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==8)) && (a15==4)) && 417 < a3 )){
  error_34: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==11)) && (a15==4)) && 417 < a3 )){
  error_57: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==8)) && (a15==4)) && a3 <= 115 )){
  error_19: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==8)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_9: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==12)) && (a15==4)) && a3 <= 115 )){
  error_3: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==9)) && (a15==4)) && 417 < a3 )){
  error_55: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==8)) && (a15==4)) && a3 <= 115 )){
  error_39: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==9)) && (a15==4)) && 417 < a3 )){
  error_35: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==10)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_31: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==11)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_52: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==11)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_12: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==9)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_10: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==9)) && (a15==4)) && a3 <= 115 )){
  error_0: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==12)) && (a15==4)) && 417 < a3 )){
  error_38: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==12)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_8: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==8)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_49: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==12)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_33: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==9)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_25: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==10)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_6: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==10)) && (a15==4)) && a3 <= 115 )){
  error_1: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==10)) && (a15==4)) && 417 < a3 )){
  error_36: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==11)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_32: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==9)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_45: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==11)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_27: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==11)) && (a15==4)) && 417 < a3 )){
  error_17: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==8)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_44: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==12)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_53: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==8)) && (a15==4)) && 417 < a3 )){
  error_54: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==9)) && (a15==4)) && 417 < a3 )){
  error_15: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==10)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_46: __VERIFIER_assume(0);
  }
  if(((((a24==3) && (a18==8)) && (a15==4)) && a3 <= 115 )){
  error_59: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==9)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_5: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==8)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_29: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==12)) && (a15==4)) && 417 < a3 )){
  error_58: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==11)) && (a15==4)) && a3 <= 115 )){
  error_22: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==10)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_11: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==9)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_30: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==9)) && (a15==4)) && a3 <= 115 )){
  error_40: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==12)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_13: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==10)) && (a15==4)) && 417 < a3 )){
  error_16: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==11)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_7: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==10)) && (a15==4)) && 417 < a3 )){
  error_56: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==11)) && (a15==4)) && a3 <= 115 )){
  error_42: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==8)) && (a15==4)) && 417 < a3 )){
  error_14: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==8)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_24: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==8)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_4: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==8)) && (a15==4)) && a3 <= 115 )){
  globalError: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==12)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_48: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==12)) && (a15==4)) && a3 <= 115 )){
  error_23: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==11)) && (a15==4)) && 417 < a3 )){
  error_37: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==12)) && (a15==4)) && 417 < a3 )){
  error_18: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==10)) && (a15==4)) && a3 <= 115 )){
  error_21: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==11)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_47: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==10)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_51: __VERIFIER_assume(0);
  }
  if(((((a24==0) && (a18==11)) && (a15==4)) && a3 <= 115 )){
  error_2: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==10)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_26: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==9)) && (a15==4)) && ((306 < a3) && (417 >= a3)) )){
  error_50: __VERIFIER_assume(0);
  }
  if(((((a24==1) && (a18==12)) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
  error_28: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==10)) && (a15==4)) && a3 <= 115 )){
  error_41: __VERIFIER_assume(0);
  }
  if(((((a24==2) && (a18==12)) && (a15==4)) && a3 <= 115 )){
  error_43: __VERIFIER_assume(0);
  }
     if((((input == 5) && (( a3 <= 115 && ((a18==9) && (a24==3))) || (( 417 < a3 && ((a18==12) && (a24==2))) || ( a3 <= 115 && ((a24==3) && (a18==8)))))) && (a15==6))){
      a3 = (((((a3 * 9)/ 10) * 1) % 299791)+ 300208);
       a24 = 3;
       a18 = 8;
       a15 = 4;
       return 22;
     } else if(((a15==5) && ((((input == 6) && ((a18==8) || (a18==9))) && (a24==3)) && 417 < a3 ))){
      a3 = (((a3 - 124953) / 5) + -249228);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==4) && ((a24==4) && (((a18==11) || (a18==12)) && (input == 5)))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 + -235837) + 210119) + -280591);
       a24 = 1;
       a18 = 9;
       a15 = 5;
       return 25;
     } else if((((a24==4) && (((input == 3) && ((a18==9) || (a18==10))) && (a15==4))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 + -125183) + 316577) * -3);
       a24 = 1;
       a18 = 8;
       a15 = 5;
       return 21;
     } else if(( a3 <= 115 && ((((input == 5) && ((a18==9) || (a18==10))) && (a15==5)) && (a24==1)))){
      a3 = ((((a3 + 0) % 95)+ 211) - 1);
       a24 = 0;
       a18 = 10;
       a15 = 6;
       return 21;
     } else if((((a18==10) && (( 417 < a3 && (input == 3)) && (a15==5))) && (a24==3))){
      a3 = ((((((a3 / 5) % 55)+ 356) * 5) % 55)- -314);
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 26;
     } else if((((((((a18==8) || (a18==9)) || (a18==10)) && (input == 2)) && (a15==4)) && (a24==4)) && ((306 < a3) && (417 >= a3)) )){
      a3 = ((((a3 * 5) / 5) * 5) - 511620);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((((a18==11) || (a18==12)) && (input == 5)) && (a15==4)) && ((115 < a3) && (306 >= a3)) ) && (a24==3))){
      a3 = (((a3 * 5) * 5) + 152989);
       a18 = 10;
       return 26;
     } else if(((a18==12) && ((((input == 6) && a3 <= 115 ) && (a24==2)) && (a15==5)))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && (((((a18==10) || (a18==11)) || (a18==12)) && (input == 6)) && (a24==0))) && (a15==5))){
      a3 = (((a3 + -492005) - 108001) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && (((input == 2) && (((a18==12) && ((306 < a3) && (417 >= a3)) ) || ((a18==8) && 417 < a3 ))) && (a15==6)))){
      a3 = (((a3 + -600003) + -276) + -22);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((((((a18==8) || (a18==9)) || (a18==10)) && (input == 3)) && ((115 < a3) && (306 >= a3)) ) && (a24==1)))){
      a3 = ((((((a3 % 55)+ 342) * 9)/ 10) + -61412) + 61448);
       a24 = 4;
       a18 = 10;
       a15 = 4;
       return 25;
     } else if((((a24==0) && ((a15==6) && ((input == 2) && ((a18==9) || (a18==10))))) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 + 28289) * 10)/ 9) - -559528);
       a18 = 10;
       return 26;
     } else if(( ((306 < a3) && (417 >= a3)) && (((a15==5) && ((input == 2) && (a18==12))) && (a24==3)))){
       return 22;
     } else if(((a15==5) && ((a24==2) && ( ((306 < a3) && (417 >= a3)) && (((a18==9) || (a18==10)) && (input == 5)))))){
      a3 = (((a3 + 507676) - -44123) / -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==1) && (((input == 4) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a15==5)))){
      a3 = (((a3 * 5) * 5) - 257753);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && (( a3 <= 115 && (input == 6)) && (a15==5))) && (a18==11))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==10) && ( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((a24==0) && (input == 1)))))){
      a3 = ((((a3 - 489685) - -489506) - -522886) + -522861);
       a24 = 4;
       a18 = 11;
       a15 = 4;
       return 21;
     } else if(((a24==3) && ((a15==6) && (((input == 4) && ((a18==10) || (a18==11))) && 417 < a3 )))){
      a3 = (((a3 - 116826) - 483087) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((( ((306 < a3) && (417 >= a3)) && (a18==12)) || ((a18==8) && 417 < a3 )) || ( 417 < a3 && (a18==9))) && (input == 2)) && (a24==3)) && (a15==6))){
      a3 = (((((a3 - 473859) % 55)- -361) / 5) + 288);
       a24 = 2;
       a18 = 11;
       a15 = 4;
       return -1;
     } else if(((a24==4) && ((a15==4) && ( ((306 < a3) && (417 >= a3)) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 1)))))){
      a3 = ((((a3 * 4)/ 10) + -559800) - -559927);
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return 22;
     } else if(((a15==4) && (( ((306 < a3) && (417 >= a3)) && ((input == 1) && ((a18==10) || ((a18==8) || (a18==9))))) && (a24==3)))){
      a3 = ((((a3 * 4)/ 10) - -595933) + -595866);
       a24 = 4;
       a18 = 12;
       return 21;
     } else if(((a24==2) && ((a15==6) && ( 417 < a3 && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 2)))))){
      a3 = ((((a3 - 0) - 576583) + -1411) - 22284);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 6) && (((a18==9) || (a18==10)) || (a18==11))) && (a24==2)) && (a15==6)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 - 189557) - 119436) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((a24==0) && (((a18==11) || (a18==12)) && (input == 1)))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 / -5) + -114521) + -348481);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a18==12) && (( a3 <= 115 && (input == 1)) && (a24==2))))){
      a3 = ((((((a3 * 9)/ 10) % 95)- -210) / 5) - -204);
       a24 = 1;
       a18 = 11;
       a15 = 4;
       return -1;
     } else if((((a24==3) && ((input == 4) && (((a18==9) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==12)) || ( 417 < a3 && (a18==8)))))) && (a15==6))){
      a3 = ((((((a3 % 55)- -309) - 2) * 5) % 55)+ 348);
       a24 = 0;
       a18 = 11;
       a15 = 4;
       return -1;
     } else if(((((a24==1) && ((input == 1) && (a18==8))) && a3 <= 115 ) && (a15==5))){
      a3 = (((a3 / 5) - -593842) * 1);
       a24 = 4;
       a18 = 10;
       return 25;
     } else if(((a15==4) && ((((((a18==12) && (a24==3)) && 417 < a3 ) || (((a24==4) && (a18==8)) && a3 <= 115 )) || (((a24==4) && (a18==9)) && a3 <= 115 )) && (input == 5)))){
      a3 = (((((a3 * 9)/ 10) + -18815) / 5) - 203034);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==0) && ((a15==6) && ((input == 3) && ((a18==11) || (a18==12))))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 + 245225) + -351147) + -288530);
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==0) && ((a15==6) && ((input == 1) && ((a18==9) || (a18==10))))))){
       a24 = 4;
       a18 = 11;
       a15 = 4;
       return 22;
     } else if(((((a24==2) && ((a15==5) && (input == 2))) && a3 <= 115 ) && (a18==9))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && (((a15==6) && (((a18==9) || (a18==10)) && (input == 5))) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 - 189054) - 142438) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && (((a24==4) && (((a18==9) || (a18==10)) && (input == 4))) && 417 < a3 ))){
      a3 = (((a3 - 600257) + 156422) - 156169);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==5) && ( 417 < a3 && ((a24==1) && ((input == 6) && (a18==11)))))){
      a3 = (((a3 + 0) - 600399) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((( 417 < a3 && ((a24==3) && (a18==12))) || (((a24==4) && (a18==8)) && a3 <= 115 )) || ( a3 <= 115 && ((a24==4) && (a18==9)))) && (input == 2)) && (a15==5))){
      a3 = ((((a3 % 300057)- 299941) + 0) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((((a18==10) || (a18==11)) && (input == 3)) && (a24==3)) && a3 <= 115 ))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((( 417 < a3 && ((a15==5) && ((a18==11) && (a24==4)))) || ( 417 < a3 && ((a15==5) && ((a24==4) && (a18==12))))) || ( a3 <= 115 && ((a15==6) && ((a18==8) && (a24==0))))) && (input == 1))){
      a3 = ((((((a3 * 9)/ 10) % 55)- -362) + -271326) - -271325);
       a24 = 3;
       a18 = 10;
       a15 = 6;
       return 22;
     } else if(((a15==6) && ((( a3 <= 115 && ((a18==9) && (a24==1))) || (( 417 < a3 && ((a18==12) && (a24==0))) || ( a3 <= 115 && ((a18==8) && (a24==1))))) && (input == 2)))){
      a3 = (((((a3 % 299791)+ 300208) + -511595) * 1) - -511597);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==4) && ((( 417 < a3 && (a18==8)) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12)))) && (input == 2))) && (a15==4))){
      a3 = ((((a3 - 246812) % 299791)- -300208) + 1);
       a24 = 1;
       a18 = 9;
       a15 = 5;
       return 26;
     } else if(((a18==11) && (((a24==1) && ((input == 3) && (a15==6))) && ((306 < a3) && (417 >= a3)) ))){
      a3 = ((((a3 - 175271) + 109800) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==5) && ((((a18==9) || (a18==10)) && (input == 5)) && (a24==1))))){
       a18 = 10;
       a15 = 6;
       return 22;
     } else if(((((((a18==8) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 3)) && (a24==3)) && (a15==4))){
      a3 = ((((a3 - 0) + -210150) / 5) + 219839);
       a24 = 4;
       a18 = 11;
       return 26;
     } else if(( ((306 < a3) && (417 >= a3)) && (((((a18==11) || (a18==12)) && (input == 3)) && (a24==0)) && (a15==5)))){
      a3 = (((a3 / -5) + -537874) / 5);
       a24 = 4;
       a18 = 10;
       return 21;
     } else if((( a3 <= 115 && (((input == 2) && (a18==12)) && (a24==2))) && (a15==6))){
       a24 = 1;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a15==6) && ((input == 1) && (a24==0))) && (a18==11)))){
      a3 = (((((a3 + 433729) - -163417) * 1) % 55)+ 344);
       a24 = 3;
       a18 = 8;
       return 25;
     } else if(((a24==3) && ((a15==4) && (((input == 4) && ((a18==11) || (a18==12))) && ((115 < a3) && (306 >= a3)) )))){
      a3 = ((((a3 / -5) * 5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 5)) && 417 < a3 ) && (a15==5)) && (a24==1))){
      a3 = (((a3 / -5) * 4) - 112270);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && (((input == 6) && (((a18==10) || (a18==11)) || (a18==12))) && a3 <= 115 )) && (a24==1))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && (((((a18==9) || (a18==10)) || (a18==11)) && (input == 4)) && 417 < a3 )) && (a15==4))){
      a3 = ((((a3 - 600348) * 1) - -551189) + -550883);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a24==1) && (((a18==11) || (a18==12)) && (input == 4))) && (a15==6)) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 - 106664) * 10)/ 9) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((a24==2) && ((input == 2) && (a18==12))) && a3 <= 115 ))){
      a3 = ((((a3 + 311999) / 5) / 5) - -587471);
       a24 = 3;
       a18 = 10;
       a15 = 6;
       return 22;
     } else if((( ((306 < a3) && (417 >= a3)) && ((((a18==9) || (a18==10)) && (input == 4)) && (a24==2))) && (a15==5))){
      a3 = ((((a3 * 5) * 5) * 5) + -170401);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && ((((((a18==12) && (a24==3)) && 417 < a3 ) || ( a3 <= 115 && ((a24==4) && (a18==8)))) || (((a24==4) && (a18==9)) && a3 <= 115 )) && (input == 2)))){
      a3 = ((((a3 % 300057)- 299941) + -3) + 0);
       a24 = 0;
       a18 = 10;
       a15 = 5;
       return 25;
     } else if((( ((115 < a3) && (306 >= a3)) && (((input == 6) && ((a18==10) || ((a18==8) || (a18==9)))) && (a24==2))) && (a15==6))){
      a3 = (((a3 / -5) * 5) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && ((a24==0) && ((a18==12) && (input == 4)))) && (a15==5))){
      a3 = ((((a3 + -350374) * 1) * 1) + 630246);
       a24 = 3;
       a18 = 10;
       return 21;
     } else if((((((a18==8) && (input == 1)) && ((115 < a3) && (306 >= a3)) ) && (a24==4)) && (a15==4))){
      a3 = ((((a3 - -132427) * 10)/ 9) * 4);
       a24 = 0;
       a18 = 9;
       a15 = 5;
       return 25;
     } else if(((a15==4) && ( ((115 < a3) && (306 >= a3)) && ((a24==3) && ((input == 2) && ((a18==8) || (a18==9))))))){
      a3 = (((a3 + -451078) * 1) + -6890);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==6) && ((((input == 4) && ((a18==9) || (a18==10))) && (a24==0)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 - 570855) + 51748) / 5);
       a24 = 2;
       a18 = 10;
       return 22;
     } else if(( a3 <= 115 && (((a15==5) && ((input == 4) && ((a18==10) || (a18==11)))) && (a24==0)))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((((a18==11) && (a24==1)) && 417 < a3 ) || (((a24==1) && (a18==12)) && 417 < a3 )) || (((a18==8) && (a24==2)) && a3 <= 115 )) && (input == 3)) && (a15==6))){
      a3 = (((((a3 % 300057)- 299941) * 1) - -312324) + -312324);
       a24 = 1;
       a18 = 8;
       return -1;
     } else if((((((a18==12) && (input == 2)) && (a15==6)) && ((306 < a3) && (417 >= a3)) ) && (a24==1))){
       a18 = 8;
       return -1;
     } else if(((a24==4) && ((((input == 2) && ((a18==9) || (a18==10))) && ((115 < a3) && (306 >= a3)) ) && (a15==5)))){
      a3 = (((a3 / 5) + -247996) + -125990);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((((a18==12) && (a24==2)) && 417 < a3 ) || ( a3 <= 115 && ((a18==8) && (a24==3)))) || (((a18==9) && (a24==3)) && a3 <= 115 )) && (input == 3)) && (a15==6))){
      a3 = ((((a3 % 95)- -211) - -90755) - 90754);
       a24 = 2;
       a18 = 9;
       return -1;
     } else if(((a15==4) && (((((a24==4) && (a18==9)) && a3 <= 115 ) || (( 417 < a3 && ((a24==3) && (a18==12))) || ( a3 <= 115 && ((a24==4) && (a18==8))))) && (input == 6)))){
      a3 = ((((a3 % 300057)- 299941) - 3) + 0);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a15==6) && (((input == 5) && ((a18==12) || ((a18==10) || (a18==11)))) && (a24==3))) && a3 <= 115 )){
       a18 = 10;
       return 25;
     } else if(((a24==4) && ( a3 <= 115 && ((a18==10) && ((input == 4) && (a15==5)))))){
       a24 = 2;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((a18==11) && (((a24==1) && (input == 5)) && ((306 < a3) && (417 >= a3)) )))){
       a24 = 0;
       a18 = 10;
       return -1;
     } else if((((((((a24==3) && (a18==12)) && 417 < a3 ) || (((a24==4) && (a18==8)) && a3 <= 115 )) || (((a24==4) && (a18==9)) && a3 <= 115 )) && (input == 5)) && (a15==5))){
      a3 = ((((((a3 * 9)/ 10) % 55)+ 361) - 5570) + 5570);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 26;
     } else if((((a24==2) && (((input == 3) && (a18==9)) && (a15==5))) && a3 <= 115 )){
      a3 = ((((((a3 % 55)- -361) - -1) * 5) % 55)- -321);
       a24 = 3;
       a18 = 8;
       a15 = 6;
       return 22;
     } else if(((( a3 <= 115 && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 2))) && (a15==6)) && (a24==3))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((((input == 4) && ((a18==12) || ((a18==10) || (a18==11)))) && (a15==5)) && (a24==0)))){
      a3 = ((((a3 - 546051) - -353166) + -225492) - 181644);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (( ((115 < a3) && (306 >= a3)) && (((a18==11) || (a18==12)) && (input == 6))) && (a24==4)))){
      a3 = (((a3 + -267207) * 2) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 6) && ((a18==11) || (a18==12))) && ((115 < a3) && (306 >= a3)) ) && (a15==4)) && (a24==3))){
      a3 = (((a3 - 233538) + 304894) * -5);
       a24 = 4;
       a18 = 10;
       return 25;
     } else if(((a15==4) && (((a24==3) && ((input == 4) && ((115 < a3) && (306 >= a3)) )) && (a18==10)))){
      a3 = ((((a3 % 55)- -310) - 182118) - -182144);
       a18 = 12;
       return 22;
     } else if(((a15==5) && (((a24==3) && (((a18==8) || (a18==9)) && (input == 4))) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 / -5) * 5) + -483134);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && (((((a18==11) || ((a18==9) || (a18==10))) && (input == 2)) && 417 < a3 ) && (a24==0)))){
       a18 = 9;
       return 21;
     } else if((( 417 < a3 && ((a24==2) && ((input == 6) && (((a18==9) || (a18==10)) || (a18==11))))) && (a15==6))){
      a3 = ((((a3 - 92069) / 5) * 5) + -508090);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && ((a15==6) && ( ((306 < a3) && (417 >= a3)) && (input == 5)))) && (a18==10))){
       a24 = 0;
       return -1;
     } else if(((((a15==6) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 5))) && (a24==3)) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 + -86655) + -241663) * 10)/ 9);
       a24 = 0;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && ((a24==2) && (((a18==10) || (a18==11)) && (input == 1)))) && (a15==5))){
      a3 = (((((a3 % 55)+ 335) + 127162) - 377530) - -250379);
       a24 = 0;
       a18 = 10;
       a15 = 6;
       return 25;
     } else if(((((((a18==9) && 417 < a3 ) || (((a18==12) && ((306 < a3) && (417 >= a3)) ) || ((a18==8) && 417 < a3 ))) && (input == 6)) && (a24==3)) && (a15==6))){
      a3 = ((((a3 % 299791)+ 418) - -254727) + 15511);
       a24 = 1;
       a18 = 12;
       a15 = 4;
       return -1;
     } else if((((a18==11) && ( ((115 < a3) && (306 >= a3)) && ((a15==6) && (input == 2)))) && (a24==0))){
      a3 = (((((a3 % 55)+ 330) - -551622) / 5) + -110076);
       return 21;
     } else if((((a15==5) && ((input == 2) && (( ((306 < a3) && (417 >= a3)) && (a18==8)) || (( ((115 < a3) && (306 >= a3)) && (a18==11)) || ( ((115 < a3) && (306 >= a3)) && (a18==12)))))) && (a24==2))){
      a3 = (((a3 * 5) / 5) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ( a3 <= 115 && (((a18==10) || (a18==11)) && (input == 1)))) && (a24==0))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && (((a15==6) && ((input == 6) && (a24==0))) && (a18==10)))){
      a3 = ((((a3 * 5) * -5) * 10)/ 9);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((a24==3) && ((input == 4) && (((a18==8) || (a18==9)) || (a18==10))))) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 / -5) + 391912) / 5) + -246982);
       a18 = 10;
       return -1;
     } else if((((a24==1) && ( ((306 < a3) && (417 >= a3)) && ((a15==6) && (input == 4)))) && (a18==10))){
      a3 = (((a3 - 568756) - -39065) + -62303);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && ( ((115 < a3) && (306 >= a3)) && ((input == 2) && ((a18==11) || (a18==12))))) && (a15==6))){
       a18 = 11;
       return 22;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==5) && ((a24==1) && ((input == 2) && ((a18==9) || (a18==10))))))){
       a18 = 11;
       a15 = 6;
       return 25;
     } else if(((((input == 2) && (( ((306 < a3) && (417 >= a3)) && (a18==9)) || (( ((115 < a3) && (306 >= a3)) && (a18==12)) || ((a18==8) && ((306 < a3) && (417 >= a3)) )))) && (a15==6)) && (a24==0))){
      a3 = (((((a3 * 5) % 55)- -358) + 428422) + -428464);
       a24 = 2;
       a18 = 10;
       return 25;
     } else if((((a15==6) && ( 417 < a3 && ((input == 2) && ((a18==10) || (a18==11))))) && (a24==3))){
      a3 = ((((a3 * 9)/ 10) * -1) + -3567);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((((((a18==8) || (a18==9)) || (a18==10)) && (input == 4)) && 417 < a3 ) && (a24==1)))){
      a3 = (((((a3 - 0) % 95)+ 132) * 9)/ 10);
       a24 = 0;
       a18 = 12;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a24==4) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 4)))) && (a15==5))){
       a24 = 1;
       a18 = 10;
       a15 = 6;
       return 25;
     } else if(( 417 < a3 && ((a18==11) && (((input == 2) && (a24==3)) && (a15==5))))){
      a3 = (((a3 / 5) - 194334) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && (((((a18==10) || (a18==11)) && (input == 2)) && a3 <= 115 ) && (a15==6)))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==0) && (((input == 6) && ((a18==11) || (a18==12))) && ((306 < a3) && (417 >= a3)) )) && (a15==6))){
      a3 = (((a3 - 482897) - 10815) - 90332);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && (((a15==5) && ((a24==2) && (input == 1))) && (a18==9)))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && ( ((115 < a3) && (306 >= a3)) && ((a15==6) && ((((a18==8) || (a18==9)) || (a18==10)) && (input == 3)))))){
      a3 = (((((a3 + -167391) % 55)- -414) * 9)/ 10);
       a24 = 1;
       a18 = 12;
       return -1;
     } else if(((( ((115 < a3) && (306 >= a3)) && ((input == 3) && (a24==0))) && (a15==5)) && (a18==12))){
      a3 = (((a3 - -107225) * 5) - 989175);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a18==10) && (((a24==1) && (input == 6)) && (a15==6))))){
      a3 = ((((a3 - 10913) * 5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && (((a24==2) && (input == 2)) && (a18==9))) && (a15==5))){
      a3 = ((((((a3 - 0) * 9)/ 10) / 5) % 95)+ 183);
       a24 = 3;
       a15 = 4;
       return 26;
     } else if(((a24==1) && ((a15==6) && ((a18==10) && ( ((306 < a3) && (417 >= a3)) && (input == 3)))))){
      a3 = (((a3 * 5) * 5) * 5);
       a24 = 4;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 1) && (((((a24==2) && (a18==12)) && 417 < a3 ) || (((a18==8) && (a24==3)) && a3 <= 115 )) || (((a24==3) && (a18==9)) && a3 <= 115 ))) && (a15==5))){
      a3 = ((((a3 + 0) % 300057)+ -299941) - 1);
       a24 = 3;
       a18 = 11;
       a15 = 4;
       return 25;
     } else if(((a24==1) && ((a15==6) && ( ((306 < a3) && (417 >= a3)) && ((a18==12) && (input == 3)))))){
       a18 = 10;
       a15 = 5;
       return 22;
     } else if(((((((a18==8) || (a18==9)) && (input == 3)) && ((115 < a3) && (306 >= a3)) ) && (a24==3)) && (a15==5))){
       a24 = 1;
       a18 = 12;
       a15 = 6;
       return 22;
     } else if((( 417 < a3 && (((input == 1) && ((a18==10) || ((a18==8) || (a18==9)))) && (a24==1))) && (a15==6))){
      a3 = ((((a3 + -202771) % 55)+ 362) + -1);
       a24 = 0;
       a18 = 10;
       return -1;
     } else if((( a3 <= 115 && ((a24==2) && (((a18==10) || (a18==11)) && (input == 6)))) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==1) && ((a15==5) && ((input == 1) && ((a18==9) || (a18==10))))))){
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(( a3 <= 115 && ((a15==6) && ((a24==1) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 4)))))){
      a3 = ((((((a3 % 55)- -362) + -62676) * 5) % 55)+ 372);
       a24 = 0;
       a18 = 11;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((input == 6) && (((a18==9) || (a18==10)) || (a18==11))))) && (a24==3))){
      a3 = (((a3 * 5) * 5) + -452441);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((((((a18==12) && (a24==2)) && 417 < a3 ) || (((a18==8) && (a24==3)) && a3 <= 115 )) || ( a3 <= 115 && ((a18==9) && (a24==3)))) && (input == 1)))){
      a3 = ((((a3 % 55)- -362) - -75998) + -75998);
       a24 = 0;
       a18 = 10;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 2)) && (a15==5)) && (a24==2)) && ((306 < a3) && (417 >= a3)) )){
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 22;
     } else if((( ((306 < a3) && (417 >= a3)) && (((((a18==8) || (a18==9)) || (a18==10)) && (input == 4)) && (a24==0))) && (a15==5))){
      a3 = (((a3 * 5) / -5) - 492008);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ( ((115 < a3) && (306 >= a3)) && ((input == 2) && ((a18==9) || (a18==10))))) && (a24==2))){
      a3 = ((((a3 % 55)+ 358) - -38100) + -38118);
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 22;
     } else if(((a24==0) && (((input == 5) && ((( ((115 < a3) && (306 >= a3)) && (a18==12)) || ( ((306 < a3) && (417 >= a3)) && (a18==8))) || ((a18==9) && ((306 < a3) && (417 >= a3)) ))) && (a15==6)))){
      a3 = (((a3 - 426555) * 1) - 85224);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && (((a24==0) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 3))) && (a15==5)))){
      a3 = ((((a3 % 55)- -349) + 238447) + -238484);
       a24 = 4;
       a18 = 8;
       return 26;
     } else if((((a24==3) && (((input == 6) && (a18==9)) && a3 <= 115 )) && (a15==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a15==5) && ((a18==11) && (input == 5))) && (a24==3)) && ((306 < a3) && (417 >= a3)) )){
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 25;
     } else if(((((((a18==9) || (a18==10)) && (input == 6)) && (a24==1)) && (a15==5)) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 / 5) + -86788) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((a24==4) && ((a15==4) && ((input == 2) && ((a18==9) || (a18==10))))))){
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return 22;
     } else if((((((a24==3) && (input == 1)) && (a15==4)) && ((115 < a3) && (306 >= a3)) ) && (a18==10))){
      a3 = (((a3 / -5) - 495685) + -6188);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==4) && ((a15==4) && ((input == 4) && ((a18==11) || (a18==12))))) && 417 < a3 )){
      a3 = (((a3 - 600119) + -213) + -49);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==0) && ((((input == 5) && ((a18==11) || ((a18==9) || (a18==10)))) && (a15==5)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((((a3 + 74903) % 55)- -322) + 86378) - 86375);
       a24 = 3;
       a18 = 11;
       return 26;
     } else if((((( 417 < a3 && ((a24==1) && (a18==12))) || ( a3 <= 115 && ((a24==2) && (a18==8)))) && (input == 4)) && (a15==5))){
      a3 = ((((a3 % 300057)+ -299941) * 1) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ( ((115 < a3) && (306 >= a3)) && ((input == 6) && ((a18==9) || (a18==10))))) && (a24==2))){
      a3 = (((a3 - 499587) - -528266) + 565008);
       a24 = 1;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && (((a15==5) && ((a24==4) && (input == 5))) && (a18==10)))){
       a24 = 3;
       a18 = 8;
       a15 = 6;
       return 26;
     } else if(((a15==6) && (((((a18==9) && (a24==3)) && a3 <= 115 ) || ((((a24==2) && (a18==12)) && 417 < a3 ) || (((a18==8) && (a24==3)) && a3 <= 115 ))) && (input == 6)))){
      a3 = (((((a3 * 9)/ 10) + -18293) % 300057)- 299941);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && (( ((115 < a3) && (306 >= a3)) && ((input == 3) && ((a18==11) || (a18==12)))) && (a15==4)))){
      a3 = ((((a3 * 5) - -136601) * 4) * -1);
       a24 = 4;
       a18 = 11;
       return 22;
     } else if(((((a24==3) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 6))) && a3 <= 115 ) && (a15==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==5) && ( 417 < a3 && ((a18==11) && ((a24==3) && (input == 3)))))){
      a3 = (((((a3 * 9)/ 10) + 16316) % 95)- -140);
       a24 = 1;
       a15 = 6;
       return 25;
     } else if(((a24==2) && ( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((input == 4) && ((a18==11) || ((a18==9) || (a18==10)))))))){
      a3 = (((a3 * -5) - -422540) + -755759);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((input == 3) && (( a3 <= 115 && (((a18==8) && (a24==0)) && (a15==6))) || (( 417 < a3 && (((a18==11) && (a24==4)) && (a15==5))) || (((a15==5) && ((a24==4) && (a18==12))) && 417 < a3 ))))){
      a3 = (((((a3 % 300057)- 299941) + 483000) / 5) + -208875);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a24==4) && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 5)) && (a15==5))))){
      a3 = (((((a3 - -34125) * 10)/ 9) + -72306) - -296189);
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if(((a24==4) && ((a15==4) && ( 417 < a3 && ((input == 2) && ((a18==11) || (a18==12))))))){
      a3 = (((a3 - 600352) - 17) + -33);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==1) && ((((input == 2) && (((a18==8) || (a18==9)) || (a18==10))) && (a15==6)) && 417 < a3 ))){
      a3 = ((((((a3 * 9)/ 10) % 95)- -158) * 9)/ 10);
       a24 = 0;
       a18 = 12;
       return -1;
     } else if((( 417 < a3 && ((a15==5) && ((input == 2) && (((a18==10) || (a18==11)) || (a18==12))))) && (a24==0))){
      a3 = (((a3 + -599991) + -376) / 5);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 4) && (( a3 <= 115 && ((a24==4) && (a18==9))) || (( 417 < a3 && ((a24==3) && (a18==12))) || ( a3 <= 115 && ((a24==4) && (a18==8)))))) && (a15==5))){
      a3 = (((((a3 % 95)- -211) - -1) + -459913) - -459911);
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 22;
     } else if(((a15==6) && ((a24==1) && ( ((115 < a3) && (306 >= a3)) && ((input == 4) && ((a18==10) || ((a18==8) || (a18==9)))))))){
      a3 = ((((a3 + -24074) / 5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==1) && ((a15==5) && (input == 3))) && 417 < a3 ) && (a18==11))){
       a24 = 2;
       a18 = 10;
       a15 = 6;
       return 22;
     } else if((( ((115 < a3) && (306 >= a3)) && ((a15==6) && ((input == 6) && (((a18==8) || (a18==9)) || (a18==10))))) && (a24==1))){
      a3 = ((((a3 / 5) - 413364) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && (((a18==8) && (input == 5)) && (a15==5))) && (a24==0))){
      a3 = ((((a3 % 95)+ 210) / 5) - -168);
       a24 = 2;
       a18 = 11;
       return 25;
     } else if(((a15==5) && ( 417 < a3 && ((((a18==9) || (a18==10)) && (input == 6)) && (a24==1))))){
      a3 = (((a3 / 5) - 368976) + -84976);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==0) && ((input == 3) && (((a18==9) || (a18==10)) || (a18==11)))) && (a15==6)) && 417 < a3 )){
      a3 = ((((a3 % 95)+ 185) + -557016) + 556980);
       a24 = 1;
       a18 = 10;
       a15 = 5;
       return -1;
     } else if(((a18==9) && ((((a15==5) && (input == 5)) && 417 < a3 ) && (a24==2)))){
      a3 = ((((a3 / 5) - -185556) + 149195) - 583824);
       a24 = 1;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ( 417 < a3 && ((a24==0) && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 6)))))){
      a3 = ((((a3 / -5) * 10)/ 9) * 4);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && ((a15==4) && ((input == 3) && (((a18==10) || (a18==11)) || (a18==12))))) && (a24==3))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((( a3 <= 115 && ((a15==4) && ((input == 2) && ((a18==12) || ((a18==10) || (a18==11)))))) && (a24==3))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((((input == 6) && ((a18==9) || (a18==10))) && (a15==4)) && (a24==4)) && 417 < a3 )){
      a3 = (((a3 - 497960) / 5) - 129660);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==5) && (((input == 4) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a24==2)))){
      a3 = ((((a3 + -453075) * 1) - -496454) + -621321);
       a24 = 3;
       a18 = 10;
       a15 = 6;
       return 22;
     } else if((((((input == 5) && (a18==12)) && (a24==1)) && ((306 < a3) && (417 >= a3)) ) && (a15==6))){
      a3 = (((a3 + 559405) / 5) - 169813);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((( a3 <= 115 && ((input == 5) && (a18==9))) && (a24==2)) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((input == 2) && (((((a15==5) && ((a18==11) && (a24==4))) && 417 < a3 ) || (((a15==5) && ((a18==12) && (a24==4))) && 417 < a3 )) || ( a3 <= 115 && (((a18==8) && (a24==0)) && (a15==6)))))){
      a3 = ((((a3 % 299791)- -300208) * 1) + 1);
       a24 = 3;
       a18 = 10;
       a15 = 6;
       return 26;
     } else if(((a18==12) && ((a15==5) && (( ((306 < a3) && (417 >= a3)) && (input == 6)) && (a24==3))))){
      a3 = ((((((a3 * 10)/ 14) / 5) / 5) * 149)/ 10);
       a24 = 0;
       a18 = 9;
       return 21;
     } else if((((((((a24==4) && (a18==11)) && (a15==5)) && 417 < a3 ) || ( 417 < a3 && ((a15==5) && ((a18==12) && (a24==4))))) || ( a3 <= 115 && ((a15==6) && ((a24==0) && (a18==8))))) && (input == 5))){
      a3 = (((((a3 % 55)+ 361) / 5) + -210824) + 211148);
       a24 = 1;
       a18 = 12;
       a15 = 6;
       return 21;
     } else if(((a24==3) && ((a15==5) && (((input == 3) && ((a18==12) || ((a18==10) || (a18==11)))) && ((115 < a3) && (306 >= a3)) )))){
      a3 = ((((((a3 % 55)+ 307) * 10)/ 9) - 502807) - -502809);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 22;
     } else if((((a24==3) && ((a15==6) && ((input == 4) && (((a18==10) || (a18==11)) || (a18==12))))) && a3 <= 115 )){
      a3 = ((((a3 % 299791)+ 300208) - 0) - 0);
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return 22;
     } else if(((a18==12) && (((a15==5) && ((input == 1) && (a24==3))) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((a3 + -464933) + -121992) - -414088);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && ((a15==4) && ((input == 6) && ((a18==8) || (a18==9))))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 / 5) / -5) * 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==4) && (((((a18==11) || (a18==12)) && (input == 4)) && (a15==4)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 * 5) - 543917) / 5);
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a15==6) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 5))) && (a24==2)))){
      a3 = (((a3 * 5) + -120433) - 423433);
       a18 = 9;
       return -1;
     } else if(((((((a18==8) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 1)) && (a15==4)) && (a24==4))){
      a3 = (((((a3 / 5) / 5) + -353728) * -1)/ 10);
       a24 = 1;
       a18 = 8;
       a15 = 5;
       return 22;
     } else if(((a15==5) && (((input == 2) && ((((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) )) || ((a18==8) && 417 < a3 ))) && (a24==2)))){
      a3 = ((((a3 / 5) / -5) - -217576) + -598337);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((((a18==10) || (a18==11)) || (a18==12)) && (input == 6)) && (a24==3)) && (a15==6)) && a3 <= 115 )){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && (((a24==2) && ((a15==5) && (input == 6))) && (a18==9)))){
      a3 = (((a3 / -5) - -574465) / -5);
       a24 = 4;
       a18 = 8;
       a15 = 4;
       return 21;
     } else if(( a3 <= 115 && (((a24==4) && ((input == 5) && ((a18==11) || (a18==12)))) && (a15==4)))){
      a3 = ((((((a3 * 9)/ 10) % 95)+ 211) + -520198) - -520197);
       a24 = 0;
       a18 = 12;
       a15 = 5;
       return 25;
     } else if(( a3 <= 115 && ((a15==6) && (((((a18==9) || (a18==10)) || (a18==11)) && (input == 3)) && (a24==0))))){
      a3 = ((((a3 - 0) - -521706) % 95)- -210);
       a24 = 3;
       a18 = 10;
       return 25;
     } else if((( a3 <= 115 && ((a24==2) && (((a18==10) || (a18==11)) && (input == 4)))) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && ((a15==6) && ((((a18==10) || (a18==11)) && (input == 6)) && a3 <= 115 )))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ( 417 < a3 && ((((a18==9) || (a18==10)) && (input == 3)) && (a24==1))))){
      a3 = ((((a3 * 9)/ 10) - 582937) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a15==5) && (((input == 3) && ((a18==9) || (a18==10))) && (a24==4))))){
      a3 = (((a3 - 384115) + -138585) * 1);
       a18 = 11;
       a15 = 4;
       return 22;
     } else if((((input == 1) && (( a3 <= 115 && ((a24==4) && (a18==9))) || ((((a24==3) && (a18==12)) && 417 < a3 ) || ( a3 <= 115 && ((a24==4) && (a18==8)))))) && (a15==4))){
      a3 = ((((a3 - 0) % 300057)+ -299941) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && (((a15==5) && ((input == 3) && (((a18==8) || (a18==9)) || (a18==10)))) && (a24==3)))){
      a3 = (((a3 - -222713) / 5) / -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((input == 1) && (( a3 <= 115 && (a18==12)) || ( ((115 < a3) && (306 >= a3)) && (a18==8)))) && (a24==0)) && (a15==6))){
      a3 = ((((((a3 * 9)/ 10) % 55)- -362) / 5) + 260);
       a24 = 1;
       a18 = 12;
       return 22;
     } else if(( 417 < a3 && ((((a18==11) && (input == 5)) && (a15==5)) && (a24==1)))){
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(((a18==10) && ((a15==6) && ((a24==0) && ((input == 3) && ((306 < a3) && (417 >= a3)) ))))){
       return -1;
     } else if(((a24==4) && (((input == 6) && (((a18==8) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ((a18==12) && ((306 < a3) && (417 >= a3)) )))) && (a15==4)))){
      a3 = (((((a3 * 9)/ 10) / -5) - -574086) * -1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 2)) && ((115 < a3) && (306 >= a3)) ) && (a15==4)) && (a24==4))){
      a3 = (((a3 / -5) * 5) - 102575);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==6) && (((((a18==9) && ((306 < a3) && (417 >= a3)) ) || (( ((115 < a3) && (306 >= a3)) && (a18==12)) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (input == 1)) && (a24==0)))){
      a3 = ((((a3 % 55)- -326) - 12) - 5);
       a24 = 3;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if(((((input == 1) && (( 417 < a3 && (a18==8)) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ((a18==12) && ((306 < a3) && (417 >= a3)) )))) && (a24==1)) && (a15==5))){
      a3 = ((((a3 * 9)/ 10) - -45185) * -1);
       a24 = 2;
       a18 = 9;
       a15 = 6;
       return 26;
     } else if(((( ((115 < a3) && (306 >= a3)) && ((input == 4) && (((a18==10) || (a18==11)) || (a18==12)))) && (a24==3)) && (a15==5))){
      a3 = (((a3 - 249142) * 2) + -18516);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && (((input == 5) && (((a18==8) && ((306 < a3) && (417 >= a3)) ) || (((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) )))) && (a15==5)))){
      a3 = ((((a3 + -89516) - -57833) * 10)/ -9);
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if(((a15==4) && (((a24==3) && ((((a18==8) || (a18==9)) || (a18==10)) && (input == 6))) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((a3 * 5) - 108118) - 378730);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==4) && ( 417 < a3 && ((input == 1) && ((a18==9) || (a18==10))))) && (a15==4))){
      a3 = (((a3 - 600133) - -230159) + -230069);
       a24 = 2;
       a18 = 9;
       a15 = 5;
       return 21;
     } else if((((((a24==1) && (input == 1)) && ((306 < a3) && (417 >= a3)) ) && (a15==6)) && (a18==12))){
       a24 = 4;
       a15 = 4;
       return 21;
     } else if(( a3 <= 115 && (((a24==2) && ((a18==12) && (input == 5))) && (a15==5)))){
      a3 = ((((((a3 / 5) % 95)- -211) * 5) % 95)+ 123);
       a24 = 1;
       a18 = 10;
       a15 = 6;
       return 22;
     } else if(((((input == 6) && (((a18==12) && ((306 < a3) && (417 >= a3)) ) || ((a18==8) && 417 < a3 ))) && (a15==6)) && (a24==2))){
      a3 = (((a3 / 5) / 5) * -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==5) && (((((a18==10) || (a18==11)) || (a18==12)) && (input == 1)) && 417 < a3 )))){
      a3 = (((a3 / -5) - -187906) - 664383);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a18==11) && ((input == 4) && (a24==3)))) && (a15==5))){
      a3 = (((a3 - 379131) * 1) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==10) || (a18==11)) && (input == 3)) && a3 <= 115 ) && (a15==5)) && (a24==2))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((a24==3) && ((((a18==10) || (a18==11)) && (input == 5)) && (a15==6))))){
      a3 = (((((a3 * 9)/ 10) * 1) + -221488) - 328260);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && ( a3 <= 115 && ((input == 5) && (a15==5)))) && (a18==8))){
       a24 = 0;
       a15 = 4;
       return -1;
     } else if((((((a18==9) && (input == 1)) && 417 < a3 ) && (a15==5)) && (a24==2))){
      a3 = ((((((a3 % 55)+ 360) - 50) * 5) % 55)+ 313);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && (((((a18==9) || (a18==10)) && (input == 1)) && (a24==4)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 / -5) * 5) - 547274);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((((a24==1) && (input == 2)) && (a18==11)) && 417 < a3 ) && (a15==5))){
      a3 = ((((a3 / -5) + 230985) + 32867) * -2);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((input == 5) && ((((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) )) || ((a18==8) && 417 < a3 ))) && (a24==4)) && (a15==4))){
      a3 = (((((a3 % 55)+ 324) * 1) - 458794) - -458832);
       a24 = 1;
       a18 = 9;
       a15 = 5;
       return 22;
     } else if(( 417 < a3 && (((a15==5) && ((input == 5) && ((a18==10) || (a18==11)))) && (a24==2)))){
      a3 = ((((a3 - 107077) % 55)- -361) * 1);
       a24 = 1;
       a18 = 12;
       a15 = 6;
       return 26;
     } else if((((a24==4) && ( ((115 < a3) && (306 >= a3)) && (((a18==11) || (a18==12)) && (input == 2)))) && (a15==5))){
      a3 = (((a3 * -5) - 3558) + -200043);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((a24==4) && ((input == 4) && ((a18==11) || (a18==12)))) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 / -5) / 5) * 5);
       a24 = 2;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if(((a24==1) && ((a15==5) && (((input == 1) && a3 <= 115 ) && (a18==11))))){
      a3 = (((((a3 + 588233) - -8309) - 166649) % 55)+ 362);
       a24 = 0;
       a18 = 9;
       a15 = 6;
       return 21;
     } else if(((((a15==6) && ((input == 1) && (a24==0))) && 417 < a3 ) && (a18==8))){
      a3 = (((a3 + 0) - 600047) + -219);
       a15 = 4;
       return -1;
     } else if(((((((a18==8) && 417 < a3 ) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 1)) && (a15==4)) && (a24==3))){
      a3 = ((((((a3 % 55)- -309) * 1) * 5) % 55)+ 325);
       a24 = 4;
       a18 = 12;
       return 21;
     } else if((((a24==3) && ((((a18==11) || ((a18==9) || (a18==10))) && (input == 3)) && (a15==6))) && ((306 < a3) && (417 >= a3)) )){
       a18 = 9;
       return 22;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==0) && (((input == 3) && (a18==11)) && (a15==6))))){
      a3 = (((a3 - -499132) * 1) * 1);
       a24 = 3;
       a18 = 10;
       return 22;
     } else if(((a15==5) && ((a24==1) && ( a3 <= 115 && ((input == 1) && ((a18==9) || (a18==10))))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==5) && ((input == 5) && (a18==11))) && (a24==1)) && a3 <= 115 )){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 3) && ((a18==11) || ((a18==9) || (a18==10)))) && (a24==3)) && (a15==4)) && 417 < a3 )){
      a3 = (((a3 - 0) + -600222) - 134);
       a24 = 0;
       a18 = 9;
       a15 = 5;
       return 25;
     } else if(((((( 417 < a3 && ((a18==12) && (a24==3))) || (((a24==4) && (a18==8)) && a3 <= 115 )) || (((a24==4) && (a18==9)) && a3 <= 115 )) && (input == 6)) && (a15==5))){
      a3 = (((((a3 + 0) / 5) * 4) % 300057)- 299941);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (( a3 <= 115 && ((input == 3) && (a24==0))) && (a18==8)))){
       a24 = 2;
       a18 = 12;
       return 22;
     } else if((( 417 < a3 && ((a24==3) && (((a18==8) || (a18==9)) && (input == 1)))) && (a15==5))){
      a3 = ((((a3 - 600276) / 5) - -526846) * -1);
       a18 = 10;
       a15 = 4;
       return 26;
     } else if(((a24==2) && ((a15==5) && ((input == 3) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) )))))){
      a3 = ((((a3 * 10)/ 2) * 5) - -347313);
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 25;
     } else if((((a24==0) && ((((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 2))) && (a15==5))){
      a3 = ((((a3 % 95)+ 210) - -2) - 2);
       a24 = 3;
       a18 = 11;
       return 26;
     } else if((((a15==5) && (((input == 1) && (((a18==8) || (a18==9)) || (a18==10))) && ((306 < a3) && (417 >= a3)) )) && (a24==3))){
      a3 = (((a3 + -139) * 5) / 5);
       a24 = 0;
       a18 = 11;
       return 26;
     } else if((((((((a24==2) && (a18==12)) && 417 < a3 ) || ( a3 <= 115 && ((a24==3) && (a18==8)))) || ( a3 <= 115 && ((a24==3) && (a18==9)))) && (input == 3)) && (a15==5))){
      a3 = ((((a3 % 300057)- 299941) + -3) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((((a18==8) || (a18==9)) || (a18==10)) && (input == 2)) && (a24==4)) && (a15==5)) && 417 < a3 )){
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 25;
     } else if(((a24==3) && ( ((115 < a3) && (306 >= a3)) && ((a15==5) && (((a18==8) || (a18==9)) && (input == 6)))))){
      a3 = (((a3 + -131119) * 4) - 61015);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==10) || (a18==11)) && (input == 2)) && 417 < a3 ) && (a24==2)) && (a15==5))){
      a3 = ((((a3 - 421186) - -355802) + 22928) + -557586);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 2)) && a3 <= 115 ) && (a15==5)) && (a24==1))){
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if((((( 417 < a3 && ((a18==12) && (a24==1))) || ( a3 <= 115 && ((a18==8) && (a24==2)))) && (input == 2)) && (a15==5))){
      a3 = (((((a3 % 300057)+ -299941) / 5) + 105507) + -246470);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==2) && ((((a18==11) || ((a18==9) || (a18==10))) && (input == 5)) && (a15==6))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 * 5) + 587119) / -5);
       a24 = 1;
       a18 = 11;
       return -1;
     }
     return calculate_output2(input);
 }
 int calculate_output2(int input) {
     if(( ((306 < a3) && (417 >= a3)) && ((a24==2) && (((((a18==9) || (a18==10)) || (a18==11)) && (input == 1)) && (a15==6))))){
      a3 = ((((a3 - -295390) + -295576) / 5) + 170);
       a18 = 12;
       return -1;
     } else if((( 417 < a3 && ((a15==6) && ((input == 1) && (((a18==9) || (a18==10)) || (a18==11))))) && (a24==0))){
      a3 = ((((a3 % 95)+ 136) - 391386) + 391437);
       a24 = 1;
       a18 = 9;
       a15 = 5;
       return 25;
     } else if((((((input == 5) && (a18==10)) && (a15==5)) && 417 < a3 ) && (a24==3))){
      a3 = (((a3 / -5) * 4) + -76077);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && ((a24==3) && ((a15==5) && ((input == 1) && ((a18==10) || (a18==11))))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 1) && (((((a24==0) && (a18==12)) && 417 < a3 ) || (((a18==8) && (a24==1)) && a3 <= 115 )) || ( a3 <= 115 && ((a24==1) && (a18==9))))) && (a15==6))){
      a3 = ((((a3 % 300057)+ -299941) + -3) + 0);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && (( ((306 < a3) && (417 >= a3)) && (input == 4)) && (a15==6))) && (a18==12))){
       a18 = 10;
       return -1;
     } else if(((((input == 4) && ((((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) )) || ( 417 < a3 && (a18==8)))) && (a15==4)) && (a24==4))){
      a3 = (((a3 / 5) - 185457) + -359914);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==4) && ((input == 4) && (( a3 <= 115 && ((a24==4) && (a18==9))) || ((((a24==3) && (a18==12)) && 417 < a3 ) || (((a24==4) && (a18==8)) && a3 <= 115 )))))){
      a3 = ((((a3 + 0) % 300057)- 299941) - 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==3) && ((a15==4) && ((input == 4) && (( 417 < a3 && (a18==8)) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ( ((306 < a3) && (417 >= a3)) && (a18==12)))))))){
      a3 = (((((a3 / 5) % 55)+ 335) - -21338) + -21349);
       a24 = 4;
       a18 = 10;
       return 25;
     } else if(((a15==6) && ((((a18==8) && (input == 4)) && 417 < a3 ) && (a24==0)))){
      a3 = ((((((a3 % 55)- -334) * 5) + -342050) % 55)+ 388);
       a24 = 3;
       a18 = 10;
       a15 = 4;
       return 22;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a15==4) && ((a24==4) && (((a18==9) || (a18==10)) && (input == 5)))))){
      a3 = (((a3 + -351209) * 1) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((( ((115 < a3) && (306 >= a3)) && ((input == 1) && (((a18==8) || (a18==9)) || (a18==10)))) && (a15==6)) && (a24==3))){
      a3 = (((a3 * 5) + 401484) + 195663);
       a24 = 2;
       a18 = 9;
       return -1;
     } else if((((input == 4) && ((( 417 < a3 && ((a24==0) && (a18==12))) || (((a24==1) && (a18==8)) && a3 <= 115 )) || (((a24==1) && (a18==9)) && a3 <= 115 ))) && (a15==6))){
      a3 = ((((a3 % 95)- -210) + 0) - -1);
       a24 = 3;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if(((((((a18==12) || ((a18==10) || (a18==11))) && (input == 5)) && a3 <= 115 ) && (a15==4)) && (a24==3))){
      a3 = ((((((a3 * 9)/ 10) % 95)+ 210) - -563481) - 563479);
       a18 = 10;
       return 21;
     } else if((((input == 6) && (( a3 <= 115 && ((a24==2) && (a18==8))) || ((((a24==1) && (a18==11)) && 417 < a3 ) || ( 417 < a3 && ((a24==1) && (a18==12)))))) && (a15==6))){
      a3 = ((((a3 - 0) / 5) + 70566) - 277039);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((input == 3) && ((( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12))) || ( 417 < a3 && (a18==8)))) && (a24==1)))){
      a3 = ((((a3 + -600031) * 1) + 229814) - 229714);
       a24 = 2;
       a18 = 10;
       a15 = 6;
       return 21;
     } else if(((((( 417 < a3 && (a18==8)) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 3)) && (a15==4)) && (a24==4))){
      a3 = (((a3 + -600088) - 109) / 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a24==2) && ( 417 < a3 && (input == 4))) && (a18==9)) && (a15==5))){
       a18 = 11;
       a15 = 4;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && ((a18==8) && ((a15==5) && (input == 4)))) && (a24==2))){
      a3 = (((((a3 % 55)- -335) + 5) - 106400) + 106419);
       a24 = 1;
       a15 = 6;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==4) && (((input == 6) && (a18==8)) && (a15==4))))){
      a3 = (((a3 / 5) - -34270) * -5);
       a24 = 0;
       return -1;
     } else if(( a3 <= 115 && (((a24==3) && (((a18==12) || ((a18==10) || (a18==11))) && (input == 4))) && (a15==4)))){
      a3 = (((((a3 % 95)- -210) + 1) - 295391) - -295391);
       a18 = 9;
       return 21;
     } else if(((((((a18==8) || (a18==9)) && (input == 6)) && (a15==5)) && 417 < a3 ) && (a24==0))){
      a3 = ((((a3 - 0) + -182899) + 73617) - 490836);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a24==0) && ((((a18==8) || (a18==9)) || (a18==10)) && (input == 3)))) && (a15==5))){
      a3 = ((((a3 * 5) - 436532) - -702373) * -2);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && (((input == 5) && (a18==12)) && ((306 < a3) && (417 >= a3)) )) && (a15==5))){
      a3 = (((a3 * 5) / -5) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((a24==2) && ((input == 4) && (( ((306 < a3) && (417 >= a3)) && (a18==8)) || (((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) ))))))){
      a3 = (((((a3 + -31604) % 95)+ 226) / 5) + 121);
       a18 = 11;
       return -1;
     } else if(((a15==5) && ((input == 4) && ((((a18==9) && (a24==3)) && a3 <= 115 ) || ((((a18==12) && (a24==2)) && 417 < a3 ) || (((a24==3) && (a18==8)) && a3 <= 115 )))))){
      a3 = ((((((a3 % 95)- -211) * 5) * 5) % 95)- -211);
       a24 = 3;
       a18 = 11;
       a15 = 4;
       return 26;
     } else if(( ((306 < a3) && (417 >= a3)) && (((((a18==9) || (a18==10)) && (input == 1)) && (a15==5)) && (a24==2)))){
      a3 = ((((a3 / -5) - 126690) + 323186) * -3);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==1) && ((a15==5) && (((( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12))) || ((a18==8) && 417 < a3 )) && (input == 4))))){
      a3 = ((((a3 - 599963) + 321584) - 213242) + -108421);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 22;
     } else if(((a15==6) && ( ((306 < a3) && (417 >= a3)) && ((a24==1) && (((a18==8) || (a18==9)) && (input == 2)))))){
       a24 = 0;
       a18 = 10;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && (((a24==4) && ((input == 4) && ((a18==11) || (a18==12)))) && (a15==5)))){
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 21;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==3) && ((((a18==8) || (a18==9)) && (input == 5)) && (a15==4))))){
      a3 = ((((a3 % 55)+ 359) / 5) - -330);
       a18 = 10;
       return 22;
     } else if(((a15==6) && ( ((306 < a3) && (417 >= a3)) && ((((a18==11) || (a18==12)) && (input == 4)) && (a24==0))))){
      a3 = ((((a3 - 442409) + -75157) + 886999) * -1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==4) && (((((a18==8) || (a18==9)) || (a18==10)) && (input == 2)) && (a24==3))) && ((306 < a3) && (417 >= a3)) )){
      a3 = ((((((a3 * 4)/ 10) * 1) * 5) % 95)+ 143);
       a24 = 4;
       a18 = 8;
       return 26;
     } else if((( 417 < a3 && (((a18==10) && (input == 6)) && (a24==3))) && (a15==5))){
      a3 = (((((a3 * 9)/ 10) + -135101) - -50940) - 461817);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((a15==4) && (input == 4)) && a3 <= 115 ) && (a24==3)) && (a18==9))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==4) && (( 417 < a3 && ((input == 1) && ((a18==11) || (a18==12)))) && (a24==4)))){
      a3 = ((((a3 / -5) * 10)/ 9) + -311570);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==2) && ((a15==5) && ((input == 6) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ( ((115 < a3) && (306 >= a3)) && (a18==12))) || ( ((306 < a3) && (417 >= a3)) && (a18==8))))))){
      a3 = (((((a3 + -167734) * 10)/ 9) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==10) && ((a15==4) && (((input == 6) && a3 <= 115 ) && (a24==4))))){
      a3 = (((((a3 % 95)- -211) * 1) - 216688) - -216688);
       a24 = 0;
       a15 = 5;
       return 25;
     } else if((((a15==5) && ((a24==0) && ( a3 <= 115 && (input == 4)))) && (a18==9))){
      a3 = ((((a3 % 55)+ 362) * 1) * 1);
       a24 = 2;
       return 25;
     } else if(((a15==5) && ( a3 <= 115 && (((input == 4) && (a24==2)) && (a18==9))))){
      a3 = (((((a3 % 95)+ 210) + 0) + 65155) + -65154);
       a24 = 3;
       a18 = 12;
       a15 = 6;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a24==3) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 5))) && (a15==5)))){
      a3 = ((((a3 % 55)+ 336) * 1) + -21);
       a24 = 2;
       a18 = 12;
       a15 = 6;
       return 25;
     } else if(((a24==2) && (((input == 1) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a15==5)))){
      a3 = ((((a3 * 5) + 312497) - -270968) + -1067025);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((a24==4) && (((a18==11) || (a18==12)) && (input == 1)))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 / 5) * -5) + -536237);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==4) && ( ((306 < a3) && (417 >= a3)) && ((input == 6) && (((a18==8) || (a18==9)) || (a18==10))))))){
      a3 = (((a3 * 5) * -5) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a15==5) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 5)))) && (a24==3))){
      a3 = ((((a3 / -5) + 56113) * 5) * -2);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==0) && ( a3 <= 115 && (((a18==11) || ((a18==9) || (a18==10))) && (input == 4)))) && (a15==6))){
       a24 = 2;
       a18 = 12;
       return 22;
     } else if((((a15==6) && ((((a18==12) && a3 <= 115 ) || ( ((115 < a3) && (306 >= a3)) && (a18==8))) && (input == 2))) && (a24==0))){
      a3 = (((((a3 % 300057)+ -299941) * 1) - -466629) - 466629);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ( a3 <= 115 && ((a24==1) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 1)))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==11) && ( 417 < a3 && (((input == 1) && (a24==3)) && (a15==5))))){
      a3 = (((a3 + -229901) / 5) + -297359);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((((a18==11) && (input == 5)) && (a24==3)) && (a15==5)))){
      a3 = ((((a3 % 55)+ 324) + 20) + 13);
       a24 = 1;
       a18 = 10;
       a15 = 6;
       return 21;
     } else if((( a3 <= 115 && ((a15==4) && ((input == 4) && ((a18==11) || (a18==12))))) && (a24==4))){
      a3 = (((((a3 % 55)- -362) / 5) - -237700) - 237388);
       a24 = 0;
       a18 = 11;
       a15 = 5;
       return 25;
     } else if(((((a18==8) && ((a15==5) && (input == 2))) && a3 <= 115 ) && (a24==0))){
      a3 = ((((((a3 + 0) * 9)/ 10) + 482915) % 95)- -211);
       a24 = 2;
       return 26;
     } else if(( a3 <= 115 && ((a15==4) && ((a24==4) && ((input == 1) && ((a18==11) || (a18==12))))))){
      a3 = ((((a3 % 55)- -361) + 0) + 0);
       a24 = 0;
       a18 = 10;
       a15 = 5;
       return 21;
     } else if(((a15==6) && ((((input == 5) && ((a18==10) || ((a18==8) || (a18==9)))) && ((115 < a3) && (306 >= a3)) ) && (a24==1)))){
      a3 = (((a3 / 5) + -529169) - 30787);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 1) && (((a18==9) || (a18==10)) || (a18==11))) && 417 < a3 ) && (a15==6)) && (a24==2))){
      a3 = ((((a3 % 55)+ 319) / 5) - -294);
       a18 = 8;
       return -1;
     } else if((((a24==2) && ( ((115 < a3) && (306 >= a3)) && ((input == 2) && ((a18==10) || ((a18==8) || (a18==9)))))) && (a15==6))){
       a24 = 1;
       a18 = 8;
       return -1;
     } else if(( a3 <= 115 && ((a24==2) && ((a15==5) && ((input == 1) && ((a18==10) || (a18==11))))))){
      a3 = ((((a3 * 9)/ 10) / 5) - -540399);
       a24 = 3;
       a18 = 9;
       a15 = 6;
       return 21;
     } else if((((a24==4) && (((( a3 <= 115 && (a18==11)) || ( a3 <= 115 && (a18==12))) || ( ((115 < a3) && (306 >= a3)) && (a18==8))) && (input == 4))) && (a15==5))){
      a3 = ((((a3 * 9)/ 10) - 10839) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((a24==1) && (((a18==11) || (a18==12)) && (input == 5)))) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 % 55)- -343) + -318920) + 318925);
       a24 = 0;
       a18 = 12;
       return -1;
     } else if((((a15==5) && (((input == 6) && ((a18==11) || (a18==12))) && ((306 < a3) && (417 >= a3)) )) && (a24==0))){
      a3 = (((a3 - 444267) + -104446) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((( a3 <= 115 && ((a18==9) && (a24==3))) || ((((a24==2) && (a18==12)) && 417 < a3 ) || ( a3 <= 115 && ((a24==3) && (a18==8))))) && (input == 4)))){
      a3 = ((((a3 % 300057)+ -299941) - 2) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 1) && a3 <= 115 ) && (a15==6)) && (a24==2)) && (a18==9))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 6)) && (a15==6)) && (a24==0))){
      a3 = ((((a3 % 300057)+ -299941) * 1) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==5) && ((a24==1) && ((input == 4) && ((a18==9) || (a18==10))))))){
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(((((a15==4) && (((a18==11) || ((a18==9) || (a18==10))) && (input == 6))) && 417 < a3 ) && (a24==3))){
      a3 = (((a3 - 413229) - -96489) - 283466);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && (((input == 5) && ((a18==9) || (a18==10))) && (a15==5))) && (a24==1))){
      a3 = (((a3 - -500185) - -90325) * 1);
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 26;
     } else if(((a15==4) && ((((( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12))) || ( 417 < a3 && (a18==8))) && (input == 5)) && (a24==3)))){
      a3 = (((a3 / 5) + 169567) * 2);
       a24 = 4;
       a18 = 9;
       return 21;
     } else if(((a15==6) && (((((a18==9) && ((306 < a3) && (417 >= a3)) ) || (((a18==12) && ((115 < a3) && (306 >= a3)) ) || ( ((306 < a3) && (417 >= a3)) && (a18==8)))) && (input == 3)) && (a24==0)))){
      a3 = (((((a3 * 5) - 389703) + -60924) % 95)+ 250);
       a24 = 4;
       a18 = 12;
       a15 = 4;
       return 22;
     } else if(( a3 <= 115 && ((a18==10) && (((input == 4) && (a15==4)) && (a24==4))))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((( a3 <= 115 && (((input == 5) && ((a18==10) || (a18==11))) && (a15==5))) && (a24==3))){
       a24 = 2;
       a18 = 9;
       a15 = 6;
       return 21;
     } else if((((a24==2) && ((a15==6) && ((input == 4) && ((a18==10) || ((a18==8) || (a18==9)))))) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 + -41262) * 10)/ 9) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==4) && ( 417 < a3 && (((input == 3) && ((a18==11) || (a18==12))) && (a15==4))))){
      a3 = (((a3 + -600335) / 5) - 125944);
       a24 = 2;
       a18 = 10;
       a15 = 5;
       return 22;
     } else if(((a15==6) && (((( ((306 < a3) && (417 >= a3)) && (a18==12)) || ((a18==8) && 417 < a3 )) && (input == 3)) && (a24==2)))){
      a3 = ((((a3 + -424004) / 5) / 5) + 383913);
       a24 = 3;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((input == 6) && (( ((306 < a3) && (417 >= a3)) && (a18==9)) || (( ((115 < a3) && (306 >= a3)) && (a18==12)) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))))) && (a24==0))){
      a3 = (((a3 / -5) / 5) * 5);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((input == 1) && (((((a18==12) && (a24==3)) && 417 < a3 ) || (((a24==4) && (a18==8)) && a3 <= 115 )) || ( a3 <= 115 && ((a24==4) && (a18==9))))))){
      a3 = ((((a3 % 300057)- 299941) * 1) - 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==12) && ( a3 <= 115 && (((a24==3) && (input == 6)) && (a15==5))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && ((a24==3) && ((a15==5) && (input == 4)))) && (a18==11))){
      a3 = (((a3 / 5) / -5) - 412531);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==4) && ((a24==3) && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 1)))) && 417 < a3 )){
      a3 = ((((a3 + -600145) - 33) - -315605) + -315686);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==4) && (((a24==3) && ((input == 5) && ((a18==11) || ((a18==9) || (a18==10))))) && 417 < a3 ))){
      a3 = ((((a3 - 0) - 600010) + 324047) - 324015);
       a24 = 0;
       a18 = 8;
       a15 = 5;
       return 22;
     } else if((((a15==5) && ((a24==2) && (((a18==10) || (a18==11)) && (input == 3)))) && 417 < a3 )){
      a3 = (((a3 - 600297) - -482535) - 482385);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==5) && ((input == 3) && (( a3 <= 115 && (a18==12)) || ((a18==8) && ((115 < a3) && (306 >= a3)) )))))){
      a3 = (((((a3 % 300057)- 299941) + 247619) * 1) + -247621);
       a24 = 3;
       a18 = 11;
       return 22;
     } else if(((a15==6) && ( ((306 < a3) && (417 >= a3)) && ((a24==0) && ((input == 2) && (a18==10)))))){
      a3 = ((((a3 + -33842) - 560480) / 5) + 119012);
       a24 = 4;
       a18 = 11;
       a15 = 4;
       return 21;
     } else if((( a3 <= 115 && ((a15==6) && ((input == 3) && ((a18==12) || ((a18==10) || (a18==11)))))) && (a24==3))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && ( ((115 < a3) && (306 >= a3)) && ((input == 3) && ((a18==9) || (a18==10))))) && (a15==5))){
      a3 = (((a3 * 5) * 5) / -5);
       a18 = 11;
       a15 = 6;
       return 22;
     } else if((((((input == 5) && ((a18==11) || (a18==12))) && (a24==0)) && ((306 < a3) && (417 >= a3)) ) && (a15==5))){
      a3 = (((a3 * -5) - 208207) * 2);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==5) && ((a24==1) && (input == 6))) && a3 <= 115 ) && (a18==8))){
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((((input == 1) && ((a18==9) || (a18==10))) && (a24==1)) && (a15==5)))){
      a3 = (((a3 - 600092) * 1) / 5);
       a24 = 2;
       a18 = 12;
       a15 = 6;
       return 22;
     } else if(((a15==6) && ( 417 < a3 && ((((a18==10) || (a18==11)) && (input == 1)) && (a24==3))))){
      a3 = (((a3 / 5) - 303308) - 179168);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==5) && (((input == 2) && ((a18==10) || ((a18==8) || (a18==9)))) && ((306 < a3) && (417 >= a3)) )))){
      a3 = (((a3 / 5) + 390983) + -783525);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((( a3 <= 115 && (input == 6)) && (a18==10)) && (a15==5)) && (a24==4))){
      a3 = (((((a3 % 95)+ 211) * 5) % 95)+ 205);
       a24 = 3;
       a18 = 8;
       a15 = 4;
       return 22;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==3) && ((a15==4) && ((input == 1) && ((a18==11) || (a18==12))))))){
      a3 = (((a3 * 5) + 347415) / -5);
       a24 = 4;
       a18 = 8;
       return 26;
     } else if(((a24==1) && ((a15==6) && ((a18==11) && ( ((306 < a3) && (417 >= a3)) && (input == 1)))))){
      a3 = ((((a3 * 5) / -5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==1) && (((input == 1) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ( ((115 < a3) && (306 >= a3)) && (a18==12))) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a15==5)))){
      a3 = (((((a3 % 95)+ 169) + -15) - -40745) - 40763);
       a18 = 11;
       a15 = 6;
       return 22;
     } else if(((( a3 <= 115 && (((a18==10) || (a18==11)) && (input == 2))) && (a15==5)) && (a24==0))){
      a3 = ((((a3 / 5) + 399627) * 10)/ 9);
       a24 = 2;
       a18 = 9;
       return 26;
     } else if(((a15==5) && (( 417 < a3 && ((input == 3) && (a18==9))) && (a24==2)))){
      a3 = ((((a3 + 0) / 5) % 95)+ 164);
       a24 = 3;
       a15 = 4;
       return 21;
     } else if(((a15==5) && (((input == 2) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a24==1)))){
      a3 = (((a3 - 524684) + -18707) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && (((input == 2) && (a24==1)) && (a18==8))) && a3 <= 115 )){
      a3 = (((((a3 * 9)/ 10) % 55)+ 361) + 0);
       a24 = 4;
       a18 = 11;
       return 21;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a24==3) && ((input == 3) && (((a18==8) || (a18==9)) || (a18==10)))) && (a15==6)))){
      a3 = (((a3 * 5) * 5) * 5);
       a24 = 1;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if((((a24==2) && (((input == 4) && (a18==12)) && a3 <= 115 )) && (a15==5))){
      a3 = ((((a3 + 366490) % 95)+ 210) + 0);
       a18 = 9;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==2) && ((input == 6) && (( 417 < a3 && (a18==8)) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))))))){
      a3 = (((a3 / 5) / -5) + -10954);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==4) && ((input == 3) && ((a18==11) || (a18==12)))) && (a15==4)) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 / 5) - 507268) / 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a18==11) && (((input == 3) && (a15==5)) && (a24==3))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 - 577812) - 20233) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==3) && (((a18==8) || (a18==9)) && (input == 2))) && ((115 < a3) && (306 >= a3)) ) && (a15==5))){
      a3 = (((a3 - -173677) * -3) - 39591);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((a15==6) && (((a24==0) && (input == 3)) && (a18==8))))){
      a3 = (((((a3 % 95)- -146) / 5) * 49)/ 10);
       a24 = 4;
       a18 = 11;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a15==6) && (((input == 3) && ((a18==9) || (a18==10))) && (a24==0))))){
      a3 = (((a3 * 5) * -5) * 5);
       a24 = 2;
       a18 = 10;
       return 25;
     } else if(( a3 <= 115 && ((a15==6) && (((((a18==10) || (a18==11)) || (a18==12)) && (input == 3)) && (a24==1))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((((a18==10) || ((a18==8) || (a18==9))) && (input == 1)) && ((306 < a3) && (417 >= a3)) ) && (a24==4)))){
      a3 = ((((a3 / 5) * 69)/ 10) + 383903);
       a24 = 3;
       a18 = 11;
       a15 = 6;
       return 26;
     } else if(((a15==5) && (((((a18==8) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 4)) && (a24==2)))){
      a3 = (((a3 + 0) + -599992) * 1);
       a24 = 0;
       a18 = 11;
       return 22;
     } else if(((a18==10) && (( a3 <= 115 && ((input == 5) && (a15==4))) && (a24==4)))){
      a3 = ((((((a3 + 0) % 95)- -211) * 5) % 95)- -182);
       a24 = 0;
       a18 = 8;
       a15 = 5;
       return 25;
     } else if(((((a24==0) && ((a15==6) && (input == 5))) && 417 < a3 ) && (a18==8))){
      a3 = (((((a3 % 55)- -348) - 7) + -316112) + 316103);
       a18 = 12;
       return -1;
     } else if(( a3 <= 115 && ((a24==4) && ((a18==10) && ((a15==5) && (input == 3)))))){
      a3 = ((((a3 % 299791)- -300208) * 1) - -1);
       a24 = 1;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if((((input == 4) && (( a3 <= 115 && ((a24==2) && (a18==8))) || ((((a18==11) && (a24==1)) && 417 < a3 ) || ( 417 < a3 && ((a18==12) && (a24==1)))))) && (a15==6))){
      a3 = (((a3 / 5) / 5) + -42467);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((( 417 < a3 && ((a15==5) && ((a24==4) && (a18==11)))) || ( 417 < a3 && (((a18==12) && (a24==4)) && (a15==5)))) || ( a3 <= 115 && (((a24==0) && (a18==8)) && (a15==6)))) && (input == 4))){
      a3 = ((((a3 % 95)- -211) - -1) * 1);
       a24 = 1;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if((((a24==0) && ((((a18==10) || (a18==11)) && (input == 5)) && (a15==5))) && a3 <= 115 )){
      a3 = ((((a3 / 5) - -318888) * 10)/ 9);
       a24 = 2;
       a18 = 10;
       return 26;
     } else if(( a3 <= 115 && ((a18==10) && ((a24==4) && ((input == 3) && (a15==4)))))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==3) && ((( ((306 < a3) && (417 >= a3)) && (input == 3)) && (a15==5)) && (a18==12)))){
      a3 = (((((a3 * 5) % 95)- -126) + -434219) + 434223);
       a15 = 4;
       return 21;
     } else if(((a15==6) && ( a3 <= 115 && ((a24==0) && ((input == 2) && ((a18==11) || ((a18==9) || (a18==10)))))))){
      a3 = ((((a3 - -556124) * 1) % 55)- -361);
       a24 = 3;
       a18 = 8;
       return 22;
     } else if(((a15==4) && (((a24==3) && ((input == 5) && (a18==9))) && a3 <= 115 ))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a18==11) && (( ((306 < a3) && (417 >= a3)) && ((input == 6) && (a24==3))) && (a15==5)))){
      a3 = (((a3 / 5) - 281685) - 220788);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && ((a24==2) && ((input == 5) && (a15==6)))) && (a18==9))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==3) && ((input == 2) && ((a18==10) || (a18==11)))) && (a15==5)) && a3 <= 115 )){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==4) && ((input == 6) && ((a18==11) || (a18==12)))) && a3 <= 115 ) && (a15==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a24==0) && ((input == 6) && (a15==6))) && (a18==11)) && ((115 < a3) && (306 >= a3)) )){
       a24 = 1;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && ((a15==5) && ((((a18==10) || (a18==11)) && (input == 2)) && (a24==2))))){
      a3 = ((((a3 + 0) % 299791)- -300208) - -1);
       a24 = 3;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if((((a15==6) && ((a24==3) && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 4)))) && ((306 < a3) && (417 >= a3)) )){
       a18 = 12;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && (((((a18==10) || (a18==11)) && (input == 4)) && (a24==2)) && (a15==5)))){
       a24 = 3;
       a18 = 9;
       a15 = 6;
       return 26;
     } else if(((((a24==3) && ((input == 1) && ((a18==11) || (a18==12)))) && (a15==6)) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 * -5) - 179535) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && ((((a18==11) || (a18==12)) && (input == 6)) && ((115 < a3) && (306 >= a3)) )) && (a15==6))){
      a3 = (((a3 * 5) / 5) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==2) && ((((a18==12) && (input == 4)) && (a15==6)) && a3 <= 115 ))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==8) && ((a24==2) && ((a15==5) && ((input == 5) && ((115 < a3) && (306 >= a3)) ))))){
      a3 = (((a3 * 5) * 5) * 5);
       a24 = 1;
       a15 = 6;
       return 21;
     } else if(((((a15==6) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 1))) && (a24==3)) && a3 <= 115 )){
      a3 = ((((a3 % 299791)- -300208) - 0) + 1);
       a24 = 1;
       a18 = 12;
       a15 = 5;
       return -1;
     } else if(((a15==5) && ((((input == 2) && (a24==0)) && (a18==9)) && a3 <= 115 ))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && (((input == 3) && ((a18==8) || (a18==9))) && (a24==3))) && (a15==4))){
       a18 = 12;
       return 26;
     } else if(((a24==4) && (((((a18==11) || (a18==12)) && (input == 5)) && 417 < a3 ) && (a15==4)))){
      a3 = ((((a3 * 9)/ 10) - 540271) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==4) && ( ((115 < a3) && (306 >= a3)) && ((((a18==9) || (a18==10)) && (input == 4)) && (a15==5))))){
      a3 = (((((a3 / 5) - -296) * 5) % 55)- -338);
       a24 = 0;
       a18 = 11;
       return 21;
     } else if((((a15==6) && ((a18==10) && ((input == 2) && ((306 < a3) && (417 >= a3)) ))) && (a24==1))){
       a24 = 0;
       a18 = 12;
       return -1;
     } else if((((((input == 1) && ((a18==10) || (a18==11))) && a3 <= 115 ) && (a15==6)) && (a24==2))){
      a3 = ((((a3 % 299791)+ 300208) + 1) + 0);
       a24 = 0;
       a18 = 11;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((input == 5) && (a24==3)))) && (a18==8))){
      a3 = ((((a3 / 5) + 335232) - -192484) + -697164);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((((a18==10) || (a18==11)) && (input == 6)) && a3 <= 115 ) && (a24==0)))){
      a3 = (((((a3 % 55)- -361) + 2) / 5) + 262);
       a24 = 2;
       a18 = 12;
       return 26;
     } else if(((a15==6) && (((a24==3) && (((a18==11) || (a18==12)) && (input == 4))) && ((115 < a3) && (306 >= a3)) ))){
      a3 = ((((a3 / 5) + 235204) * 10)/ 9);
       a24 = 0;
       a18 = 9;
       return -1;
     } else if((((((a24==3) && (input == 1)) && (a18==9)) && a3 <= 115 ) && (a15==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==1) && ((input == 3) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ( ((306 < a3) && (417 >= a3)) && (a18==8))))) && (a15==5))){
      a3 = (((a3 * -5) + -458640) + -74105);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==4) && ((input == 4) && (a18==8))) && ((115 < a3) && (306 >= a3)) ) && (a15==4))){
      a3 = (((a3 * 5) - 152212) + -319037);
       a24 = 0;
       return -1;
     } else if(((a15==6) && ((a24==0) && (((((a18==9) || (a18==10)) || (a18==11)) && (input == 6)) && a3 <= 115 )))){
      a3 = (((((a3 - -256975) - -72978) + 59929) % 299791)+ 300208);
       a24 = 2;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if(((a18==11) && ( ((115 < a3) && (306 >= a3)) && (((input == 4) && (a24==0)) && (a15==6))))){
      a3 = (((a3 / 5) + -494978) + 495292);
       a24 = 2;
       a18 = 10;
       return 25;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((a18==11) && ((input == 4) && (a24==1)))))){
      a3 = ((((a3 - 417466) * 10)/ 9) - 65788);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((a24==0) && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 2)))) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 + -413155) * 10)/ 9) - 35418);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==4) && (((input == 6) && ((a18==10) || ((a18==8) || (a18==9)))) && (a24==4))))){
      a3 = (((a3 / 5) * -5) - 173631);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==1) && (((input == 6) && ((a18==10) || ((a18==8) || (a18==9)))) && 417 < a3 )) && (a15==6))){
      a3 = ((((((a3 % 55)+ 330) * 1) * 5) % 55)+ 326);
       a24 = 2;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 5)) && (a24==2)) && (a15==5)) && ((115 < a3) && (306 >= a3)) )){
      a3 = ((((a3 / 5) / 5) / 5) + 580327);
       a18 = 8;
       a15 = 6;
       return 22;
     } else if((((a15==5) && ((input == 6) && ((((a18==11) && a3 <= 115 ) || ((a18==12) && a3 <= 115 )) || ( ((115 < a3) && (306 >= a3)) && (a18==8))))) && (a24==4))){
      a3 = ((((a3 % 300057)- 299941) / 5) + -398005);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((a24==2) && ((((a18==10) || (a18==11)) && (input == 3)) && a3 <= 115 )))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((input == 4) && (( a3 <= 115 && (a18==12)) || ( ((115 < a3) && (306 >= a3)) && (a18==8)))) && (a15==5)) && (a24==1))){
      a3 = ((((a3 * 9)/ 10) - 50450) - 3494);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && (((a18==9) && ((input == 5) && (a15==5))) && (a24==0)))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==8) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12)))) && (input == 6)) && (a24==3)) && (a15==4))){
      a3 = (((a3 - 0) + -600115) - 69);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a18==12) && ( a3 <= 115 && ((input == 6) && (a15==6)))) && (a24==2))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && (((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ( ((115 < a3) && (306 >= a3)) && (a18==12))) || ( ((306 < a3) && (417 >= a3)) && (a18==8))) && (input == 3))) && (a24==2))){
      a3 = (((a3 / 5) + 328) - -2);
       a24 = 1;
       a18 = 8;
       return -1;
     } else if(((a15==6) && (((((a18==9) && 417 < a3 ) || (( ((306 < a3) && (417 >= a3)) && (a18==12)) || ( 417 < a3 && (a18==8)))) && (input == 5)) && (a24==3)))){
      a3 = (((((a3 % 95)+ 154) * 9)/ 10) + -3);
       a18 = 10;
       a15 = 4;
       return -1;
     } else if((((((((a18==8) || (a18==9)) || (a18==10)) && (input == 2)) && (a15==5)) && (a24==3)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((((a3 - 161) - -42) / 5) * 32)/ 10);
       a18 = 11;
       a15 = 4;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a15==5) && ((a18==8) && ((input == 2) && (a24==2)))))){
      a3 = (((a3 - -26663) / 5) - -390761);
       a24 = 0;
       a15 = 6;
       return 22;
     } else if(((((a15==6) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 5))) && a3 <= 115 ) && (a24==1))){
      a3 = ((((a3 % 55)+ 361) - 0) * 1);
       a24 = 4;
       a18 = 9;
       a15 = 4;
       return 25;
     } else if(((((((a18==10) || ((a18==8) || (a18==9))) && (input == 6)) && 417 < a3 ) && (a24==4)) && (a15==5))){
      a3 = (((a3 + -600048) - 20) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((a15==5) && ((((a18==8) || (a18==9)) && (input == 2)) && (a24==3))))){
      a3 = ((((((a3 * 9)/ 10) % 95)+ 198) - -450812) - 450873);
       a24 = 0;
       a18 = 9;
       return 26;
     } else if(((((input == 5) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ( ((115 < a3) && (306 >= a3)) && (a18==12))) || ( ((306 < a3) && (417 >= a3)) && (a18==8)))) && (a15==6)) && (a24==2))){
      a3 = (((((a3 * 5) % 55)- -315) - -396523) + -396526);
       a24 = 0;
       a18 = 9;
       return -1;
     } else if((( a3 <= 115 && ((a24==1) && ((input == 4) && ((a18==9) || (a18==10))))) && (a15==5))){
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if((((a15==6) && (((input == 5) && ((a18==10) || (a18==11))) && a3 <= 115 )) && (a24==2))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ( ((306 < a3) && (417 >= a3)) && ((a24==0) && (((a18==11) || (a18==12)) && (input == 2)))))){
      a3 = (((a3 + -496276) - 86553) - -262868);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && (((a18==8) && (input == 4)) && (a15==5))) && (a24==1))){
       a24 = 0;
       a15 = 4;
       return -1;
     } else if((((a24==3) && (((input == 3) && ((a18==10) || (a18==11))) && (a15==6))) && 417 < a3 )){
       a24 = 4;
       a18 = 11;
       a15 = 4;
       return 26;
     } else if(((a18==9) && ( a3 <= 115 && (((input == 6) && (a24==2)) && (a15==5))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ( 417 < a3 && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 4)) && (a24==4))))){
       a24 = 2;
       a18 = 9;
       a15 = 6;
       return 26;
     } else if(((a24==2) && (( a3 <= 115 && ((input == 5) && ((a18==10) || (a18==11)))) && (a15==5)))){
      a3 = (((((a3 % 55)- -362) - 1) + -285407) + 285408);
       a24 = 3;
       a18 = 9;
       a15 = 6;
       return 22;
     } else if(((a24==0) && (((((a18==11) || ((a18==9) || (a18==10))) && (input == 4)) && 417 < a3 ) && (a15==6)))){
      a3 = (((((a3 - 0) + -550575) / 5) % 55)- -362);
       a24 = 4;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 2) && ((115 < a3) && (306 >= a3)) ) && (a15==5)) && (a24==0)) && (a18==12))){
      a3 = (((a3 + 471605) * -1) - 35997);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==6) && ((input == 4) && (((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )))))){
      a3 = ((((a3 + 51670) % 299791)+ 300208) - 0);
       a24 = 1;
       a18 = 11;
       return 22;
     } else if((((((input == 6) && (a15==5)) && a3 <= 115 ) && (a24==0)) && (a18==9))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && ((input == 6) && (( a3 <= 115 && (a18==12)) || ((a18==8) && ((115 < a3) && (306 >= a3)) )))) && (a15==5))){
      a3 = (((((a3 - -342184) * 1) - -67276) % 300057)+ -299941);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a24==4) && ((input == 2) && ((a18==11) || (a18==12))))) && (a15==5))){
       a24 = 3;
       a18 = 8;
       a15 = 6;
       return 25;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a24==0) && (((input == 1) && ((a18==11) || (a18==12))) && (a15==5))))){
      a3 = ((((a3 + 82715) * -5) * 10)/ 9);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && (((((a18==10) || ((a18==8) || (a18==9))) && (input == 4)) && (a24==3)) && ((306 < a3) && (417 >= a3)) ))){
      a3 = ((((a3 - 281062) - -189973) / 5) + 18380);
       a24 = 4;
       a18 = 10;
       return 25;
     } else if(( 417 < a3 && ((a15==4) && ((((a18==9) || (a18==10)) && (input == 3)) && (a24==4))))){
       a24 = 1;
       a18 = 11;
       a15 = 5;
       return 26;
     } else if(((a15==5) && ((((input == 1) && (a24==4)) && (a18==10)) && a3 <= 115 ))){
      a3 = (((((a3 * 9)/ 10) / 5) % 55)- -361);
       a24 = 1;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ( ((115 < a3) && (306 >= a3)) && ((a18==12) && ((a24==0) && (input == 5)))))){
      a3 = ((((a3 - 527731) * -1)/ 10) + 75216);
       a24 = 3;
       a18 = 11;
       return 25;
     } else if(( 417 < a3 && (((a24==3) && (((a18==10) || (a18==11)) && (input == 6))) && (a15==6)))){
      a3 = ((((a3 - 0) + -235764) - -210834) + -575453);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((((input == 2) && ((a18==11) || (a18==12))) && (a24==3)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 + -181485) - -640692) + -655914);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((((((a18==9) || (a18==10)) || (a18==11)) && (input == 2)) && (a15==6)) && (a24==2)))){
      a3 = ((((a3 * 10)/ 7) - -506955) * 1);
       a24 = 1;
       a18 = 9;
       return -1;
     } else if(((a24==0) && ((a15==6) && ((( a3 <= 115 && (a18==12)) || ( ((115 < a3) && (306 >= a3)) && (a18==8))) && (input == 5))))){
      a3 = (((((a3 % 300057)- 299941) + -2) - -24950) + -24948);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((input == 3) && ((((a24==4) && (a18==9)) && a3 <= 115 ) || (( 417 < a3 && ((a24==3) && (a18==12))) || ( a3 <= 115 && ((a24==4) && (a18==8)))))))){
      a3 = ((((a3 + 0) % 300057)+ -299941) + -3);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && (((((a18==8) || (a18==9)) && (input == 4)) && (a15==4)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 + -3630) - 330740) - -61086);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==6) && ((input == 1) && (( a3 <= 115 && ((a24==2) && (a18==8))) || ((((a18==11) && (a24==1)) && 417 < a3 ) || (((a18==12) && (a24==1)) && 417 < a3 )))))){
      a3 = ((((a3 % 300057)- 299941) * 1) - 2);
       a24 = 1;
       a18 = 12;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==0) && ((a15==6) && ((input == 5) && (a18==11)))))){
      a3 = ((((((a3 + -233915) % 55)- -372) * 5) % 55)+ 320);
       a24 = 1;
       a18 = 12;
       a15 = 4;
       return -1;
     } else if(((a15==6) && (((( 417 < a3 && ((a24==0) && (a18==12))) || (((a18==8) && (a24==1)) && a3 <= 115 )) || (((a24==1) && (a18==9)) && a3 <= 115 )) && (input == 6)))){
      a3 = ((((a3 % 300057)- 299941) * 1) - 2);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && ( ((115 < a3) && (306 >= a3)) && ((a24==4) && ((input == 2) && ((a18==11) || (a18==12))))))){
      a3 = (((a3 * 5) / 5) * -5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a24==3) && ((input == 4) && (((a18==8) || (a18==9)) || (a18==10)))) && ((306 < a3) && (417 >= a3)) ) && (a15==5))){
      a3 = (((a3 / 5) + 310616) * -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((((((a18==9) || (a18==10)) || (a18==11)) && (input == 3)) && (a24==2)) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((((a3 - 175) * 5) - 464342) % 95)+ 231);
       a24 = 1;
       a18 = 12;
       return -1;
     } else if(((a24==0) && (((input == 6) && (((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) ))) && (a15==5)))){
      a3 = (((a3 / 5) - 80019) + -55888);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==4) && ((input == 3) && (((a18==8) && ((115 < a3) && (306 >= a3)) ) || (((a18==11) && a3 <= 115 ) || ((a18==12) && a3 <= 115 ))))))){
      a3 = ((((a3 % 300057)- 299941) + -2) - 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && (((input == 3) && ((a18==11) || (a18==12))) && (a24==4))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 - -556691) + 19755) + 1901);
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 22;
     } else if((( a3 <= 115 && ((a15==6) && (((a18==11) || ((a18==9) || (a18==10))) && (input == 1)))) && (a24==0))){
      a3 = (((((a3 % 95)+ 211) - 337944) + 322681) + 15262);
       a24 = 1;
       a18 = 11;
       return 25;
     } else if(((( a3 <= 115 && ((input == 2) && (a24==4))) && (a18==10)) && (a15==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==6) && ((a24==0) && ((( ((306 < a3) && (417 >= a3)) && (a18==9)) || (( ((115 < a3) && (306 >= a3)) && (a18==12)) || ( ((306 < a3) && (417 >= a3)) && (a18==8)))) && (input == 4))))){
      a3 = (((((a3 * 5) - 539276) - -945607) % 55)- -325);
       a18 = 9;
       return 22;
     } else if((((input == 5) && ((((a18==8) && (a24==2)) && a3 <= 115 ) || (( 417 < a3 && ((a24==1) && (a18==11))) || (((a24==1) && (a18==12)) && 417 < a3 )))) && (a15==6))){
      a3 = (((((a3 % 300057)- 299941) * 1) + 541081) - 541082);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && (( ((115 < a3) && (306 >= a3)) && (((a18==9) || (a18==10)) && (input == 6))) && (a15==6)))){
      a3 = (((a3 + 502459) + 8631) + -1092299);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((( ((115 < a3) && (306 >= a3)) && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 1))) && (a15==5)) && (a24==3))){
      a3 = (((a3 + -295614) * 2) + -4517);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((input == 1) && (((a18==12) && a3 <= 115 ) || ( ((115 < a3) && (306 >= a3)) && (a18==8))))) && (a24==0))){
      a3 = (((((a3 % 300057)- 299941) + -3) * 9)/ 10);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==1) && (((( 417 < a3 && (a18==8)) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12)))) && (input == 2)) && (a15==5)))){
      a3 = (((a3 - 225429) / 5) + -274418);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==3) && ((a15==6) && ((input == 2) && ((a18==10) || ((a18==8) || (a18==9)))))))){
       a24 = 0;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && ((a15==5) && ((a24==0) && ((input == 4) && (a18==8)))))){
       a15 = 4;
       return -1;
     } else if(((((((a18==8) || (a18==9)) && (input == 3)) && (a15==5)) && 417 < a3 ) && (a24==0))){
      a3 = ((((a3 * 9)/ 10) - -58077) + -636180);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && ((a15==6) && ((input == 3) && (((a18==8) || (a18==9)) || (a18==10))))) && (a24==1))){
      a3 = ((((a3 - 362576) % 55)- -361) * 1);
       a18 = 8;
       return -1;
     } else if((((a15==4) && ((a24==4) && (((a18==9) || (a18==10)) && (input == 4)))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 / -5) / 5) - 368802);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((((input == 4) && ((a18==9) || (a18==10))) && (a24==1)) && (a15==5)) && 417 < a3 )){
      a3 = ((((a3 % 55)- -317) + 43) + -53);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if((((a15==6) && (((input == 2) && 417 < a3 ) && (a18==8))) && (a24==0))){
       return 21;
     } else if((( ((115 < a3) && (306 >= a3)) && (((input == 5) && (a18==8)) && (a24==4))) && (a15==4))){
      a3 = ((((a3 * 10)/ 2) + 361821) - -109713);
       a24 = 0;
       a18 = 10;
       a15 = 5;
       return 22;
     } else if(((((( ((115 < a3) && (306 >= a3)) && (a18==8)) || (( a3 <= 115 && (a18==11)) || ( a3 <= 115 && (a18==12)))) && (input == 1)) && (a24==4)) && (a15==5))){
      a3 = (((((a3 / 5) - 388906) * 1) % 95)- -232);
       a24 = 3;
       a18 = 12;
       a15 = 4;
       return 25;
     } else if(((a18==8) && ((a15==4) && ( ((115 < a3) && (306 >= a3)) && ((a24==4) && (input == 2)))))){
      a3 = (((a3 + -348052) * 1) * 1);
       a24 = 0;
       return -1;
     } else if((((a24==1) && ((( a3 <= 115 && (a18==12)) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 5))) && (a15==5))){
      a3 = ((((a3 + 460537) - -99317) % 300057)+ -299941);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==4) && ((input == 1) && ((a18==11) || (a18==12)))) && ((115 < a3) && (306 >= a3)) ) && (a24==4))){
      a3 = (((a3 + -264808) / 5) + -532776);
       a24 = 1;
       a18 = 11;
       a15 = 5;
       return 22;
     } else if(((a15==5) && ((a24==4) && (((( a3 <= 115 && (a18==11)) || ((a18==12) && a3 <= 115 )) || ( ((115 < a3) && (306 >= a3)) && (a18==8))) && (input == 2))))){
      a3 = ((((a3 - 0) % 300057)+ -299941) * 1);
       a18 = 12;
       return 26;
     } else if((((input == 3) && (( 417 < a3 && ((a18==12) && (a24==1))) || (((a18==8) && (a24==2)) && a3 <= 115 ))) && (a15==5))){
      a3 = ((((a3 % 300057)+ -299941) + 186485) + -186486);
       a24 = 3;
       a18 = 12;
       a15 = 6;
       return 25;
     }
     return calculate_output3(input);
 }
 int calculate_output3(int input) {
     if(( ((115 < a3) && (306 >= a3)) && ((a15==6) && ((a24==1) && ((input == 1) && ((a18==10) || ((a18==8) || (a18==9)))))))){
      a3 = ((((a3 * 5) - 228379) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a18==10) && ((a24==0) && ((input == 5) && (a15==6)))))){
      a3 = (((((a3 - 578654) + 578540) * 5) % 95)- -177);
       a24 = 4;
       a18 = 12;
       a15 = 4;
       return -1;
     } else if((((a18==10) && ( ((115 < a3) && (306 >= a3)) && ((a24==3) && (input == 5)))) && (a15==4))){
      a3 = (((a3 + 480105) + -828894) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a18==8) && ((input == 1) && (a24==0))) && (a15==5)) && a3 <= 115 )){
      a3 = (((((a3 * 9)/ 10) / 5) % 95)- -211);
       a24 = 2;
       a18 = 9;
       return 26;
     } else if(((a15==5) && ((((input == 1) && ((a18==9) || (a18==10))) && (a24==4)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = ((((a3 - 220252) + -152971) - -519832) + -704390);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && (((a18==9) && (input == 3)) && (a15==6))) && (a24==2))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && ((a15==5) && ( ((306 < a3) && (417 >= a3)) && ((input == 6) && (((a18==8) || (a18==9)) || (a18==10))))))){
      a3 = (((a3 - -224713) + -318603) - 374075);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( a3 <= 115 && (((input == 5) && (a15==6)) && (a18==12))) && (a24==2))){
      a3 = (((((a3 + 0) - -198715) - -161935) % 55)- -361);
       a24 = 0;
       return -1;
     } else if((((a18==9) && (((input == 2) && (a24==3)) && a3 <= 115 )) && (a15==4))){
       a18 = 11;
       return 25;
     } else if(((a15==5) && (( ((306 < a3) && (417 >= a3)) && ((input == 2) && ((a18==10) || ((a18==8) || (a18==9))))) && (a24==4)))){
      a3 = (((a3 / -5) * 5) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==1) && ((a18==11) && ((input == 4) && 417 < a3 ))))){
      a3 = (((((a3 * 9)/ 10) % 55)+ 322) * 1);
       a24 = 2;
       a15 = 6;
       return 25;
     } else if(((((a15==5) && ((input == 1) && (a24==3))) && a3 <= 115 ) && (a18==12))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==5) && ((a24==1) && (input == 3))) && a3 <= 115 ) && (a18==8))){
       a24 = 0;
       a15 = 4;
       return -1;
     } else if((((((input == 2) && ((a18==11) || (a18==12))) && (a15==5)) && (a24==0)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 * -5) / 5) * 5);
       a24 = 4;
       a18 = 12;
       return 21;
     } else if(((a18==11) && ((a15==5) && (( ((306 < a3) && (417 >= a3)) && (input == 2)) && (a24==3))))){
      a3 = (((a3 * -5) + 225437) + -658289);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && ((((input == 3) && ((115 < a3) && (306 >= a3)) ) && (a24==4)) && (a18==8)))){
      a3 = (((a3 + 576835) + 10477) * -1);
       a24 = 0;
       return -1;
     } else if(((((((a18==8) || (a18==9)) && (input == 5)) && (a15==5)) && 417 < a3 ) && (a24==3))){
      a3 = (((a3 / -5) * 4) / 5);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 25;
     } else if(( ((306 < a3) && (417 >= a3)) && ((((input == 6) && ((a18==8) || (a18==9))) && (a15==6)) && (a24==1)))){
      a3 = (((a3 - 221948) - 334823) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((( a3 <= 115 && ((input == 2) && (a18==10))) && (a24==4)) && (a15==5))){
       a18 = 12;
       a15 = 4;
       return 26;
     } else if(( ((115 < a3) && (306 >= a3)) && ((((((a18==9) || (a18==10)) || (a18==11)) && (input == 1)) && (a15==5)) && (a24==0)))){
      a3 = (((a3 + -27346) + -170095) + -360716);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==6) && ( 417 < a3 && (((a18==11) || ((a18==9) || (a18==10))) && (input == 5)))))){
      a3 = (((a3 + -550462) + -49929) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((( 417 < a3 && ((a18==12) && (a24==1))) || ( a3 <= 115 && ((a18==8) && (a24==2)))) && (input == 1)))){
      a3 = ((((((a3 % 95)+ 211) - 1) / 5) * 51)/ 10);
       a24 = 3;
       a18 = 8;
       a15 = 6;
       return 25;
     } else if(((a15==6) && (((( 417 < a3 && ((a24==2) && (a18==12))) || (((a18==8) && (a24==3)) && a3 <= 115 )) || (((a24==3) && (a18==9)) && a3 <= 115 )) && (input == 2)))){
      a3 = ((((a3 + 0) % 300057)- 299941) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==12) && ((((a15==5) && (input == 4)) && (a24==3)) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((a3 + -210461) / 5) - 424035);
       a24 = 4;
       a18 = 10;
       a15 = 4;
       return 25;
     } else if(((a18==8) && ((a24==2) && (((a15==5) && (input == 3)) && ((115 < a3) && (306 >= a3)) )))){
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 22;
     } else if(((a18==10) && (((a24==1) && ( ((306 < a3) && (417 >= a3)) && (input == 1))) && (a15==6)))){
      a3 = (((a3 + -210212) + -222317) + -2929);
       a18 = 11;
       return -1;
     } else if(((a15==5) && ((((input == 1) && 417 < a3 ) && (a24==3)) && (a18==10)))){
      a3 = ((((a3 - 600318) / 5) - -154691) * -3);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && (((a15==6) && (input == 3)) && (a18==8))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 * -5) / 5) + -202524);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (( a3 <= 115 && ((a18==12) && (input == 5))) && (a24==3)))){
      a3 = ((((((a3 % 55)- -362) * 5) * 5) % 55)+ 362);
       a24 = 0;
       a18 = 9;
       a15 = 6;
       return 22;
     } else if(((a24==3) && ((a15==6) && ((( 417 < a3 && (a18==9)) || (((a18==12) && ((306 < a3) && (417 >= a3)) ) || ((a18==8) && 417 < a3 ))) && (input == 3))))){
      a3 = ((((((a3 % 55)- -308) + 21) / 5) * 48)/ 10);
       a24 = 0;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && (((a15==5) && ((input == 5) && ((a18==12) || ((a18==10) || (a18==11))))) && (a24==0)))){
      a3 = ((((a3 * 9)/ 10) - -36392) - 632350);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((input == 6) && ((( 417 < a3 && ((a15==5) && ((a24==4) && (a18==11)))) || ( 417 < a3 && (((a24==4) && (a18==12)) && (a15==5)))) || ((((a18==8) && (a24==0)) && (a15==6)) && a3 <= 115 )))){
      a3 = (((((a3 * 9)/ 10) % 300057)+ -299941) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 6) && ((( 417 < a3 && ((a18==12) && (a24==2))) || ( a3 <= 115 && ((a24==3) && (a18==8)))) || (((a18==9) && (a24==3)) && a3 <= 115 ))) && (a15==5))){
      a3 = ((((a3 + 0) % 300057)+ -299941) - 3);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==2) && (( a3 <= 115 && (input == 4)) && (a15==6))) && (a18==9))){
       a24 = 1;
       a18 = 12;
       return -1;
     } else if((((a15==5) && ( 417 < a3 && ((input == 3) && ((a18==8) || (a18==9))))) && (a24==3))){
      a3 = (((a3 + -600125) / 5) - 225046);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ( ((306 < a3) && (417 >= a3)) && ((((a18==11) || (a18==12)) && (input == 5)) && (a15==6))))){
      a3 = (((a3 * -5) * 5) + -417846);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && (((( 417 < a3 && ((a24==3) && (a18==12))) || (((a24==4) && (a18==8)) && a3 <= 115 )) || ( a3 <= 115 && ((a18==9) && (a24==4)))) && (input == 3)))){
      a3 = ((((a3 % 300057)- 299941) - 0) / 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((( 417 < a3 && (a18==9)) || (( ((306 < a3) && (417 >= a3)) && (a18==12)) || ((a18==8) && 417 < a3 ))) && (input == 1)) && (a15==6)) && (a24==3))){
      a3 = (((a3 - 600180) + -68) + -5);
       a24 = 0;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && (((a18==12) && ((a15==5) && (input == 4))) && (a24==3)))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==11) && ((a15==5) && ((a24==1) && ((input == 3) && a3 <= 115 ))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==4) && ( ((115 < a3) && (306 >= a3)) && ((input == 5) && ((a18==9) || (a18==10))))))){
       a24 = 3;
       a18 = 10;
       a15 = 6;
       return 26;
     } else if(( a3 <= 115 && ((a15==5) && ((a18==12) && ((a24==3) && (input == 2)))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((( 417 < a3 && ((a18==12) && (a24==1))) || ( a3 <= 115 && ((a18==8) && (a24==2)))) && (input == 5)) && (a15==5))){
      a3 = ((((a3 % 300057)+ -299941) + -3) + 0);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==4) && ((((a18==8) || (a18==9)) && (input == 1)) && ((115 < a3) && (306 >= a3)) )) && (a24==3))){
      a3 = (((((a3 + -336354) * 10)/ 9) + 613674) * -2);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((( a3 <= 115 && ((a18==8) && (a24==2))) || (( 417 < a3 && ((a18==11) && (a24==1))) || (((a24==1) && (a18==12)) && 417 < a3 ))) && (input == 2)) && (a15==6))){
      a3 = (((a3 / 5) / 5) - 193557);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 4) && (a24==0)) && (a18==10)) && (a15==6)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 * -5) - 26325) + -245415);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( 417 < a3 && ((a15==6) && (((((a18==9) || (a18==10)) || (a18==11)) && (input == 3)) && (a24==2))))){
      a3 = (((a3 - 600325) + -21) - 8);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((((input == 1) && (a18==8)) && ((115 < a3) && (306 >= a3)) ) && (a24==2)))){
      a3 = (((((a3 + -399259) * 10)/ 9) - -480809) - 273660);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(((((a24==3) && ((input == 6) && ((a18==10) || (a18==11)))) && a3 <= 115 ) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 6) && ((((a24==1) && (a18==12)) && 417 < a3 ) || ( a3 <= 115 && ((a24==2) && (a18==8))))) && (a15==5))){
      a3 = ((((a3 % 300057)- 299941) - 3) - 0);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==10) || ((a18==8) || (a18==9))) && (input == 5)) && (a24==0)) && (a15==5)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 - -442665) + 92897) + 22018);
       a24 = 3;
       a18 = 12;
       return 22;
     } else if((( ((306 < a3) && (417 >= a3)) && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 3)) && (a15==4))) && (a24==3))){
      a3 = (((a3 * -5) - -433285) + -717706);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((( 417 < a3 && ((input == 4) && ((a18==8) || (a18==9)))) && (a24==0)) && (a15==5))){
      a3 = (((a3 / 5) - -381686) - 967713);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==1) && (( 417 < a3 && (input == 1)) && (a18==11))) && (a15==5))){
       a24 = 2;
       a18 = 12;
       a15 = 6;
       return 21;
     } else if((((a24==1) && ((input == 5) && ((((a18==11) && ((306 < a3) && (417 >= a3)) ) || ( ((306 < a3) && (417 >= a3)) && (a18==12))) || ((a18==8) && 417 < a3 )))) && (a15==5))){
      a3 = ((((a3 % 299791)+ 418) / 5) - -420468);
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(((((a15==6) && ((input == 1) && ((306 < a3) && (417 >= a3)) )) && (a18==8)) && (a24==3))){
      a3 = (((a3 - 586621) * 1) * 1);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if((((((input == 5) && ((a18==8) || (a18==9))) && (a15==5)) && 417 < a3 ) && (a24==0))){
      a3 = ((((a3 % 95)- -153) - -494189) + -494212);
       a24 = 4;
       a18 = 11;
       return 21;
     } else if((((((input == 1) && ((a18==9) || (a18==10))) && (a15==5)) && ((306 < a3) && (417 >= a3)) ) && (a24==1))){
      a3 = ((((a3 / -5) * 10)/ 9) - 36262);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a18==11) && ((a24==1) && ( a3 <= 115 && (input == 4)))))){
      a3 = (((((a3 + 0) * 9)/ 10) % 95)+ 211);
       a24 = 0;
       a15 = 6;
       return 22;
     } else if(((a15==5) && ( a3 <= 115 && (((input == 3) && (a24==0)) && (a18==9))))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && ((a15==5) && (((a18==11) || (a18==12)) && (input == 3)))) && (a24==4))){
       a24 = 2;
       a18 = 10;
       a15 = 6;
       return 21;
     } else if((((a24==1) && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 2)) && (a15==6))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 * 5) - 144511) * 4);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((( a3 <= 115 && ((input == 3) && (a18==12))) && (a15==6)) && (a24==2))){
      a3 = (((((a3 + 507416) % 55)+ 362) / 5) + 280);
       a24 = 1;
       a18 = 11;
       return -1;
     } else if(((((((a24==3) && (a18==9)) && a3 <= 115 ) || (( 417 < a3 && ((a24==2) && (a18==12))) || (((a18==8) && (a24==3)) && a3 <= 115 ))) && (input == 5)) && (a15==5))){
      a3 = ((((a3 % 300057)+ -299941) - -3499) - 3501);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((a24==0) && ((((a18==9) || (a18==10)) || (a18==11)) && (input == 6))) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 + 251759) / 5) * 5);
       a24 = 3;
       a18 = 8;
       return 22;
     } else if(( 417 < a3 && ((a15==6) && ((a24==2) && ((input == 5) && (((a18==9) || (a18==10)) || (a18==11))))))){
      a3 = (((a3 + -600416) * 1) + -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((((a18==9) || (a18==10)) && (input == 6)) && (a24==1)) && a3 <= 115 ) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((input == 3) && (((a18==8) && 417 < a3 ) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ( ((306 < a3) && (417 >= a3)) && (a18==12))))) && (a24==2)))){
      a3 = (((a3 / -5) * 4) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && ( ((306 < a3) && (417 >= a3)) && ((a24==3) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 5)))))){
      a3 = (((a3 * -5) * 5) + -421636);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==0) && ((((input == 3) && ((a18==11) || ((a18==9) || (a18==10)))) && ((115 < a3) && (306 >= a3)) ) && (a15==5)))){
      a3 = (((((a3 % 55)+ 352) * 5) % 55)+ 346);
       a24 = 3;
       a18 = 8;
       return 21;
     } else if(((a24==1) && ((((input == 2) && a3 <= 115 ) && (a15==5)) && (a18==11)))){
      a3 = (((((a3 + 0) * 9)/ 10) % 55)+ 362);
       a24 = 0;
       a18 = 10;
       a15 = 6;
       return 26;
     } else if((((a24==4) && ((a15==4) && ((input == 6) && ((a18==11) || (a18==12))))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 - 556367) + 516565) - 261281);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a18==8) && (((input == 6) && (a15==5)) && ((115 < a3) && (306 >= a3)) )) && (a24==2))){
      a3 = (((a3 - 75636) * 5) * 1);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(((a24==1) && ((a15==6) && ((((a18==8) || (a18==9)) && (input == 5)) && ((306 < a3) && (417 >= a3)) )))){
       a24 = 0;
       a18 = 10;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a15==4) && ((input == 6) && ((a18==9) || (a18==10)))) && (a24==4)))){
      a3 = ((((a3 / -5) * 10)/ 9) * 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==6) && (((a24==0) && (((a18==11) || ((a18==9) || (a18==10))) && (input == 5))) && a3 <= 115 ))){
       a18 = 12;
       a15 = 4;
       return -1;
     } else if(((a15==6) && (((( ((306 < a3) && (417 >= a3)) && (a18==12)) || ((a18==8) && 417 < a3 )) && (input == 5)) && (a24==2)))){
      a3 = ((((a3 - 300331) % 299791)- -300208) + 1);
       a24 = 1;
       a18 = 11;
       return -1;
     } else if(((a15==6) && (((((a18==11) || (a18==12)) && (input == 6)) && (a24==1)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((a3 * 5) - 551568) - 18434);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((((a18==8) || (a18==9)) || (a18==10)) && (input == 1)) && (a15==6)) && ((115 < a3) && (306 >= a3)) ) && (a24==2))){
      a3 = ((((a3 / 5) * -5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==4) && ((input == 3) && ((a18==11) || (a18==12)))) && a3 <= 115 ) && (a24==4))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==0) && ((((((a18==8) || (a18==9)) || (a18==10)) && (input == 1)) && ((306 < a3) && (417 >= a3)) ) && (a15==5)))){
      a3 = (((a3 + -393691) - -276142) - 216630);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 4) && ((a18==9) || (a18==10))) && ((115 < a3) && (306 >= a3)) ) && (a15==5)) && (a24==2))){
       a18 = 10;
       return 22;
     } else if((( ((115 < a3) && (306 >= a3)) && (((input == 3) && ((a18==11) || (a18==12))) && (a24==1))) && (a15==6))){
      a3 = (((a3 + -510291) + -59438) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a18==10) && (((a15==4) && (input == 2)) && (a24==3))) && ((115 < a3) && (306 >= a3)) )){
      a3 = (((a3 + -521291) * 1) + -9196);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a15==6) && (((input == 6) && (a18==8)) && (a24==0))) && 417 < a3 )){
      a3 = ((((a3 + -600234) * 1) + 297586) - 297405);
       a15 = 4;
       return -1;
     } else if(((((((a18==8) || (a18==9)) && (input == 1)) && (a24==0)) && 417 < a3 ) && (a15==5))){
      a3 = (((a3 - 600243) - 161) - 12);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 5)) && (a24==1))) && (a15==6))){
      a3 = (((((a3 * 9)/ 10) * 1) % 55)+ 345);
       a18 = 11;
       a15 = 5;
       return 22;
     } else if(((((( a3 <= 115 && (a18==12)) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 1)) && (a15==5)) && (a24==1))){
      a3 = ((((a3 % 300057)- 299941) + -1) + -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((a18==9) && (input == 1)) && a3 <= 115 ) && (a24==0)) && (a15==5))){
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==4) && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 5)) && (a15==4))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 * -5) * 5) + -544020);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(( a3 <= 115 && ((a18==9) && (((a24==2) && (input == 6)) && (a15==6))))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (((((a18==11) || ((a18==9) || (a18==10))) && (input == 4)) && (a24==0)) && ((115 < a3) && (306 >= a3)) ))){
      a3 = (((((a3 % 55)- -326) / 5) * 48)/ 10);
       a24 = 3;
       a18 = 12;
       return 25;
     } else if(((((a24==3) && ((input == 4) && ((306 < a3) && (417 >= a3)) )) && (a18==8)) && (a15==6))){
      a3 = (((a3 / -5) / 5) + -274110);
       a24 = 2;
       a18 = 9;
       a15 = 5;
       return 21;
     } else if(((a24==3) && ( ((306 < a3) && (417 >= a3)) && ((a15==6) && (((a18==11) || ((a18==9) || (a18==10))) && (input == 5)))))){
      a3 = ((((a3 + -19095) / 5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((( 417 < a3 && (a18==8)) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) ))) && (input == 1))) && (a24==2))){
      a3 = ((((a3 % 95)- -152) - 524473) + 524442);
       a24 = 3;
       a18 = 12;
       a15 = 4;
       return 25;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a24==1) && (((input == 6) && (a18==11)) && (a15==6))))){
      a3 = (((a3 * 5) - 174301) - 257370);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((a24==2) && ((( ((306 < a3) && (417 >= a3)) && (a18==12)) || ((a18==8) && 417 < a3 )) && (input == 1))))){
      a3 = (((((a3 * 9)/ 10) / 5) * 5) * -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==4) && ( ((115 < a3) && (306 >= a3)) && ((input == 5) && ((a18==11) || (a18==12))))) && (a15==5))){
      a3 = (((a3 - -530317) * -1) - -511598);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((input == 6) && (((a18==8) && ((306 < a3) && (417 >= a3)) ) || (((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) ))))) && (a24==1))){
      a3 = (((a3 / -5) * 5) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 5) && (( a3 <= 115 && ((a24==1) && (a18==9))) || ((((a24==0) && (a18==12)) && 417 < a3 ) || (((a24==1) && (a18==8)) && a3 <= 115 )))) && (a15==6))){
      a3 = (((((a3 * 9)/ 10) % 55)- -362) - -1);
       a24 = 3;
       a18 = 11;
       a15 = 4;
       return 22;
     } else if(((a15==5) && (((input == 5) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ( ((306 < a3) && (417 >= a3)) && (a18==8)))) && (a24==1)))){
      a3 = (((a3 / -5) * 5) * 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==1) && ((a15==5) && ( 417 < a3 && ((input == 2) && ((a18==9) || (a18==10))))))){
      a3 = (((((a3 % 95)- -211) - 7) + -364409) - -364321);
       a24 = 2;
       a18 = 8;
       a15 = 6;
       return 26;
     } else if(( ((306 < a3) && (417 >= a3)) && ((((input == 6) && ((a18==9) || (a18==10))) && (a15==5)) && (a24==2)))){
      a3 = ((((a3 + -439044) + 888150) / 5) * -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((((input == 4) && ((a18==10) || (a18==11))) && a3 <= 115 ) && (a24==3)))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==6) && ((a24==3) && (((input == 1) && (((a18==9) || (a18==10)) || (a18==11))) && ((306 < a3) && (417 >= a3)) )))){
      a3 = ((((a3 * -5) * 10)/ 9) - 248258);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==0) && ((((a18==8) || (a18==9)) && (input == 2)) && (a15==5))) && 417 < a3 )){
      a3 = ((((a3 / -5) + 439722) * 1) * -1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((( ((306 < a3) && (417 >= a3)) && (a18==8)) || (((a18==11) && ((115 < a3) && (306 >= a3)) ) || ( ((115 < a3) && (306 >= a3)) && (a18==12)))) && (input == 2)) && (a15==6)) && (a24==2))){
      a3 = (((a3 + -286536) + 462238) * -3);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( 417 < a3 && (((input == 6) && (a18==11)) && (a15==5))) && (a24==3))){
      a3 = (((((a3 * 9)/ 10) / 5) / 5) * -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && ( ((306 < a3) && (417 >= a3)) && ((a15==6) && ((input == 2) && (((a18==9) || (a18==10)) || (a18==11))))))){
      a3 = (((a3 - -499668) - -6024) / -5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && (( a3 <= 115 && (input == 3)) && (a18==12))) && (a15==5))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==3) && ((((a18==8) || (a18==9)) && (input == 5)) && ((115 < a3) && (306 >= a3)) )))){
      a3 = (((a3 - 531322) + 519310) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==4) && ((a15==5) && (((input == 3) && ((a18==10) || ((a18==8) || (a18==9)))) && 417 < a3 )))){
      a3 = ((((a3 - 150180) - 310980) + 456741) - 595726);
       a24 = 1;
       a18 = 8;
       return 26;
     } else if((( a3 <= 115 && ((((a18==10) || (a18==11)) && (input == 4)) && (a15==6))) && (a24==2))){
      a3 = (((((a3 % 95)- -211) * 1) + 289514) + -289514);
       a24 = 3;
       a18 = 10;
       a15 = 4;
       return -1;
     } else if(((a24==0) && ((a15==6) && ((input == 3) && (( a3 <= 115 && (a18==12)) || ( ((115 < a3) && (306 >= a3)) && (a18==8))))))){
      a3 = ((((a3 + 94090) % 300057)- 299941) * 1);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ((((a18==10) || ((a18==8) || (a18==9))) && (input == 5)) && 417 < a3 )) && (a24==4))){
      a3 = ((((((a3 - 0) % 55)+ 334) * 5) % 55)- -359);
       a24 = 2;
       a18 = 9;
       a15 = 6;
       return 25;
     } else if(((a15==6) && (((((a18==10) || ((a18==8) || (a18==9))) && (input == 6)) && ((115 < a3) && (306 >= a3)) ) && (a24==3)))){
      a3 = (((a3 / 5) - -320) - -35);
       a24 = 1;
       a18 = 11;
       a15 = 4;
       return -1;
     } else if((((a24==2) && (( a3 <= 115 && (input == 2)) && (a18==9))) && (a15==6))){
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==0) && ((((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 5))))){
      a3 = ((((((a3 * 9)/ 10) % 95)+ 211) - -438126) + -438125);
       a24 = 3;
       a18 = 8;
       return 25;
     } else if(( 417 < a3 && (((a24==4) && (((a18==11) || (a18==12)) && (input == 6))) && (a15==4)))){
      a3 = (((a3 - 0) - 600138) + -71);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a24==1) && (( ((115 < a3) && (306 >= a3)) && ((input == 1) && ((a18==11) || (a18==12)))) && (a15==6)))){
       a18 = 11;
       return -1;
     } else if(((a24==4) && (((((a18==10) || ((a18==8) || (a18==9))) && (input == 4)) && ((306 < a3) && (417 >= a3)) ) && (a15==4)))){
      a3 = ((((a3 * 5) % 95)- -125) * 1);
       a24 = 1;
       a18 = 10;
       a15 = 5;
       return 25;
     } else if(((a24==1) && (( a3 <= 115 && ((((a18==10) || (a18==11)) || (a18==12)) && (input == 2))) && (a15==6)))){
      a3 = (((((a3 + 0) % 55)- -362) + 458587) - 458587);
       a24 = 0;
       a18 = 10;
       return -1;
     } else if((((a24==4) && ((a15==4) && ((a18==10) && (input == 1)))) && a3 <= 115 )){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==5) && ((a24==4) && ( ((306 < a3) && (417 >= a3)) && ((input == 6) && ((a18==11) || (a18==12))))))){
      a3 = (((a3 * 5) - 574289) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a15==4) && ((input == 2) && ((a18==11) || ((a18==9) || (a18==10))))) && (a24==3)) && 417 < a3 )){
      a3 = (((a3 + -600129) - 241) / 5);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((a24==0) && (((a18==12) && (input == 1)) && (a15==5))))){
      a3 = (((a3 * -5) / 5) * 5);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((306 < a3) && (417 >= a3)) && (((input == 6) && (a18==12)) && (a15==6))) && (a24==1))){
      a3 = (((a3 * 5) * -5) + -554351);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && ((((input == 2) && ((a18==11) || (a18==12))) && (a24==3)) && (a15==4)))){
      a3 = (((a3 - 406098) / 5) - 3614);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((input == 5) && (((a18==8) && ((115 < a3) && (306 >= a3)) ) || (((a18==11) && a3 <= 115 ) || ((a18==12) && a3 <= 115 )))) && (a15==5)) && (a24==4))){
      a3 = ((((((a3 + 0) % 55)- -361) * 5) % 55)+ 352);
       a24 = 0;
       a18 = 10;
       a15 = 6;
       return 25;
     } else if(((((a24==2) && ( a3 <= 115 && (input == 3))) && (a15==5)) && (a18==12))){
      a3 = ((((((a3 % 55)+ 361) * 5) - -268768) % 55)+ 318);
       a24 = 0;
       a15 = 6;
       return 25;
     } else if(((( ((306 < a3) && (417 >= a3)) && ((input == 3) && ((a18==8) || (a18==9)))) && (a24==1)) && (a15==6))){
       a24 = 4;
       a18 = 12;
       a15 = 4;
       return 21;
     } else if(((a24==4) && ((a15==5) && ( ((306 < a3) && (417 >= a3)) && ((input == 1) && ((a18==11) || (a18==12))))))){
      a3 = ((((a3 - -278437) / -5) * 10)/ 9);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((a24==4) && (((a18==11) || (a18==12)) && (input == 5))) && (a15==5)) && ((306 < a3) && (417 >= a3)) )){
       a24 = 1;
       a18 = 11;
       a15 = 6;
       return 25;
     } else if(((a24==3) && ( ((115 < a3) && (306 >= a3)) && (((input == 1) && ((a18==8) || (a18==9))) && (a15==5))))){
      a3 = ((((a3 - -315256) + 60222) + 127166) - 671543);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 3) && ((a18==9) || (a18==10))) && ((306 < a3) && (417 >= a3)) ) && (a24==1)) && (a15==5))){
       a18 = 12;
       a15 = 6;
       return 21;
     } else if((((a15==4) && (((input == 3) && (((a18==8) || (a18==9)) || (a18==10))) && (a24==4))) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 - 463226) - 56049) - 30162);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a15==5) && ((((a18==8) || (a18==9)) || (a18==10)) && (input == 3))) && ((306 < a3) && (417 >= a3)) ) && (a24==4))){
      a3 = (((a3 / -5) + -114427) + -219360);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((input == 6) && (( 417 < a3 && (a18==8)) || (((a18==11) && ((306 < a3) && (417 >= a3)) ) || ( ((306 < a3) && (417 >= a3)) && (a18==12))))) && (a15==5)) && (a24==1))){
      a3 = ((((a3 * 9)/ 10) - 553048) / 5);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((( ((306 < a3) && (417 >= a3)) && (a18==12)) || ( 417 < a3 && (a18==8))) && (input == 4))) && (a24==2))){
      a3 = (((a3 - 599977) - 211) + -66);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ( ((306 < a3) && (417 >= a3)) && ((a24==0) && ((input == 4) && ((a18==11) || (a18==12))))))){
      a3 = (((a3 - 120) + -386244) - -386210);
       a24 = 4;
       a18 = 10;
       return 21;
     } else if((( 417 < a3 && ((a24==3) && ((input == 4) && (a18==10)))) && (a15==5))){
      a3 = ((((a3 + -546509) / 5) - -523087) * -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( a3 <= 115 && ((a15==4) && (((input == 2) && ((a18==11) || (a18==12))) && (a24==4))))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((((a24==3) && ((a15==4) && (input == 3))) && (a18==9)) && a3 <= 115 )){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a15==5) && ((((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )) && (input == 4))) && (a24==0))){
      a3 = ((((a3 - -479640) % 300057)+ -299941) - 1);
       a24 = 3;
       a18 = 12;
       return 25;
     } else if((((((a18==11) && (input == 1)) && (a24==3)) && ((306 < a3) && (417 >= a3)) ) && (a15==5))){
      a3 = ((((a3 * -5) - -47142) * 5) * -2);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ((a24==1) && ( ((115 < a3) && (306 >= a3)) && ((input == 4) && ((a18==9) || (a18==10))))))){
      a3 = ((((a3 * -5) / 5) + 310281) * -1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && (( 417 < a3 && (((a18==8) || (a18==9)) && (input == 4))) && (a15==5)))){
       a18 = 8;
       return 25;
     } else if((((((a15==4) && (input == 3)) && (a18==10)) && ((115 < a3) && (306 >= a3)) ) && (a24==3))){
      a3 = (((a3 - 561788) + -19243) + -17216);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((a24==0) && (((input == 6) && ((115 < a3) && (306 >= a3)) ) && (a15==5))) && (a18==12))){
      a3 = (((a3 / 5) + 441283) - 445116);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==6) && (((input == 6) && (a18==8)) && (a24==3))))){
      a3 = (((((a3 + -47974) * 10)/ 9) + 376027) + -859195);
       a24 = 0;
       a15 = 4;
       return -1;
     } else if(( ((115 < a3) && (306 >= a3)) && (((a24==1) && ((input == 2) && ((a18==9) || (a18==10)))) && (a15==5)))){
      a3 = (((a3 + 194776) + 314910) + 59449);
       a24 = 0;
       a18 = 11;
       a15 = 6;
       return 21;
     } else if(((a15==5) && (((a24==0) && (((a18==10) || ((a18==8) || (a18==9))) && (input == 6))) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((a3 + 363685) / 5) + -317846);
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && ((a24==2) && ((input == 3) && ((a18==9) || (a18==10))))) && (a15==5))){
      a3 = (((a3 / 5) + 249200) + -248857);
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 26;
     } else if(((a24==1) && ((((input == 3) && ((a18==9) || (a18==10))) && a3 <= 115 ) && (a15==5)))){
      a3 = ((((a3 / 5) - -218828) % 95)- -166);
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(((a24==3) && ((a15==5) && (((a18==10) && (input == 2)) && 417 < a3 )))){
      a3 = ((((a3 + 0) % 55)- -355) + 8);
       a18 = 8;
       a15 = 6;
       return 26;
     } else if(((a24==1) && (((((a18==8) || (a18==9)) && (input == 4)) && (a15==6)) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((((a3 - 152) * 9)/ 10) / 5) - -151);
       a18 = 10;
       return -1;
     } else if(((a24==0) && ( a3 <= 115 && ((a15==5) && ((input == 6) && (a18==8)))))){
       a15 = 4;
       return -1;
     } else if((((a15==6) && ((input == 1) && ((((a18==11) && ((115 < a3) && (306 >= a3)) ) || ((a18==12) && ((115 < a3) && (306 >= a3)) )) || ((a18==8) && ((306 < a3) && (417 >= a3)) )))) && (a24==2))){
      a3 = ((((a3 - -516636) + 36214) - -15968) * -1);
       a18 = 10;
       return -1;
     } else if(((a15==6) && (( ((306 < a3) && (417 >= a3)) && ((input == 2) && (a18==11))) && (a24==1)))){
      a3 = (((a3 + 536313) / -5) - 222899);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && ( 417 < a3 && ((a24==2) && (((a18==10) || (a18==11)) && (input == 6)))))){
      a3 = (((a3 + -600084) - 198) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((((input == 5) && ((a18==9) || (a18==10))) && (a15==4)) && 417 < a3 ) && (a24==4))){
      a3 = (((a3 / -5) / 5) + -396652);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && ((((a18==12) || ((a18==10) || (a18==11))) && (input == 6)) && (a15==5))) && (a24==3))){
      a3 = (((a3 / 5) - 224913) + -244476);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a18==8) && (((a15==6) && ((input == 2) && (a24==3))) && ((306 < a3) && (417 >= a3)) ))){
      a3 = (((a3 + -262113) - -794926) * 1);
       a24 = 0;
       a18 = 11;
       return -1;
     } else if(( ((306 < a3) && (417 >= a3)) && ((a15==5) && ((a24==1) && (((a18==9) || (a18==10)) && (input == 6)))))){
      a3 = (((a3 - 346964) - 81597) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==3) && ((( 417 < a3 && (a18==8)) || (( ((306 < a3) && (417 >= a3)) && (a18==11)) || ( ((306 < a3) && (417 >= a3)) && (a18==12)))) && (input == 2))) && (a15==4))){
      a3 = ((((a3 * 9)/ 10) * -1) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(( 417 < a3 && ((((input == 4) && (((a18==9) || (a18==10)) || (a18==11))) && (a15==6)) && (a24==2)))){
      a3 = ((((a3 * 9)/ 10) * -1) * 1);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((input == 3) && (( a3 <= 115 && ((a18==9) && (a24==1))) || (( 417 < a3 && ((a24==0) && (a18==12))) || ( a3 <= 115 && ((a18==8) && (a24==1)))))) && (a15==6))){
      a3 = ((((a3 % 300057)+ -299941) + -1) - 2);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((( 417 < a3 && ((a24==2) && (a18==12))) || (((a24==3) && (a18==8)) && a3 <= 115 )) || (((a24==3) && (a18==9)) && a3 <= 115 )) && (input == 2)) && (a15==5))){
      a3 = (((((a3 % 300057)+ -299941) - 3) * 9)/ 10);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==5) && (( ((115 < a3) && (306 >= a3)) && (((a18==9) || (a18==10)) && (input == 6))) && (a24==4)))){
      a3 = ((((a3 % 55)+ 341) * 1) + 10);
       a24 = 0;
       a18 = 12;
       return 21;
     } else if(((((((a18==8) || (a18==9)) && (input == 1)) && (a24==1)) && (a15==6)) && ((306 < a3) && (417 >= a3)) )){
      a3 = (((a3 / 5) * 5) + -345460);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a15==4) && ((a24==3) && (((input == 1) && (((a18==10) || (a18==11)) || (a18==12))) && a3 <= 115 )))){
       a24 = 0;
       a18 = 8;
       return -1;
     } else if((((((((a18==10) || (a18==11)) || (a18==12)) && (input == 2)) && ((115 < a3) && (306 >= a3)) ) && (a15==5)) && (a24==3))){
      a3 = ((((a3 - 172245) + -128238) * 10)/ 9);
       a24 = 1;
       a18 = 12;
       a15 = 6;
       return 26;
     } else if((((a15==6) && ( ((115 < a3) && (306 >= a3)) && (((a18==11) || (a18==12)) && (input == 3)))) && (a24==3))){
      a3 = ((((((a3 % 55)+ 320) - 12) * 5) % 55)+ 336);
       a24 = 2;
       a18 = 10;
       return -1;
     } else if(((a15==5) && ((a24==1) && ((input == 2) && (((a18==12) && a3 <= 115 ) || ((a18==8) && ((115 < a3) && (306 >= a3)) )))))){
      a3 = (((((a3 % 55)- -361) + 0) - -112814) - 112813);
       a24 = 0;
       a18 = 12;
       a15 = 6;
       return 21;
     } else if(((a15==6) && ( a3 <= 115 && ((a18==12) && ((a24==2) && (input == 1)))))){
      a3 = (((((a3 % 55)+ 361) / 5) * 5) + 2);
       a24 = 3;
       a15 = 4;
       return -1;
     } else if(((a24==2) && ( ((306 < a3) && (417 >= a3)) && (((input == 3) && ((a18==9) || (a18==10))) && (a15==5))))){
      a3 = (((a3 + 413206) - 981948) + 122837);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((a24==3) && (((a18==10) && ((input == 6) && ((115 < a3) && (306 >= a3)) )) && (a15==4)))){
      a3 = (((a3 * 5) + -583604) * 1);
       a24 = 0;
       a18 = 8;
       return -1;
     } else if(((a15==5) && (((( a3 <= 115 && (a18==12)) || ( ((115 < a3) && (306 >= a3)) && (a18==8))) && (input == 3)) && (a24==1)))){
      a3 = ((((a3 % 299791)- -300208) * 1) - 0);
       a24 = 0;
       a18 = 8;
       a15 = 6;
       return 21;
     } else if(((((((a18==11) || (a18==12)) && (input == 5)) && ((115 < a3) && (306 >= a3)) ) && (a15==6)) && (a24==3))){
      a3 = (((a3 - 580000) + -16558) - 2126);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((((a24==4) && ( 417 < a3 && (((a18==10) || ((a18==8) || (a18==9))) && (input == 1)))) && (a15==5))){
      a3 = ((((a3 + -599887) + -522) + 441660) + -441353);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if(((((input == 5) && ((((a18==11) && ((306 < a3) && (417 >= a3)) ) || ((a18==12) && ((306 < a3) && (417 >= a3)) )) || ((a18==8) && 417 < a3 ))) && (a24==2)) && (a15==5))){
      a3 = (((((a3 * 9)/ 10) / 5) % 55)+ 324);
       a24 = 0;
       a18 = 9;
       a15 = 6;
       return 25;
     } else if(((a15==6) && (((input == 6) && ((( ((115 < a3) && (306 >= a3)) && (a18==11)) || ( ((115 < a3) && (306 >= a3)) && (a18==12))) || ((a18==8) && ((306 < a3) && (417 >= a3)) ))) && (a24==2)))){
      a3 = (((a3 + -230893) + -45185) - 185687);
       a24 = 0;
       a18 = 8;
       a15 = 4;
       return -1;
     } else if((( ((115 < a3) && (306 >= a3)) && ((((a18==9) || (a18==10)) && (input == 1)) && (a15==5))) && (a24==2))){
      a3 = (((a3 / 5) + -508446) - 23939);
       a24 = 1;
       a18 = 9;
       a15 = 4;
       return -1;
     } else if((((a15==5) && ( a3 <= 115 && ((input == 3) && ((a18==10) || (a18==11))))) && (a24==0))){
      a3 = ((((a3 % 299791)- -300208) - 0) * 1);
       a24 = 2;
       a18 = 12;
       return 21;
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
