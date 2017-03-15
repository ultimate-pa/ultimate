extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

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

int lock;
int CancelIrql;
int irql;
int csl;
int CurrentWaitIrp=0;
int NewMask;
int CancelIrp;
int Mask;
int length;
int NewTimeouts;
int SerialStatus;
int pBaudRate;
int pLineControl;
int LData;
int LStop;
int LParity;
int Mask;
int keA;
int keR;
void IoAcquireCancelSpinLock(int * ip) {
   csl = 1;
   (*ip) = irql;
}
void IoReleaseCancelSpinLock(int ip) {
   csl = 0;
   irql = ip;
}
void IoMarkIrpPending(int x) {}
void RemoveReferenceAndCompleteRequest(int x,int y) {}
void RemoveReferenceForDispatch(int x) {}
void ProcessConnectionStateChange(int x) {}
int DeviceObject;
int Irp;
int status;
int OldIrql;
int main()
{
 keA = keR = 0;
 lock = 0;
 CancelIrql = __VERIFIER_nondet_int();
 irql = __VERIFIER_nondet_int();
 csl = __VERIFIER_nondet_int();
 DeviceObject = __VERIFIER_nondet_int();
 Irp = __VERIFIER_nondet_int();
 status=1;
 OldIrql;
 status = __VERIFIER_nondet_int();
 keA = 0;
 keR = 0;
 length = __VERIFIER_nondet_int();
 NewTimeouts = __VERIFIER_nondet_int();
 SerialStatus=__VERIFIER_nondet_int();
 pBaudRate = __VERIFIER_nondet_int();
 pLineControl = __VERIFIER_nondet_int();
 LData = 0;
 LStop = 0;
 LParity = 0;
 Mask = 0xff;
 if (2 != status)
 {
  while(1) { int ddd2; ddd2 = ddd2; }
 }
 if(1)
 {
  if(__VERIFIER_nondet_int())
  {
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   CurrentWaitIrp=0;
   NewMask = __VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   else
   {
    keA = 1; keA = 0;
    lock = 1; OldIrql = irql;
    NewMask = __VERIFIER_nondet_int();
    keR = 1; keR = 0;
    lock = 0; irql = OldIrql;
    if (CurrentWaitIrp != 0)
    {
     RemoveReferenceAndCompleteRequest(CurrentWaitIrp, 2);
    }
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   CurrentWaitIrp=0;
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   CurrentWaitIrp=__VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status=1;
   }
   else
   {
    IoMarkIrpPending(Irp);
    status=7;
   }
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
   if (CurrentWaitIrp != 0)
   {
    RemoveReferenceAndCompleteRequest(CurrentWaitIrp, 2);
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   CancelIrp = __VERIFIER_nondet_int();
   Mask= __VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   if (Mask && 10)
   {
    keA = 1; keA = 0;
    lock = 1; OldIrql = irql;
    length = __VERIFIER_nondet_int();
    while (length>0)
    {
     length--;
     CancelIrp=__VERIFIER_nondet_int();
     IoAcquireCancelSpinLock(&CancelIrql);
     if (__VERIFIER_nondet_int())
     {
      IoReleaseCancelSpinLock(CancelIrql);
      continue;
     }
     IoReleaseCancelSpinLock(CancelIrql);
     keR = 1; keR = 0;
     lock = 0; irql = OldIrql;
     RemoveReferenceAndCompleteRequest(CancelIrp, 11);
     keA = 1; keA = 0;
     lock = 1; OldIrql = irql;
               }
               CancelIrp=((void *)0);
               if (__VERIFIER_nondet_int())
               {
     CancelIrp=__VERIFIER_nondet_int();
               }
               keR = 1; keR = 0;
      lock = 0; irql = OldIrql;
               if (CancelIrp != ((void *)0))
      {
     RemoveReferenceAndCompleteRequest(CancelIrp, 11);
               }
   }
  }
  else if(__VERIFIER_nondet_int())
  {
           if (__VERIFIER_nondet_int())
     {
    status = 4;
           }
  }
  else if(__VERIFIER_nondet_int())
  {
   NewTimeouts = __VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   if (__VERIFIER_nondet_int())
   {
    status = 15;
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
  }
  else if(__VERIFIER_nondet_int())
  {
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
  }
  else if(__VERIFIER_nondet_int())
  {
   SerialStatus=__VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
  }
  else if(__VERIFIER_nondet_int())
  {
     keA = 1; keA = 0;
     lock = 1; OldIrql = irql;
     if (__VERIFIER_nondet_int())
     {
     }
     else
     {
    if (__VERIFIER_nondet_int())
    {
    }
     }
     keR = 1; keR = 0;
     lock = 0; irql = OldIrql;
     ProcessConnectionStateChange(DeviceObject);
  }
  else if(__VERIFIER_nondet_int())
  {
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   else
   {
    keA = 1; keA = 0;
    lock = 1; OldIrql = irql;
    keR = 1; keR = 0;
    lock = 0; irql = OldIrql;
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   pBaudRate = __VERIFIER_nondet_int();
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   else
   {
    keA = 1; keA = 0;
    lock = 1; OldIrql = irql;
    keR = 1; keR = 0;
    lock = 0; irql = OldIrql;
   }
  }
  else if(__VERIFIER_nondet_int())
  {
   pLineControl = __VERIFIER_nondet_int();
   LData = 0;
   LStop = 0;
   LParity = 0;
   Mask = 0xff;
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   if(1)
   {
    if(__VERIFIER_nondet_int())
    {
     LData = 27;
     Mask = 0x1f;
    }
    else if(__VERIFIER_nondet_int())
    {
     LData = 24;
     Mask = 0x3f;
    }
    else if(__VERIFIER_nondet_int())
    {
     LData = 25;
     Mask = 0x7f;
    }
    else if(__VERIFIER_nondet_int())
    {
                   LData = 26;
    }
    else
    {
                   status = 15;
    }
   }
   if (status != 2)
   {
                        ;
   }
   if(1)
   {
    if(__VERIFIER_nondet_int())
    {
     LParity = 29;
    }
    else if(__VERIFIER_nondet_int())
    {
     LParity = 31;
    }
    else if(__VERIFIER_nondet_int())
    {
     LParity = 33;
    }
    else if(__VERIFIER_nondet_int())
    {
     LParity = 35;
    }
    else if(__VERIFIER_nondet_int())
    {
     LParity = 37;
    }
    else
    {
     status = 15;
    }
   }
   if (status != 2)
   {
   }
   if (1)
   {
    if(__VERIFIER_nondet_int())
    {
     LStop = 32;
    }
    else if(__VERIFIER_nondet_int())
    {
     if (LData != 27)
     {
      status = 15;
     }
     LStop = 37;
    }
    else if(__VERIFIER_nondet_int())
    {
     if (LData == 27)
     {
      status = 15;
     }
     LStop = 33;
    }
    else
    {
     status = 15;
    }
   }
   if (status != 2)
   {
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
  }
  else if(__VERIFIER_nondet_int())
  {
   if (__VERIFIER_nondet_int())
   {
    status = 4;
   }
   keA = 1; keA = 0;
   lock = 1; OldIrql = irql;
   keR = 1; keR = 0;
   lock = 0; irql = OldIrql;
  }
  else if(__VERIFIER_nondet_int())
  {
  }
  else
  {
   status=41;
  }
 }
 if (status != 7)
 {
  if (Irp != ((void *)0))
  {
   RemoveReferenceAndCompleteRequest(Irp, status);
  }
 }
 RemoveReferenceForDispatch(DeviceObject);
 while (1) { int rrr; rrr = rrr; }
}
