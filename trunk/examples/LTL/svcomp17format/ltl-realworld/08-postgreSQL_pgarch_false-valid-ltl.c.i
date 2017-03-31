extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern unsigned int __VERIFIER_nondet_unsigned() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
unsigned int last_copy_time = 0;
unsigned int curtime;
int got_SIGHUP;
int wakend;
void init()
{
  wakend = 1;
  got_SIGHUP = __VERIFIER_nondet_int();
}
void ProcessConfigFile(int a)
{
}
int XLogArchivingActive()
{
 return __VERIFIER_nondet_int();
}
void pgarch_ArchiverCopyLoop()
{
}
unsigned int time(int a)
{
 return __VERIFIER_nondet_unsigned();
}
void pg_usleep(int a)
{
}
int PostmasterIsAlive(int a)
{
 return __VERIFIER_nondet_int();
}
int main() {
 init();
 wakend = 1;
 do
 {
  if (got_SIGHUP)
  {
   got_SIGHUP = 0;
   ProcessConfigFile(1);
   if (!XLogArchivingActive())
    break;
  }
  if (wakend)
  {
   wakend = 0;
   pgarch_ArchiverCopyLoop();
   last_copy_time = time(0);
  }
  if (!wakend)
  {
   pg_usleep(1000 * 1000000L);
   curtime = time(0);
   if ((unsigned int) (curtime - last_copy_time) >= (unsigned int) 1000)
   {
    wakend = 1;
   }
  }
 } while (PostmasterIsAlive(1));
}
