extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

#define NTSTATUS int
#define STATUS_CANCELLED 2
#define STATUS_UNSUCCESSFUL 1
#define STATUS_SUCCESS 1
#define STATUS_TIMEOUT 3
#define SERIAL_TIMEOUTS int
#define PLIST_ENTRY int
#define PIRP int
#define KIRQL int
#define ULONG int
#define PIO_STACK_LOCATION int
#define BOOLEAN int
#define TRUE 1
#define FALSE 0

#include<stdio.h>

int a; int r;
int irql;
int csl;
NTSTATUS          status;
KIRQL             OldIrql;
SERIAL_TIMEOUTS   CurrentTimeouts;
int lock;
int k;
PLIST_ENTRY         ListElement;
PIRP                Irp;
PIO_STACK_LOCATION  IrpSp;
KIRQL               CancelIrql;
KIRQL             CancelIrql;
BOOLEAN           LockHeld;
SERIAL_TIMEOUTS   CurrentTimeouts;

// Initialization routine
int __INITIALIZED = 0;
void env_init() {
  status = STATUS_UNSUCCESSFUL;
  CurrentTimeouts = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
	__INITIALIZED = 1;
}  
  

void KeAcquireSpinLock(int * lp, int * ip) {
  (*lp) = 1;
  (*ip) = irql;
}

void KeReleaseSpinLock(int * lp, int i) {
  (*lp) = 0;
  irql = i;
}


void IoAcquireCancelSpinLock(int * ip) {
  csl = 1;
  (*ip) = irql;
}

void IoReleaseCancelSpinLock(int ip) {
  csl = 0;
  irql = ip;
}

int IoGetCurrentIrpStackLocation(int a) { return __VERIFIER_nondet_int(); }

void RemoveReferenceAndCompleteRequest(int a, int b) {}

int main()
{
	env_init();

  a = 1; a = 0; // KeAcquireSpinLock( &lock, &OldIrql);

  while ((__VERIFIER_nondet_int() && k>0) && (__VERIFIER_nondet_int() || __VERIFIER_nondet_int())) {

    ListElement = __VERIFIER_nondet_int();
    Irp = __VERIFIER_nondet_int();
    IrpSp = __VERIFIER_nondet_int();
    CancelIrql = __VERIFIER_nondet_int();

    k--;

    Irp= __VERIFIER_nondet_int();

    IoAcquireCancelSpinLock(&CancelIrql);

    if (__VERIFIER_nondet_int()) {

      IoReleaseCancelSpinLock(CancelIrql);

      continue;
    }

    // IoSetCancelRoutine(Irp, NULL);
    IoReleaseCancelSpinLock(CancelIrql);
    r = 1;r = 0; // KeReleaseSpinLock(&lock, OldIrql);

    //CALL TO TryToSatisfyRead( deviceExtension);
    {
      status=STATUS_UNSUCCESSFUL;
      Irp=0;
      LockHeld = TRUE;

      a = 1; a= 0; //KeAcquireSpinLock(&lock,&OldIrql);

      if (__VERIFIER_nondet_int() && __VERIFIER_nondet_int()) {
	//
	//  there is an IRP and there are characters waiting
	//
	Irp=__VERIFIER_nondet_int();

	IrpSp=IoGetCurrentIrpStackLocation(Irp);

	
      }
      else
	{
	  if (__VERIFIER_nondet_int())
	    {
	      Irp = __VERIFIER_nondet_int();


	      IoAcquireCancelSpinLock(&CancelIrql);
	      if (__VERIFIER_nondet_int())
		{
		  IoReleaseCancelSpinLock(CancelIrql);

		  r = 1; r = 0; // KeReleaseSpinLock( &lock, OldIrql);

		  RemoveReferenceAndCompleteRequest(Irp,
						    STATUS_CANCELLED);
		  LockHeld = FALSE;
		}
	      else
		{
		  CurrentTimeouts = __VERIFIER_nondet_int();

		  if(__VERIFIER_nondet_int())
		    {
		      IoReleaseCancelSpinLock(CancelIrql);

		      r = 1; r = 0; // KeReleaseSpinLock( &lock, OldIrql);

		      RemoveReferenceAndCompleteRequest(
							Irp, STATUS_TIMEOUT);

		      LockHeld = FALSE;
		    }
		  else
		    {
		      IoReleaseCancelSpinLock(CancelIrql);
		      k--;
		    }
		}

	      Irp = 0;
	    }

	}

      if (LockHeld == 1)
	{
	  r = 1; r = 0; //KeReleaseSpinLock( &lock, OldIrql);
	}

      if (Irp != 0) {
	//
	//  if irp isn't null, then we handled one
	//
	RemoveReferenceAndCompleteRequest(Irp, STATUS_SUCCESS);


      }



    }
    //-------------------------------------------------------------
    a=1; a=0; // KeAcquireSpinLock(&lock, &OldIrql)
      }

  r=1; r=0; //KeReleaseSpinLock( &lock, OldIrql);

  while(1) {
    { int ddd; ddd = ddd; }
  }
}
