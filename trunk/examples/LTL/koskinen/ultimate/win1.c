// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: win1.c
// Property: G(a => F r)

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

int A; int R;
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
ULONG             BytesToMove;
ULONG             FirstHalf;
ULONG             SecondHalf;
KIRQL             CancelIrql;
BOOLEAN           LockHeld;
SERIAL_TIMEOUTS   CurrentTimeouts;

void init() { 
  A = R = 0; 
  status = STATUS_UNSUCCESSFUL; 
  CurrentTimeouts = nondet();
  k = nondet();
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

int IoGetCurrentIrpStackLocation(int a) {}

void RemoveReferenceAndCompleteRequest(int a, int b) {}

void body()
{

  A = 1; A = 0; // KeAcquireSpinLock( &lock, &OldIrql);

  while ((nondet() && k>0) && (nondet() || nondet())) {

    ListElement = nondet();
    Irp = nondet();
    IrpSp = nondet();
    CancelIrql = nondet();

    k--;

    Irp= nondet();

    IoAcquireCancelSpinLock(&CancelIrql);

    if (nondet()) {

      IoReleaseCancelSpinLock(CancelIrql);

      continue;
    }

    // IoSetCancelRoutine(Irp, NULL);
    IoReleaseCancelSpinLock(CancelIrql);
    R = 1; R = 0; // KeReleaseSpinLock(&lock, OldIrql);

    //CALL TO TryToSatisfyRead( deviceExtension);
    {
      status=STATUS_UNSUCCESSFUL;
      Irp=NULL;
      LockHeld = TRUE;

      A = 1; A = 0; //KeAcquireSpinLock(&lock,&OldIrql);

      if (nondet() && nondet()) {
	//
	//  there is an IRP and there are characters waiting
	//
	Irp=nondet();

	IrpSp=IoGetCurrentIrpStackLocation(Irp);

	BytesToMove=nondet();

	if (nondet()) {
	  FirstHalf=nondet();

	  SecondHalf=BytesToMove-FirstHalf;


	} else {
	}
      }
      else
	{
	  if (nondet())
	    {
	      Irp = nondet();


	      IoAcquireCancelSpinLock(&CancelIrql);
	      if (nondet())
		{
		  IoReleaseCancelSpinLock(CancelIrql);

		  R = 1; R = 0; // KeReleaseSpinLock( &lock, OldIrql);

		  RemoveReferenceAndCompleteRequest(Irp,
						    STATUS_CANCELLED);
		  LockHeld = FALSE;
		}
	      else
		{
		  CurrentTimeouts = nondet();

		  if(nondet())
		    {
		      IoReleaseCancelSpinLock(CancelIrql);

		      R = 1; R = 0; // KeReleaseSpinLock( &lock, OldIrql);

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

	      Irp = NULL;
	    }

	}

      if (LockHeld == 1)
	{
	  R = 1; R = 0; //KeReleaseSpinLock( &lock, OldIrql);
	}

      if (Irp != 0) {
	//
	//  if irp isn't null, then we handled one
	//
	RemoveReferenceAndCompleteRequest(Irp, STATUS_SUCCESS);


      }



    }
    //-------------------------------------------------------------
    A=1; A=0; // KeAcquireSpinLock(&lock, &OldIrql)
      }

  R=1; R=0; //KeReleaseSpinLock( &lock, OldIrql);

  while(1) {
    { int ddd; ddd = ddd; }
  }
}

int main() {}
