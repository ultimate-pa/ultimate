/*
 * Global Variables
 */
var stoppingFlag, stoppingEvent, stopped : bool;
var pendingIo : int;

/*
 *
 */
procedure ULTIMATE.start()
modifies stoppingFlag, stoppingEvent, stopped, pendingIo;
{
  pendingIo := 1;
  stopped := false;
  stoppingEvent := false;
  stoppingFlag := false;

  fork 0 ServerThread();
  fork 1 DeviceThread();
  fork 2 DeviceThread();
  fork 3 DeviceThread();
  fork 4 DeviceThread();
}

/*
 * Device thread ("Add")
 */
procedure DeviceThread()
modifies pendingIo, stoppingEvent;
{
  while (*) {
    call Enter();

    // do work
    assert !stopped;

    call Exit();
  }
}

procedure Enter()
modifies pendingIo;
{
  //atomic {
    assume !stoppingFlag;
    pendingIo := pendingIo + 1;
  //}
}

procedure Exit()
modifies pendingIo, stoppingEvent;
{
  atomic {
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
      stoppingEvent := true;
    }
  }
}

/*
 * Server thread ("Stop")
 */
procedure ServerThread()
modifies stoppingFlag, pendingIo, stoppingEvent, stopped;
{
  stoppingFlag := true;
  call Close();
  assume stoppingEvent;
  stopped := true;
}

procedure Close()
modifies pendingIo, stoppingEvent;
{
  atomic {
    pendingIo := pendingIo - 1;
    if (pendingIo == 0) {
      stoppingEvent := true;
    }
  }
}
