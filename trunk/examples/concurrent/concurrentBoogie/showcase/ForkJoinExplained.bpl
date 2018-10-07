//#Safe
/*
 * We developed an extension of the Boogie specification language that can 
 * model systems that run several procedures concurrently.
 * Our extension introduces a fork statement and a join statement, we
 * explain both statements in this file.
 *
 * Author: Lars Nitzke (lars.nitzke@outlook.com)
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-08-24
 * 
 */

var g : int;

procedure ULTIMATE.start()
modifies g;
{
    var x : int;
	var z : int;

	x := 23;
	g := 2;
    // The fork statement "forks" the program execution into two threads.
	// One thread continues executing the current procedure, the other
	// thread starts to execute the procedure that is called by the
	// fork statement.
	// Both threads run concurrently but they might run at completely different
	// speeds. E.g., the system might execute statements of both threads 
	// strictly interleaved, or first all statement of one thread and only 
	// then all statements of the other thread.
	// Each thread that is create by a fork statement has an ID that we
	// will discuss later

	// Here, we fork a new thread that executes the procedure foo.
	// The thread ID is the number that was stored in variable x
	// The argument of the procedure call is 7.
    fork x foo(7);
	
	// Now, we fork another thread
	fork 77 foo(3);
	
	// The join statement "joins" the execution of the current thread with
	// the execution of some other thread. The other thread is determined
	// by the tread id and the return value of the procedure that it executes.
	// The current thread halts at the join statement until an appropriate
	// thread reached the end of its procedure.
	
	// Here, we join some thread whose thread ID is 23 and whose procedure
	// returns an int value. We assign the returned value to the variable z.
	join 23 assign z;
	
	// The thread that was forked with thread ID 23 and argument 7
	// returns 42
	assert z == 42;
	
	// For the value of g there are three possible cases
	// 1. The thread with ID 77 modified g before the thread with ID 23 has modified g.
	// 2. The thread with ID 77 modified g after the thread with ID 23 has modified g.
	// 2. The thread with ID 77 has not yet modified g.
	assert (g == 5 || g == 6 || g == 3);
	
	// We try to join some thread that has id 23 (and this time we do not assign any 
	// return value). However, at this location there can be never a running thread
	// this this ID.
    join 23;
	
	// The following statement would always fail, however since the execution cannot
	// continue at the preceding join statement this assert statement is not reachable.
    assert (false);
}


procedure foo(n : int) returns(res : int)
modifies g;
{
	if (n >= 7) {
		g := g + 1;
		res := 42;
	} else {
		g := 2 * g;
		res := 0;
	}
}
