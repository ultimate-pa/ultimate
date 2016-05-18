
package jdd.util;

/** simple workframe for XP-like unit-testing */
public class Test {
	public static long total = 0, count = 0;

	public static void start(String module) {
		// truely stupid way of gettting the calles Class name
		Throwable t = new Throwable();
		StackTraceElement [] stack = t.getStackTrace();
		String name = stack[1].getClassName().replace('.', '/');
		JDDConsole.out.print( name );
		for(int i = name.length(); i < 50; i++) JDDConsole.out.print(' ');

		// JDDConsole.out.flush();


		count = 0;
	}

	public static void end() {
		total += count;
		System.out.println("Passed [" + count + "]");
	}

	// --------------------------------------------------------

	public static void check(boolean c) {check(c, null); }

	public static void check(boolean c, String s) {
		count++; // DEBUG
		if(!c) {
			if(s != null) System.err.println("ASSERTATION FAILED: " + s + "     ");
			show_stack_trace();
			System.exit(20);
		}
	}


	// --------------------------------------------------------

	public static void checkEquality(boolean a, boolean b, String s) {
		count++; // DEBUG
		if( a != b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " != " + b + "    ");
			show_stack_trace();

			System.exit(20);
		}
	}

	public static void checkEquality(int a, int b, String s) {
		count++; // DEBUG
		if( a != b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " != " + b + "    ");
			show_stack_trace();
			System.exit(20);
		}
	}

	public static void checkEquality(double a, double b, String s) {
		count++; // DEBUG
		if( a != b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " != " + b + "    ");
			show_stack_trace();
			System.exit(20);
		}
	}

	// --------------------------------------------------------

	public static void checkInequality(int a, int b, String s) {
		count++; // DEBUG
		if( a == b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " == " + b + "    ");
			show_stack_trace();
			System.exit(20);
		}
	}

	// --------------------------------------------------------

	public static void checkLessThan(int a, int b, String s) {
		count++; // DEBUG
		if( a >= b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " >= " + b + "    ");
			show_stack_trace();
			System.exit(20);
		}
	}

	// ----------------------------------------------------
	public static void checkGreaterThan(int a, int b, String s) {
		count++; // DEBUG
		if( a <= b) {
			System.err.print("ASSERTATION FAILED: ");
			if(s != null) System.err.print(s + " ");
			System.err.println(""+ a + " >= " + b + "    ");
			show_stack_trace();
			System.exit(20);
		}
	}

	// ----------------------------------------------------
	private static void show_stack_trace() {
		Thread.dumpStack();
	}
}
