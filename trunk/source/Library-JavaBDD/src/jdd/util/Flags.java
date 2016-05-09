
package jdd.util;


/**
 * abstraction of flags.
 * <p>
 * The Flag object allows you to store and access 32 distinct flags
 */

public class Flags {
	private int flags;

	/** create a Flag object with the given value */

	public Flags(int f) {
		this.flags = f;
	}

	/** create an empty Flag object  */
	public Flags() {
		this(0);
	}

	// --------------------------------
	/** set the 32-bit flags variable in one operation */
	protected void setAll(int f) {
		flags = f;
	}

	/** get all the 32 flags variable in one operation */
	public int getAll() {
		return flags;
	}

	/** copy FROM the <tt>f</tt> object */
	public void copyFlags(final Flags f) {
		this.flags = f.flags;
	}

	// --------------------------------
	/** set the flag <tt>flag</tt> */
	private void set(int flag) {
		flags |= (1 << flag);
	}

	/** clear/reset the flag <tt>flag</tt> */
	private void reset(int flag) {
		flags &= ~(1 << flag);
	}

	/** set the flag <tt>flag</tt> to <tt>set</tt> */
	public void set(int f, boolean set) {
		if(set) set(f);
		else		reset(f);
	}

	/** get the value of <tt>flag</tt> */
	public boolean get(int flag) {
		return (flags & (1<< flag) ) != 0;
	}


	// ------------------------------------------------------
	/** internal test. do not call */
	public static void internal_test() {
		Test.start("Flags");

		Flags f = new Flags();

		f.set(0, true);
		f.set(1, true);
		f.set(1, false);
		f.set(2, true);
		Test.checkEquality( f.get(0), true, "get (1)");
		Test.checkEquality( f.get(1), false, "get (2)");
		Test.checkEquality( f.get(2), true, "get (3)");

		f.setAll(0);
		for(int i = 0; i < 32; i++) Test.checkEquality( f.get(i), false, "get FALSE (i)");

		f.setAll(-1);
		for(int i = 0; i < 32; i++) Test.checkEquality( f.get(i), true, "get TRUE (i)");

		Test.end();
	}
}