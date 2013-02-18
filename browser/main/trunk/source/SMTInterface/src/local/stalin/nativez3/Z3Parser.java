package local.stalin.nativez3;

import local.stalin.logic.Formula;

public class Z3Parser {

	private static native void initIDs();
	
	static {
		String osname = System.getProperty("os.name");
		String z3libname = osname.contains("Windows") ? "z3" : "z3-gmp";
		System.loadLibrary(z3libname);
		System.loadLibrary("nativez3");
		initIDs();
	}
	
	/**
	 * Storage for native parser content.
	 */
	@SuppressWarnings("unused")
	private long nativestore;
	
	// Memory management
	private native void init(long np) throws NativeCodeException;
	private native void deinit();
	// Ast creation and assertion
	private native void assertast(Formula ass) throws Z3Exception,NativeCodeException;

	/**
	 * Create a Z3Parser backed by a Z3 native store.
	 * @param ctx Native Store.
	 * @throws Z3Exception Z3 reported an exception.
	 * @throws NativeCodeException Memory allocation failed in native code.
	 */
	Z3Parser(Z3Context ctx) throws Z3Exception,NativeCodeException {
		init(ctx.nativestore);
	}
	
	// TODO: do we really want this function?
	/* After calling this function, native code has no knowledge about sorts and functions,
	 * but native context still has. Also parser still knows about function and sorts...
	 */
	public void finished() {
		deinit();
	}
	
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		deinit();
	}
	
	public void addAssumption(Formula ass) throws Z3Exception, NativeCodeException {
		assert(ass.typeCheck());
		assertast(ass);
	}
}
