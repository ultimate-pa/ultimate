package local.stalin.nativez3;

import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.Theory;

/**
 * Class Representing a Z3_context structure.
 * @author Juergen Christ
 */
public class Z3Context {

	private static native void initIDs();
	
	static {
		String osname = System.getProperty("os.name");
		String z3libname = osname.contains("Windows") ? "z3" : "z3-gmp";
		System.loadLibrary(z3libname);
		System.loadLibrary("nativez3");
		initIDs();
	}
	
	/*
	 * Result types according to Z3_lbool
	 */
	public static final int Z3UNSAT = -1;
	public static final int Z3UNKNOWN = 0;
	public static final int Z3SAT = 1;
	
	private static final String[] resultstrings = {
		"unsat", "unknown", "sat"
	};
	
	public static final String resultToString(int result) {
		return resultstrings[result+1];
	}
	
	/*
	 * Search failures according to Z3_search_failure
	 */
	public static final int Z3_ERR_NO_FAILURE = 0;
	public static final int Z3_ERR_UNKNOWN = 1;
	public static final int Z3_ERR_TIMEOUT = 2;
	public static final int Z3_ERR_MEMOUT_WATERMARK = 3;
	public static final int Z3_ERR_CANCELED = 4;
	public static final int Z3_ERR_NUM_CONFLICTS = 5;
	public static final int Z3_ERR_THEORY = 6;
	public static final int Z3_ERR_QUANTIFIERS = 7;
	
	private static final String[] failurestrings = {
		"No Failure",
		"Undocumented Failure",
		"Timeout occured",
		"Hit memory high-watermak limit",
		"External cancelation",
		"Maximum number of conflicts",
		"Incomplete Theory used",
		"Quantifies in context"
	};
	
	private int mlastfailure;
	
	/**
	 * Storage for native Z3_context
	 */
	long nativestore;
	private Theory mtheory;
	private Z3ProofRule mproof;
	private Z3Parser mparser;
	
	private native void initZ3(long cfg) throws Z3Exception;
	private native void deinitializeZ3();
	
	public Z3Context(Z3Config cfg,Theory theory) throws Z3Exception {
		initZ3(cfg.nativestore);
		mtheory = theory;
		mlastfailure = Z3_ERR_NO_FAILURE;
	}
	
	public Theory getTheory() {
		return mtheory;
	}

	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		deinitializeZ3();
	}
	
	public native void push() throws Z3Exception;
	public native void pop(int numpops) throws Z3Exception;
	/**
	 * Check whether the current logical context is satisfiable
	 * @return <code>Z3UNSAT</code>, <code>Z3UNKNOWN</code> or <code>Z3SAT</code>
	 * @throws Z3Exception 
	 * 
	 */
	public native int check() throws Z3Exception;
	private native int checkGetProof(Theory theory) throws Z3Exception;
	private native int checkGetSkolemsInsts(Theory t,Set<Formula> s,
			Set<Formula> i) throws Z3Exception;
	/**
	 * This function assumes, proof generation is enabled.
	 * @return <code>Z3UNSAT</code>, <code>Z3UNKNOWN</code> or <code>Z3SAT</code>
	 * @throws Z3Exception
	 */
	public int checkAndGetProof() throws Z3Exception {
		return checkGetProof(mtheory);
	}
	
	public int checkAndGetSkolemsInsts(Set<Formula> skolems,
			Set<Formula> insts) throws Z3Exception {
		return checkGetSkolemsInsts(mtheory, skolems, insts);
	}
	
	/**
	 * Cancel an ongoing check by setting a soft cancelation flag. This method 
	 * should be called by a thread different than the one invoking 
	 * {@link #check()}check.
	 */
	public native void cancelCheck();
	
	public int getLastFailure() {
		return mlastfailure;
	}
	
	public String getLastFailureDescription() {
		return failurestrings[mlastfailure];
	}
	
	public Z3ProofRule getProof() {
		return mproof;
	}
	
	public void clearProof() {
		mproof = null;
	}
	
	public Z3Parser getParser() throws Z3Exception, NativeCodeException {
		if( mparser == null )
			mparser = new Z3Parser(this);
		return mparser;
	}
}
