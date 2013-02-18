package local.stalin.nativez3;

/**
 * A wrapper around the C structure <code>Z3_config</code>. Instances of this
 * class are only used until they are passed to the constructor of class 
 * {@link Z3Context} Z3Context.
 * @author Juergen Christ
 */
public class Z3Config {
	
	/**
	 * Storage for native Z3_config
	 */
	long nativestore;
	
	private static native void initIDs();
	
	static {
		String osname = System.getProperty("os.name");
		String z3libname = osname.contains("Windows") ? "z3" : "z3-gmp";
		System.loadLibrary(z3libname);
		System.loadLibrary("nativez3");
		initIDs();
	}
	
	public Z3Config() throws Z3Exception {
		initialize();
	}
	
	/**
	 * Creates a Z3_config structure.
	 */
	private native void initialize() throws Z3Exception;
	
	/**
	 * Deletes a Z3_config structure. After calling this method, the 
	 * configuration is not usable anymore. This method is implicitly called
	 * by {@link #finalize()}finalize.
	 */
	public native void deinitialize();
	
	/**
	 * Registers a configuration value in this context. See z3 -ini? 
	 * (or z3 /ini?) for configuration parameters.
	 * @param config Configuration parameter.
	 * @param value  Configuration value.
	 */
	public native void setConfig(String config,String value) throws Z3Exception;
	
	/**
	 * Deinitializes this configuration.
	 */
	@Override
	protected void finalize() throws Throwable {
		super.finalize();
		deinitialize();
	}
	
	/**
	 * Default Configuration for model generation and Proof Production
	 * @author Juergen Christ
	 */
	public static final class Z3ConfigModelProof extends Z3Config {
		public Z3ConfigModelProof() throws Z3Exception {
			setConfig("MODEL","true");
			setConfig("PROOF_MODE","2");
			setConfig("MODEL_PARTIAL","true");
		}
	}
	
	/**
	 * Default Configuration for model generation.
	 * @author Juergen Christ
	 */
	public static final class Z3ConfigModel extends Z3Config {
		public Z3ConfigModel() throws Z3Exception {
			setConfig("MODEL","true");
			setConfig("MODEL_PARTIAL","true");
		}
	}

	/**
	 * Default Configuration for Proof Production.
	 * @author Juergen Christ
	 */
	public static final class Z3ConfigProof extends Z3Config {
		public Z3ConfigProof() throws Z3Exception {
			setConfig("PROOF_MODE","2");
		}
	}
	
}
