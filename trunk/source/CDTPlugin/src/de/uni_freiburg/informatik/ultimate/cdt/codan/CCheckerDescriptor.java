/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

/**
 * Externalized Strings which are used in the checker, basically
 * for the preferences.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 20.03.2012
 */
public interface CCheckerDescriptor {
	
	/**
	 * The Problem-Identifier for found Counterexamples.
	 */
	public static String CE_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.CounterExampleResult";

	/**
	 * The Problem-Identifier for found Invariants.
	 */
	public static String IN_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.InvariantResult";

	/**
	 * The Problem-Identifier for unproveable results.
	 */
	public static String UN_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.UnproveableResult";

	/**
	 * The Problem-Identifier for positive results;
	 */
	public static String POS_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.PositiveResult";
	
	/**
	 * The Problem-Identifier for syntax error results;
	 */
	public static String SYNERR_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.SyntaxErrorResult";
	
	/**
	 * The Problem-Identifier for time outs;
	 */
	public static String TIMEOUT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.TimeoutResult";
	
	/**
	 * The Problem-Identifier for the generic info result;
	 */
	public static String GENERIC_INFO_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericInfoResult";
	
	/**
	 * The Problem-Identifier for the generic warning result;
	 */
	public static String GENERIC_WARNING_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericWarningResult";
	
	/**
	 * The Problem-Identifier for the generic error result;
	 */
	public static String GENERIC_ERROR_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericErrorResult";
	
	/**
	 * Key for the Selection of Toolchains.
	 */
	public static String MAP_KEY = "TOOLCHAIN_SELECTION";
	/**
	 * Label Text for the Selection of Toolchains.
	 */
	public static String MAP_LABEL = "Please select one of the predefined toolchains";
}
