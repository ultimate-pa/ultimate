package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.Serializable;


/**
 * Accumulation of various settings for LassoRanker.
 * TODO: move this into a preferences page
 * 
 * @author Jan Leike
 */
public class Preferences implements Serializable {
	private static final long serialVersionUID = 3253589986886574198L;

	/**
	 * Check if the loop execution is impossible, i.e. the loop
	 * condition contradicts the post condition of the stem
	 */
	public static boolean check_if_loop_infeasible = true; // Default: true
	
	/**
	 * Number of strict supporting invariants for each Motzkin transformation.
	 * Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c > 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see num_non_strict_invariants
	 */
	public static int num_strict_invariants = 1; // Default: 1
	
	/**
	 * Number of non-strict supporting invariants for each Motzkin
	 * transformation.  Strict supporting invariants are invariants of the form
	 * <pre>Σ c_i x_i + c ≥ 0.</pre>
	 * 
	 * The value must be non-negative; set to 0 to disable the use of strict
	 * supporting invariants.  Note that increasing this number will
	 * dramatically increase runtime!
	 * 
	 * @see num_strict_invariants
	 */
	public static int num_non_strict_invariants = 1; // Default: 1
	
	/**
	 * Only consider non-decreasing invariants.
	 */
	public static boolean nondecreasing_invariants = false; // Default: false
	
	public enum VariableDomain {
		INTEGERS,
		REALS,
		AUTO_DETECT
	}
	
	/**
	 * Should the program variables be treated as integer-valued or real-valued?
	 * If set to 'auto-detect', the type will automatically be inferred from the
	 * supplied source code.
	 */
	public static VariableDomain use_variable_domain =
			VariableDomain.AUTO_DETECT; // Default: AUTO_DETECT;
	
	/**
	 * Should the polyhedra for stem and loop be made integral for integer
	 * programs?
	 */
	public static boolean compute_integral_hull = false; // not yet implemented
	
	/**
	 * Are disjunctions allowed in the stem and loop transition?
	 */
	public static boolean enable_disjunction = true; // Default: true
	
	public enum UseDivision {
		C_STYLE,    // C style division: x := a / k  -->  k*x <= a < (k+1)*x
		SAFE,       // Safe division: x := a / k can be executed iff k divides a
		RATIONALS_ONLY, // Division is only supported for Rationals
		DISABLED    // Throw an error if division is used
	}
	
	/**
	 * If and in which manner should division be supported?
	 */
	public static UseDivision use_division = UseDivision.SAFE; // Default: C_STYLE
	
	/**
	 * Try to instantiate the linear template?
	 */
	public static final boolean use_linear_template = true; // Default: true
	
	/**
	 * Try to instantiate the multiphase template?
	 */
	public static final boolean use_multiphase_template = false; // Default: true
	
	/**
	 * Rewrite occurences of booleans in the stem and loop with inequalities
	 */
	public static boolean rewrite_booleans = true; // Default: false
	
	/**
	 * Add annotations to terms for debugging purposes and/or to make use
	 * of unsatisfiable cores
	 */
	public static boolean annotate_terms = false; // Default: false
	
	/**
	 * Build a string descriptions of the current preferences
	 */
	public static String show() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of strict supporting invariants: ");
		sb.append(Preferences.num_strict_invariants);
		sb.append("Number of non-strict supporting invariants: ");
		sb.append(Preferences.num_non_strict_invariants);
		sb.append("\nCheck if loop is infeasible: ");
		sb.append(Preferences.check_if_loop_infeasible);
		sb.append("\nConsider non-deceasing supporting invariants: ");
		sb.append(Preferences.nondecreasing_invariants);
		sb.append("\nVariable domain: ");
		sb.append(Preferences.use_variable_domain);
		sb.append("\nCompute integeral hull: ");
		sb.append(Preferences.compute_integral_hull);
		sb.append("\nEnable disjunction: ");
		sb.append(Preferences.enable_disjunction);
		sb.append("\nDivision: ");
		sb.append(Preferences.use_division);
		sb.append("\nLinear template enabled: ");
		sb.append(Preferences.use_linear_template);
		sb.append("\nMultiphase template enabled: ");
		sb.append(Preferences.use_multiphase_template);
		sb.append("\nRewrite booleans enabled: ");
		sb.append(Preferences.rewrite_booleans);
		sb.append("\nTerm annotations enables: ");
		sb.append(Preferences.annotate_terms);
		return sb.toString();
	}
}