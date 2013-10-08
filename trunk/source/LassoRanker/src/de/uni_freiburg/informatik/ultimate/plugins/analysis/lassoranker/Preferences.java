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
	public static int num_strict_invariants = 0; // Default: 1
	
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
	public static int num_non_strict_invariants = 0; // Default: 1
	
	/**
	 * Only consider non-decreasing invariants.
	 */
	public static boolean nondecreasing_invariants = false; // Default: false
	
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
		RATIONALS_ONLY, // Division is only supported for rational numbers
		DISABLED    // Throw an error if division is used
	}
	
	/**
	 * If and in which manner should division be supported?
	 */
	public static UseDivision use_division = UseDivision.C_STYLE; // Default: C_STYLE
	
	/**
	 * Add annotations to terms for debugging purposes and/or to make use
	 * of unsatisfiable cores
	 */
	public static boolean annotate_terms = false; // Default: false
		// Note: currently broken
	
	/**
	 * Try to instantiate the linear template?
	 */
	public static final boolean use_affine_template = true; // Default: true
	
	/**
	 * Try to instantiate the multiphase template?
	 */
	public static final boolean use_multiphase_template = true; // Default: true
	
	/**
	 * How many phases in the multiphase template?
	 */
	public static final int multiphase_template_phases = 2; // Default: 3
	
	/**
	 * Try to instantiate the lexicographic template?
	 */
	public static final boolean use_lex_template = true; // Default: true
	
	/**
	 * How many lexicographic entries in the lexicographic template?
	 */
	public static final int lex_template_functions = 3; // Default: 3
	
	/**
	 * Try to instantiate the piecewise template?
	 */
	public static final boolean use_piecewise_template = true; // Default: true
	
	/**
	 * How many pieces in the piecewise template?
	 */
	public static final int piecewise_template_pieces = 2; // Default: 2
	
	/**
	 * Build a string descriptions of the current preferences
	 */
	public static String show() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of strict supporting invariants: ");
		sb.append(Preferences.num_strict_invariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(Preferences.num_non_strict_invariants);
		sb.append("\nConsider non-deceasing supporting invariants: ");
		sb.append(Preferences.nondecreasing_invariants);
		sb.append("\nCompute integeral hull: ");
		sb.append(Preferences.compute_integral_hull);
		sb.append("\nEnable disjunction: ");
		sb.append(Preferences.enable_disjunction);
		sb.append("\nDivision: ");
		sb.append(Preferences.use_division);
		sb.append("\nTerm annotations enables: ");
		sb.append(Preferences.annotate_terms);
		sb.append("\nAffine template enabled: ");
		sb.append(Preferences.use_affine_template);
		sb.append("\nMultiphase template enabled: ");
		sb.append(Preferences.use_multiphase_template);
		sb.append(" (" + Preferences.multiphase_template_phases + " phases)");
		sb.append("\nLexicographic template enabled: ");
		sb.append(Preferences.use_lex_template);
		sb.append(" (" + Preferences.lex_template_functions + " functions)");
		sb.append("\nPiecewise template enabled: ");
		sb.append(Preferences.use_piecewise_template);
		sb.append(" (" + Preferences.piecewise_template_pieces + " pieces)");
		return sb.toString();
	}
}