package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences;

import java.io.Serializable;


/**
 * Accumulation of various settings for LassoRanker.
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
	public int num_strict_invariants = 1; // Default: 1
	
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
	public int num_non_strict_invariants = 1; // Default: 1
	
	/**
	 * Only consider non-decreasing invariants.
	 */
	public boolean only_nondecreasing_invariants = false; // Default: false
	
	/**
	 * Should the polyhedra for stem and loop be made integral for integer
	 * programs?
	 */
	public boolean compute_integral_hull = false; // not yet implemented
	
	/**
	 * Are disjunctions allowed in the stem and loop transition?
	 */
	public boolean enable_disjunction = true; // Default: true
	
	public enum UseDivision {
		C_STYLE,    // C style division: x := a / k  -->  k*x <= a < (k+1)*x
		SAFE,       // Safe division: x := a / k can be executed iff k divides a
		RATIONALS_ONLY, // Division is only supported for rational numbers
		DISABLED    // Throw an error if division is used
	}
	
	/**
	 * If and in which manner should division be supported?
	 */
	public final UseDivision use_division = UseDivision.C_STYLE; // Default: C_STYLE
	
	/**
	 * Add annotations to terms for debugging purposes and/or to make use
	 * of unsatisfiable cores
	 */
	public boolean annotate_terms = false; // Default: false
		// Note: currently broken
	
	/**
	 * Try to instantiate the linear template?
	 */
	public boolean use_affine_template = true; // Default: true
	
	/**
	 * Try to instantiate the multiphase template?
	 */
	public boolean use_multiphase_template = true; // Default: true
	
	/**
	 * How many phases in the multiphase template?
	 */
	public int multiphase_template_size = 2; // Default: 3
	
	/**
	 * Try to instantiate the lexicographic template?
	 */
	public boolean use_lex_template = true; // Default: true
	
	/**
	 * How many lexicographic entries in the lexicographic template?
	 */
	public int lex_template_size = 3; // Default: 3
	
	/**
	 * Try to instantiate the piecewise template?
	 */
	public boolean use_piecewise_template = false; // Default: true
	
	/**
	 * How many pieces in the piecewise template?
	 */
	public int piecewise_template_size = 2; // Default: 2
	
	/**
	 * What shell command should be used to call the external smt solver?
	 */
	public String smt_solver_command = "z3 -smt2 -in";
	
	/**
	 * Build a string descriptions of the current preferences
	 */
	public String show() {
		StringBuilder sb = new StringBuilder();
		sb.append("Number of strict supporting invariants: ");
		sb.append(this.num_strict_invariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(this.num_non_strict_invariants);
		sb.append("\nConsider non-deceasing supporting invariants: ");
		sb.append(this.only_nondecreasing_invariants);
		sb.append("\nCompute integeral hull: ");
		sb.append(this.compute_integral_hull);
		sb.append("\nEnable disjunction: ");
		sb.append(this.enable_disjunction);
		sb.append("\nDivision: ");
		sb.append(this.use_division);
		sb.append("\nTerm annotations enables: ");
		sb.append(this.annotate_terms);
		sb.append("\nAffine template enabled: ");
		sb.append(this.use_affine_template);
		sb.append("\nMultiphase template enabled: ");
		sb.append(this.use_multiphase_template);
		sb.append(" (" + this.multiphase_template_size + " phases)");
		sb.append("\nLexicographic template enabled: ");
		sb.append(this.use_lex_template);
		sb.append(" (" + this.lex_template_size + " functions)");
		sb.append("\nPiecewise template enabled: ");
		sb.append(this.use_piecewise_template);
		sb.append(" (" + this.piecewise_template_size + " pieces)");
		sb.append("\nSMT solver command: ");
		sb.append(this.smt_solver_command);
		return sb.toString();
	}
}