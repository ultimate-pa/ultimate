package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

/**
 * Accumulation of various settings for the Ranking Functions Plugin.
 * TODO: move this into a preferences page
 * 
 * @author Jan Leike
 */
public class Preferences {
	
	/**
	 * If this is disabled, no supporting invariants will be created.
	 * This is probably only useful to reduce the size of the debug output.
	 */
	public static boolean add_supporting_invariants = true; // Default: true
	
	/**
	 * Should the lower bound of a ranking function be augmented by a
	 * supporting invariant?  This is only useful if supporting invariants may
	 * be not non-decreasing.
	 */
	public static boolean supporting_invariant_for_lower_bound = false; // Default: false
	
	/**
	 * Check if the loop execution is impossible, i.e. the loop
	 * condition contradicts the post condition of the stem?
	 */
	public static boolean check_if_loop_impossible = true; // Default: true
	
	/**
	 * Search for inductive invariants that may not be non-decreasing?
	 * Setting this option to true requires a non-linear SMT solver.
	 * (Currently z3 is the only supported solver that handles non-linear
	 * arithmetic.)
	 */
	public static boolean not_nondecreasing = false; // Default: false
	
	public enum UseVariableDomain {
		INTEGERS,
		REALS,
		AUTO_DETECT
	}
	
	/**
	 * Should the program variables be treated as integer-valued or real-valued?
	 * If set to 'auto-detect', the type will automatically be inferred from the
	 * supplied source code.
	 */
	public static UseVariableDomain use_variable_domain =
			UseVariableDomain.AUTO_DETECT; // Default: AUTO_DETECT;
	
	/**
	 * Should the polyhedra for stem and loop be made integral for integer
	 * programs?
	 */
	public static boolean compute_integral_hull = false; // Default: true
	
	/**
	 * Should the Ranking Functions Plugin create its own SMT solver
	 * instance?
	 */
	public static boolean use_new_script = true; // Default: true
	
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
	
	public static String show() {
		StringBuilder sb = new StringBuilder();
		sb.append("Add supporting invariants: ");
		sb.append(Preferences.add_supporting_invariants);
		sb.append("\nSupporting invariant for lower bound: ");
		sb.append(Preferences.supporting_invariant_for_lower_bound);
		sb.append("\nCheck if loop impossible: ");
		sb.append(Preferences.check_if_loop_impossible);
		sb.append("\nSupporting invariant can be not non-decreasing: ");
		sb.append(Preferences.not_nondecreasing);
		sb.append("\nVariable domain: ");
		sb.append(Preferences.use_variable_domain);
		sb.append("\nCompute integeral hull: ");
		sb.append(Preferences.compute_integral_hull);
		sb.append("\nUse new SMT script: ");
		sb.append(Preferences.use_new_script);
		sb.append("\nEnable disjunction: ");
		sb.append(Preferences.enable_disjunction);
		sb.append("\nDivision: ");
		sb.append(Preferences.use_division);
		sb.append("\nLinear template enabled: ");
		sb.append(Preferences.use_linear_template);
		sb.append("\nMultiphase template enabled: ");
		sb.append(Preferences.use_multiphase_template);
		return sb.toString();
	}
}