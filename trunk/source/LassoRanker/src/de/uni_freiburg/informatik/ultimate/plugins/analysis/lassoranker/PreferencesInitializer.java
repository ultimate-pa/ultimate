package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences;


/**
 * Initializer class for LassoRanker's preferences in Ultimate's GUI
 * 
 * @see Preferences
 * @author Jan Leike
 */
public class PreferencesInitializer extends UltimatePreferenceInitializer {
	/*
	 * Default values for GUI-only preferences
	 */
	public static final boolean s_check_for_nontermination = true;
	public static final boolean s_enable_affine_template = true;
	public static final boolean s_enable_nested_template = true;
	public static final int     s_nested_template_size = 2;
	public static final boolean s_enable_multiphase_template = true;
	public static final int     s_multiphase_template_size = 2;
	public static final boolean s_enable_lex_template = true;
	public static final int     s_lex_template_size = 2;
	public static final boolean s_enable_piecewise_template = true;
	public static final int     s_piecewise_template_size = 2;
	
	/*
	 * Preferences Labels
	 */
	public static final String LABEL_num_strict_invariants =
			"Number of strict supporting invariants";
	public static final String LABEL_num_non_strict_invariants =
			"Number of non-strict supporting invariants";
	public static final String LABEL_only_nondecreasing_invariants =
			"Non-decreasing invariants only";
	public static final String LABEL_compute_integral_hull =
			"Compute integral hull";
	public static final String LABEL_enable_disjunction =
			"Allow disjunctions";
	public static final String LABEL_division_implementation =
			"Division implementation";
	public static final String LABEL_annotate_terms =
			"Add annotations to SMT terms";
	public static final String LABEL_check_for_nontermination =
			"Check for nontermination";
	public static final String LABEL_nontermination_check_nonlinear =
			"Nonlinear SMT query for nontermination check";
	public static final String LABEL_termination_check_nonlinear =
			"Nonlinear SMT query for termination check";
	public static final String LABEL_enable_affine_template =
			"Affine template";
	public static final String LABEL_enable_nested_template =
			"Nested template";
	public static final String LABEL_nested_template_size =
			"Nested template size";
	public static final String LABEL_enable_multiphase_template =
			"Multiphase template";
	public static final String LABEL_multiphase_template_size =
			"Multiphase template size";
	public static final String LABEL_enable_lex_template =
			"Lexicographic template";
	public static final String LABEL_lex_template_size =
			"Lexicographic template size";
	public static final String LABEL_enable_piecewise_template =
			"Piecewise template";
	public static final String LABEL_piecewise_template_size =
			"Piecewise template size";
	public static final String LABEL_use_external_solver =
			"Use external SMT solver";
	public static final String LABEL_smt_solver_command =
			"SMT solver command";
	
	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		Preferences preferences = new Preferences(); // Get default preferences
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Integer>(
						LABEL_num_strict_invariants,
						preferences.num_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_num_non_strict_invariants,
						preferences.num_non_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_only_nondecreasing_invariants,
						preferences.only_nondecreasing_invariants,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_compute_integral_hull,
						preferences.compute_integral_hull,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_disjunction,
						preferences.enable_disjunction,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_annotate_terms,
						preferences.annotate_terms,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_check_for_nontermination,
						s_check_for_nontermination,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_nontermination_check_nonlinear,
						preferences.nontermination_check_nonlinear,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_termination_check_nonlinear,
						preferences.termination_check_nonlinear,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_affine_template,
						s_enable_affine_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_nested_template,
						s_enable_nested_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_nested_template_size,
						s_nested_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_multiphase_template,
						s_enable_multiphase_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_multiphase_template_size,
						s_multiphase_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_lex_template,
						s_enable_lex_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_lex_template_size,
						s_lex_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_piecewise_template,
						s_enable_piecewise_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_piecewise_template_size,
						s_piecewise_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_external_solver,
						true,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(
						LABEL_smt_solver_command,
						preferences.smt_solver_command,
						PreferenceType.String),
		};
	}
	
	/**
	 * @return the preferences currently set in the GUI
	 */
	public static Preferences getGuiPreferences() {
		// Get default preferences
		Preferences preferences = new Preferences();
		
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		preferences.num_strict_invariants = store.getInt(
				LABEL_num_strict_invariants
		);
		preferences.num_non_strict_invariants = store.getInt(
				LABEL_num_non_strict_invariants
		);
		preferences.only_nondecreasing_invariants = store.getBoolean(
				LABEL_only_nondecreasing_invariants
		);
		preferences.compute_integral_hull = store.getBoolean(
				LABEL_compute_integral_hull
		);
		preferences.enable_disjunction = store.getBoolean(
				LABEL_enable_disjunction
		);
		preferences.annotate_terms = store.getBoolean(
				LABEL_annotate_terms
		);
		preferences.nontermination_check_nonlinear = store.getBoolean(
				LABEL_nontermination_check_nonlinear
		);
		preferences.externalSolver = store.getBoolean(
				LABEL_use_external_solver
		);
		preferences.smt_solver_command = store.getString(
				LABEL_smt_solver_command
		);
		return preferences;
	}
	
	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}
	
	@Override
	public String getPreferencePageTitle() {
		return "LassoRanker";
	}
}