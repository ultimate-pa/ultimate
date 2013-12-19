package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.Preferences.DivisionImplementation;


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
	public static final boolean s_enable_multiphase_template = true;
	public static final int     s_multiphase_template_size = 2;
	public static final boolean s_enable_lex_template = true;
	public static final int     s_lex_template_size = 2;
	public static final boolean s_enable_piecewise_template = false; // FIXME: broken
	public static final int     s_piecewise_template_size = 2;
	
	/*
	 * Preferences Labels
	 */
	public static final String LABEL_num_strict_invariants =
			"Number of strict supporting invariants for each Motzkin " +
			"transformation.";
	public static final String LABEL_num_non_strict_invariants =
			"Number of non-strict supporting invariants for each Motzkin " +
			"transformation.";
	public static final String LABEL_only_nondecreasing_invariants =
			"Only use non-decreasing invariants.";
	public static final String LABEL_compute_integral_hull =
			"Compute integral hull?";
	public static final String LABEL_enable_disjunction =
			"Allow disjunctions?";
	public static final String LABEL_division_implementation =
			"How should division be handled?";
	public static final String LABEL_annotate_terms =
			"Add annotations to SMT terms?";
	public static final String LABEL_check_for_nontermination =
			"Check for nontermination?";
	public static final String LABEL_nontermination_check_nonlinear =
			"Use nonlinear SMT query for nontermination check?";
	public static final String LABEL_enable_affine_template =
			"Use the affine template?";
	public static final String LABEL_enable_multiphase_template =
			"Use the multiphase template?";
	public static final String LABEL_multiphase_template_size =
			"Number of phases in the multiphase template";
	public static final String LABEL_enable_lex_template =
			"Use the lexicographic template?";
	public static final String LABEL_lex_template_size =
			"Number of components in the lexicographic template";
	public static final String LABEL_enable_piecewise_template =
			"Use the piecewise template?";
	public static final String LABEL_piecewise_template_size =
			"Number of pieces in the piecewise template";
	public static final String LABEL_smt_solver_command =
			"Shell command to the external smt solver";
	
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
				new UltimatePreferenceItem<DivisionImplementation>(
						LABEL_division_implementation,
						preferences.division_implementation,
						PreferenceType.Combo,
						DivisionImplementation.values()),
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
						LABEL_enable_affine_template,
						s_enable_affine_template,
						PreferenceType.Boolean),
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
				new UltimatePreferenceItem<String>(
						LABEL_smt_solver_command,
						preferences.smt_solver_command,
						PreferenceType.String),
		};
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