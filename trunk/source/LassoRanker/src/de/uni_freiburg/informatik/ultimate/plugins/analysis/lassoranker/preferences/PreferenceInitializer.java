package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preferences.Preferences.UseDivision;

public class PreferenceInitializer extends UltimatePreferenceInitializer {
	
	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		Preferences pref = new Preferences();
		
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Integer>(
						LABEL_num_strict_invariants,
						pref.num_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_num_non_strict_invariants,
						pref.num_non_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_only_nondecreasing_invariants,
						pref.only_nondecreasing_invariants,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_compute_integral_hull,
						pref.compute_integral_hull,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_disjunction,
						pref.enable_disjunction,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<UseDivision>(
						LABEL_use_division,
						pref.use_division,
						PreferenceType.Combo,
						UseDivision.values()),
				new UltimatePreferenceItem<Boolean>(
						LABEL_annotate_terms,
						pref.annotate_terms,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_affine_template,
						pref.use_affine_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_multiphase_template,
						pref.use_multiphase_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_multiphase_template_size,
						pref.multiphase_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_lex_template,
						pref.use_lex_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_lex_template_size,
						pref.lex_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_piecewise_template,
						pref.use_piecewise_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_piecewise_template_size,
						pref.piecewise_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<String>(
						LABEL_smt_solver_command,
						pref.smt_solver_command,
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
			"Should the polyhedra for stem and loop be made integral for " +
			"integer programs?";
	public static final String LABEL_enable_disjunction =
			"Are disjunctions allowed in the stem and loop transition?";
	public static final String LABEL_use_division =
			"How should division be handled?";
	public static final String LABEL_annotate_terms =
			"Add annotations to SMT terms?";
	public static final String LABEL_use_affine_template =
			"Use the affine template?";
	public static final String LABEL_use_multiphase_template =
			"Use the multiphase template?";
	public static final String LABEL_multiphase_template_size =
			"Number of phases in the multiphase template";
	public static final String LABEL_use_lex_template =
			"Use the lexicographic template?";
	public static final String LABEL_lex_template_size =
			"Number of components in the lexicographic template";
	public static final String LABEL_use_piecewise_template =
			"Use the piecewise template?";
	public static final String LABEL_piecewise_template_size =
			"Number of pieces in the piecewise template";
	public static final String LABEL_smt_solver_command =
			"Shell command to the external smt solver";
}