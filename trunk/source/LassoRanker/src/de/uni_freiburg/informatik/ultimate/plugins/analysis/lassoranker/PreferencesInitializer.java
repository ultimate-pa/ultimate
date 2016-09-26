/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker plug-in.
 *
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.DefaultLassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;

/**
 * Initializer class for LassoRanker's preferences in Ultimate's GUI
 *
 * @see LassoRankerPreferences
 * @author Jan Leike
 */
public class PreferencesInitializer extends UltimatePreferenceInitializer {

	public PreferencesInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	/*
	 * Default values for GUI-only preferences
	 */
	public static final boolean s_simplify_result = true;
	public static final boolean s_enable_affine_template = true;
	public static final boolean s_enable_nested_template = true;
	public static final int s_nested_template_size = 4;
	public static final boolean s_enable_multiphase_template = true;
	public static final int s_multiphase_template_size = 2;
	public static final boolean s_enable_lex_template = true;
	public static final int s_lex_template_size = 2;
	public static final boolean s_enable_piecewise_template = true;
	public static final int s_piecewise_template_size = 2;
	public static final boolean s_enable_parallel_template = true;
	public static final int s_multilex_template_size = 2;
	public static final boolean s_enable_multilex_template = false;
	public static final int s_parallel_template_size = 2;

	/*
	 * Preferences Labels
	 */
	public static final String LABEL_enable_partitioneer = "Enable LassoPartitioneer";
	public static final String LABEL_nontermination_analysis = "Nontermination analysis";
	public static final String LABEL_nontermination_number_gevs = "Number of generalized eigenvectors";
	public static final String LABEL_nontermination_nilpotent_components = "Allow nilpotent components";
	public static final String LABEL_nontermination_bounded_executions = "Allow bounded nonterminating executions";
	public static final String LABEL_termination_analysis = "Termination analysis";
	public static final String LABEL_numstrict_invariants = "Number of strict supporting invariants";
	public static final String LABEL_numnon_strict_invariants = "Number of non-strict supporting invariants";
	public static final String LABEL_nondecreasing_invariants = "Only non-decreasing invariants";
	public static final String LABEL_compute_integral_hull = "Compute integral hull";
	public static final String LABEL_annotate_terms = "Add annotations to SMT terms";
	public static final String LABEL_simplify_result = "Simplify discovered termination arguments";
	public static final String LABEL_enable_affine_template = "Affine template";
	public static final String LABEL_enable_nested_template = "Nested template";
	public static final String LABEL_nested_template_size = "Nested template size";
	public static final String LABEL_enable_multiphase_template = "Multiphase template";
	public static final String LABEL_multiphase_template_size = "Multiphase template size";
	public static final String LABEL_enable_lex_template = "Lexicographic template";
	public static final String LABEL_lex_template_size = "Lexicographic template size";
	public static final String LABEL_enable_piecewise_template = "Piecewise template";
	public static final String LABEL_piecewise_template_size = "Piecewise template size";
	public static final String LABEL_enable_parallel_template = "Parallel template";
	public static final String LABEL_parallel_template_size = "Parallel template size";
	public static final String LABEL_enable_multilex_template = "Multilex template";
	public static final String LABEL_multilex_template_size = "Multilex template size";
	public static final String LABEL_use_external_solver = "Use external SMT solver";
	public static final String LABEL_smt_solver_command = "SMT solver command";
	public static final String LABEL_dump_smt_script = "Dump SMT script to file";
	public static final String LABEL_path_of_dumped_script = "Path of dumped script";

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		// Get default preferences and settings
		final LassoRankerPreferences preferences = new LassoRankerPreferences();
		final TerminationAnalysisSettings termination_settings = new TerminationAnalysisSettings();
		final NonTerminationAnalysisSettings nontermination_settings = new NonTerminationAnalysisSettings();
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_enable_partitioneer, preferences.isEnablePartitioneer(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_nontermination_analysis, nontermination_settings.analysis,
						PreferenceType.Combo, AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_nontermination_number_gevs, nontermination_settings.number_of_gevs,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_nontermination_nilpotent_components,
						nontermination_settings.nilpotent_components, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_nontermination_bounded_executions,
						nontermination_settings.allowBounded, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_termination_analysis, termination_settings.analysis,
						PreferenceType.Combo, AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_numstrict_invariants, termination_settings.numstrict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_numnon_strict_invariants,
						termination_settings.numnon_strict_invariants, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_nondecreasing_invariants,
						termination_settings.nondecreasing_invariants, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_compute_integral_hull, preferences.isComputeIntegralHull(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_annotate_terms, preferences.isAnnotateTerms(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_simplify_result, s_simplify_result, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_enable_affine_template, s_enable_affine_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_enable_nested_template, s_enable_nested_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_nested_template_size, s_nested_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_enable_multiphase_template, s_enable_multiphase_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_multiphase_template_size, s_multiphase_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_enable_lex_template, s_enable_lex_template, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_lex_template_size, s_lex_template_size, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_enable_piecewise_template, s_enable_piecewise_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_piecewise_template_size, s_piecewise_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_enable_parallel_template, s_enable_parallel_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_parallel_template_size, s_parallel_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_enable_multilex_template, s_enable_multilex_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_multilex_template_size, s_multilex_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_use_external_solver, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_smt_solver_command, preferences.getExternalSolverCommand(),
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_dump_smt_script, preferences.isDumpSmtSolverScript(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_path_of_dumped_script, preferences.getPathOfDumpedScript(),
						PreferenceType.String) };
	}

	/**
	 * @return the (global) LassoRanker preferences from the GUI
	 */
	public static LassoRankerPreferences getLassoRankerPreferences(final IUltimateServiceProvider services) {
		final IPreferenceProvider store = services.getPreferenceProvider(Activator.PLUGIN_ID);
		// create new preferences
		return new LassoRankerPreferences(new DefaultLassoRankerPreferences() {
			@Override
			public boolean isEnablePartitioneer() {
				return store.getBoolean(LABEL_enable_partitioneer);
			}

			@Override
			public boolean isComputeIntegralHull() {
				return store.getBoolean(LABEL_compute_integral_hull);
			}

			@Override
			public boolean isAnnotateTerms() {
				return store.getBoolean(LABEL_annotate_terms);
			}

			@Override
			public boolean isDumpSmtSolverScript() {
				return store.getBoolean(LABEL_dump_smt_script);
			}

			@Override
			public boolean isExternalSolver() {
				return store.getBoolean(LABEL_use_external_solver);
			}

			@Override
			public String getExternalSolverCommand() {
				return store.getString(LABEL_smt_solver_command);
			}

			@Override
			public String getPathOfDumpedScript() {
				return store.getString(LABEL_path_of_dumped_script);
			}
		});
	}

	/**
	 * @return the (local) termination analysis settings from the GUI
	 */
	public static TerminationAnalysisSettings getTerminationAnalysisSettings(final IUltimateServiceProvider services) {
		// Get default preferences
		final TerminationAnalysisSettings settings = new TerminationAnalysisSettings();

		final IPreferenceProvider store = services.getPreferenceProvider(Activator.PLUGIN_ID);
		settings.analysis = store.getEnum(LABEL_termination_analysis, AnalysisType.class);
		settings.numstrict_invariants = store.getInt(LABEL_numstrict_invariants);
		settings.numnon_strict_invariants = store.getInt(LABEL_numnon_strict_invariants);
		settings.nondecreasing_invariants = store.getBoolean(LABEL_nondecreasing_invariants);
		settings.simplify_termination_argument = store.getBoolean(LABEL_simplify_result);
		settings.simplify_supporting_invariants = store.getBoolean(LABEL_simplify_result);
		return settings;
	}

	/**
	 * @return the (local) nontermination analysis settings from the GUI
	 */
	public static NonTerminationAnalysisSettings
			getNonTerminationAnalysisSettings(final IUltimateServiceProvider services) {
		// Get default preferences
		final NonTerminationAnalysisSettings settings = new NonTerminationAnalysisSettings();

		final IPreferenceProvider store = services.getPreferenceProvider(Activator.PLUGIN_ID);
		settings.analysis = store.getEnum(LABEL_nontermination_analysis, AnalysisType.class);
		settings.number_of_gevs = store.getInt(LABEL_nontermination_number_gevs);
		settings.nilpotent_components = store.getBoolean(LABEL_nontermination_nilpotent_components);
		settings.allowBounded = store.getBoolean(LABEL_nontermination_bounded_executions);
		return settings;
	}
}
