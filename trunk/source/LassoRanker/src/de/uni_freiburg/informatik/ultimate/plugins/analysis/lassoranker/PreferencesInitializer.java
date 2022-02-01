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
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.DefaultLassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.DefaultNonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.INonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.DefaultTerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.ITerminationAnalysisSettings;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.TerminationAnalysisSettings;

/**
 * Initializer class for LassoRanker's preferences in Ultimate's GUI
 *
 * @see LassoRankerPreferences
 * @author Jan Leike
 */
public class PreferencesInitializer extends UltimatePreferenceInitializer {

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

	public PreferencesInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		// Get default preferences and settings
		final ILassoRankerPreferences lassoRankerDefaults = new DefaultLassoRankerPreferences();
		final ITerminationAnalysisSettings terminationSettings = new DefaultTerminationAnalysisSettings();
		final INonTerminationAnalysisSettings nonTerminationDefaults = new DefaultNonTerminationAnalysisSettings();
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_enable_partitioneer, lassoRankerDefaults.isEnablePartitioneer(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_nontermination_analysis, nonTerminationDefaults.getAnalysis(),
						PreferenceType.Combo, AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_nontermination_number_gevs, nonTerminationDefaults.getNumberOfGevs(),
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_nontermination_nilpotent_components,
						nonTerminationDefaults.isNilpotentComponents(), PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_nontermination_bounded_executions,
						nonTerminationDefaults.isAllowBounded(), PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_termination_analysis, terminationSettings.getAnalysis(),
						PreferenceType.Combo, AnalysisType.values()),
				new UltimatePreferenceItem<>(LABEL_numstrict_invariants, terminationSettings.getNumStrictInvariants(),
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_numnon_strict_invariants,
						terminationSettings.getNumNonStrictInvariants(), PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_nondecreasing_invariants,
						terminationSettings.isNonDecreasingInvariants(), PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_compute_integral_hull, lassoRankerDefaults.isComputeIntegralHull(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_annotate_terms, lassoRankerDefaults.isAnnotateTerms(),
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
				new UltimatePreferenceItem<>(LABEL_smt_solver_command, lassoRankerDefaults.getExternalSolverCommand(),
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_dump_smt_script, lassoRankerDefaults.isDumpSmtSolverScript(),
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_path_of_dumped_script, lassoRankerDefaults.getPathOfDumpedScript(),
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
		final IPreferenceProvider store = services.getPreferenceProvider(Activator.PLUGIN_ID);
		return new TerminationAnalysisSettings(new DefaultTerminationAnalysisSettings() {
			@Override
			public AnalysisType getAnalysis() {
				return store.getEnum(LABEL_termination_analysis, AnalysisType.class);
			}

			@Override
			public int getNumStrictInvariants() {
				return store.getInt(LABEL_numstrict_invariants);
			}

			@Override
			public int getNumNonStrictInvariants() {
				return store.getInt(LABEL_numnon_strict_invariants);
			}

			@Override
			public boolean isNonDecreasingInvariants() {
				return store.getBoolean(LABEL_nondecreasing_invariants);
			}

			@Override
			public boolean isSimplifyTerminationArgument() {
				return store.getBoolean(LABEL_simplify_result);
			}

			@Override
			public boolean isSimplifySupportingInvariants() {
				return store.getBoolean(LABEL_simplify_result);
			}
		});
	}

	/**
	 * @return the (local) nontermination analysis settings from the GUI
	 */
	public static NonTerminationAnalysisSettings
			getNonTerminationAnalysisSettings(final IUltimateServiceProvider services) {
		final IPreferenceProvider store = services.getPreferenceProvider(Activator.PLUGIN_ID);

		return new NonTerminationAnalysisSettings(new DefaultNonTerminationAnalysisSettings() {
			@Override
			public AnalysisType getAnalysis() {
				return store.getEnum(LABEL_nontermination_analysis, AnalysisType.class);
			}

			@Override
			public int getNumberOfGevs() {
				return store.getInt(LABEL_nontermination_number_gevs);
			}

			@Override
			public boolean isNilpotentComponents() {
				return store.getBoolean(LABEL_nontermination_nilpotent_components);
			}

			@Override
			public boolean isAllowBounded() {
				return store.getBoolean(LABEL_nontermination_bounded_executions);
			}
		});
	}
}
