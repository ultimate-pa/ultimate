/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;

import java.util.Collections;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Statements2TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

public class RcfgPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum CodeBlockSize {
		SingleStatement, OneNontrivialStatement, SequenceOfStatements, LoopFreeBlock, SequenceOfStatementsBreakOnNondet
	}

	// some solver commands
	public static final String Z3_NO_EXTENSIONAL_ARRAYS =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000 auto_config=false smt.array.extensional=false";
	public static final String Z3_NO_MBQI =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000 auto_config=false smt.mbqi=false";
	public static final String Z3_DEFAULT = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String Z3_LOW_TIMEOUT = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:2000";
	public static final String CVC4 = "cvc4 --incremental --print-success --lang smt --tlimit-per=12000";
	public static final String Princess = "princess +incremental +stdin -timeout=12000";

	/*
	 * new preferences that belong to the RCFG Builder
	 */
	public static final String LABEL_ASSUME_FOR_ASSERT = "Add additional assume for each assert";
	public static final boolean DEF_ASSUME_FOR_ASSERT = !false;

	private static final String DESC_ASSUME_FOR_ASSERT =
			"While checking some specification, assume that all other specifications hold. This is only sound in a setting where the verification process stops after the first violated specification was found.";

	public static final String LABEL_SOLVER = "SMT solver";
	public static final SolverMode DEF_SOLVER = SolverMode.External_ModelsAndUnsatCoreMode;
	// public static final Solver DEF_Solver = Solver.Internal_SMTInterpol;

	public static final String LABEL_FAKE_NON_INCREMENTAL_SCRIPT = "Fake non-incremental script";
	public static final boolean DEF_FAKE_NON_INCREMENTAL_SCRIPT = false;

	public static final String LABEL_EXT_SOLVER_COMMAND = "Command for external solver";
	public static final String DEF_EXT_SOLVER_COMMAND = Z3_DEFAULT;

	public static final String LABEL_EXT_SOLVER_LOGIC = "Logic for external solver";
	public static final String DEF_EXT_SOLVER_LOGIC = "ALL";

	public static final String LABEL_CODE_BLOCK_SIZE = "Size of a code block";

	public static final CodeBlockSize DEF_CODE_BLOCK_SIZE = CodeBlockSize.LoopFreeBlock;
	public static final String LABEL_SIMPLIFY = "Simplify code blocks";
	public static final String LABEL_CNF = "Convert code blocks to CNF";
	public static final String LABEL_REMOVE_GOTO_EDGES = "Remove goto edges from RCFG";
	public static final String LABEL_DUMP_TO_FILE = "Dump SMT script to file";
	public static final String LABEL_COMPRESS_SMT_DUMP_FILE = "Compress dumped SMT script";
	public static final String DESC_COMPRESS_SMT_DUMP_FILE = "Compress the written .smt2 script with GZip";
	public static final String LABEL_DUMP_UNSAT_CORE_BENCHMARK = "Dump unsat core track benchmark to file";
	public static final String LABEL_DUMP_MAIN_TRACK_BENCHMARK = "Dump main track benchmark to file";
	public static final String LABEL_DUMP_PATH = "To the following directory";
	public static final String DEF_DUMP_PATH = "";

	/**
	 * @see Statements2TransFormula#mSimplePartialSkolemization
	 */
	public static final String LABEL_SIMPLE_PARTIAL_SKOLEMIZATION = "Skolemize terms";
	public static final boolean DEF_SIMPLE_PARTIAL_SKOLEMIZATION = true;
	public static final String LABEL_ADDITIONAL_SMT_OPTIONS = "Additional SMT options";
	public static final Map<String, String> DEF_ADDITIONAL_SMT_OPTIONS = Collections.emptyMap();
	public static final String LABEL_REMOVE_ASSUME_TRUE = "Remove assume true statements";
	private static final boolean DEF_REMOVE_ASSUME_TRUE = true;
	private static final String DESC_REMOVE_ASSUME_TRUE =
			"Removes all assume true statements while building the RCFG graph. This is in particular useful for concurrent programs.";

	public RcfgPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_ASSUME_FOR_ASSERT, DEF_ASSUME_FOR_ASSERT, DESC_ASSUME_FOR_ASSERT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SOLVER, DEF_SOLVER, PreferenceType.Combo, SolverMode.values()),
				new UltimatePreferenceItem<>(LABEL_FAKE_NON_INCREMENTAL_SCRIPT, DEF_FAKE_NON_INCREMENTAL_SCRIPT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EXT_SOLVER_COMMAND, DEF_EXT_SOLVER_COMMAND, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_EXT_SOLVER_LOGIC, DEF_EXT_SOLVER_LOGIC, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_CODE_BLOCK_SIZE, DEF_CODE_BLOCK_SIZE, PreferenceType.Combo,
						CodeBlockSize.values()),
				new UltimatePreferenceItem<>(LABEL_REMOVE_GOTO_EDGES, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLIFY, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CNF, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLE_PARTIAL_SKOLEMIZATION, DEF_SIMPLE_PARTIAL_SKOLEMIZATION,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_REMOVE_ASSUME_TRUE, DEF_REMOVE_ASSUME_TRUE, DESC_REMOVE_ASSUME_TRUE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_TO_FILE, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_UNSAT_CORE_BENCHMARK, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_MAIN_TRACK_BENCHMARK, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_COMPRESS_SMT_DUMP_FILE, false, DESC_COMPRESS_SMT_DUMP_FILE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_PATH, DEF_DUMP_PATH, PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_ADDITIONAL_SMT_OPTIONS, DEF_ADDITIONAL_SMT_OPTIONS,
						PreferenceType.KeyValue),
				getTestGenerationSettings(),

		};
	}

	public UltimatePreferenceItem getTestGenerationSettings() {
		return new UltimatePreferenceItem<>(LABEL_TEST_GEN_REUSE_MODE, DEF_TEST_GEN_REUSE_MODE,
				DESC_TEST_GEN_REUSE_MODE, PreferenceType.Combo, TestGenReuseMode.values());
	}

	public static IPreferenceProvider getPreferences(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	// Test Generation Reuse Mode
	// ========================================================================
	private static final TestGenReuseMode DEF_TEST_GEN_REUSE_MODE = TestGenReuseMode.None;
	public static final String LABEL_TEST_GEN_REUSE_MODE = "Reuse Mode for Test Generation";
	private static final String DESC_TEST_GEN_REUSE_MODE =
			"None means no reuse, Reuse is without optimizations, ReuseUNSAT uses all optimiztations";

	/**
	 * Differnt modes of Reusing Test Cases during Test Generation
	 *
	 * @author Max Barth (Max.Barth@gmx.de)
	 */
	public enum TestGenReuseMode {
		/**
		 * No reuse during Test Generation.
		 */
		None,
		/**
		 * Simple Reuse just without optimizations
		 */
		Reuse,
		/**
		 * Reuse UNSAT by removing the check of the other branch and choosing values for inputs between testgoals
		 */
		ReuseUNSATmatchPrefix, ReuseUNSATmatchCalloc
	}
}
