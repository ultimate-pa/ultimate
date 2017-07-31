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

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Statements2TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

public class RcfgPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum CodeBlockSize {
		SingleStatement, SequenceOfStatements, LoopFreeBlock
	}

	// some solver commands
	public static final String Z3_NO_EXTENSIONAL_ARRAYS =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000 auto_config=false smt.array.extensional=false";
	public static final String Z3_NO_MBQI =
			"z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000 auto_config=false smt.mbqi=false";
	public static final String Z3_DEFAULT = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String Z3_LOW_TIMEOUT = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:2000";
	public static final String CVC4 = "cvc4 --tear-down-incremental --print-success --lang smt --tlimit-per=12000";
	public static final String Princess = "princess +incremental +stdin -timeout=12000";

	/*
	 * new preferences that belong to the RCFG Builder
	 */
	public static final String LABEL_ASSUME_FOR_ASSERT = "Add additional assume for each assert";
	public static final boolean DEF_ASSUME_FOR_ASSERT = !false;
	public static final String LABEL_Solver = "SMT solver";
	public static final SolverMode DEF_Solver = SolverMode.External_ModelsAndUnsatCoreMode;
	// public static final Solver DEF_Solver = Solver.Internal_SMTInterpol;

	public static final String LABEL_FakeNonIncrementalScript = "Fake non-incremental script";
	public static final boolean DEF_FakeNonIncrementalScript = false;

	public static final String LABEL_ExtSolverCommand = "Command for external solver";
	public static final String DEF_ExtSolverCommand = Z3_DEFAULT;

	public static final String LABEL_ExtSolverLogic = "Logic for external solver";
	public static final String DEF_ExtSolverLogic = "ALL";

	public static final String LABEL_CodeBlockSize = "Size of a code block";

	public static final CodeBlockSize DEF_CodeBlockSize = CodeBlockSize.LoopFreeBlock;
	public static final String LABEL_Simplify = "Simplify code blocks";
	public static final String LABEL_CNF = "Convert code blocks to CNF";
	public static final String LABEL_RemoveGotoEdges = "Remove goto edges from RCFG";
	public static final String LABEL_DumpToFile = "Dump SMT script to file";
	public static final String LABEL_DumpUnsatCoreTrackBenchmark = "Dump unsat core track benchmark to file";
	public static final String LABEL_DumpMainTrackBenchmark = "Dump main track benchmark to file";
	public static final String LABEL_Path = "To the following directory";
	public static final String DEF_Path = "";
	public static final String LABEL_BitvectorWorkaround = "Translate Boogie integers to SMT bitvectors";
	
	/**
	 * @see Statements2TransFormula#mSimplePartialSkolemization
	 */
	public static final String LABEL_SIMPLE_PARTIAL_SKOLEMIZATION = "Skolemize terms";
	public static final boolean DEF_SIMPLE_PARTIAL_SKOLEMIZATION = false;

	public RcfgPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_ASSUME_FOR_ASSERT, DEF_ASSUME_FOR_ASSERT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_Solver, DEF_Solver, PreferenceType.Combo, SolverMode.values()),
				new UltimatePreferenceItem<>(LABEL_FakeNonIncrementalScript, DEF_FakeNonIncrementalScript,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ExtSolverCommand, DEF_ExtSolverCommand, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_ExtSolverLogic, DEF_ExtSolverLogic, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_BitvectorWorkaround, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CodeBlockSize, DEF_CodeBlockSize, PreferenceType.Combo,
						CodeBlockSize.values()),
				new UltimatePreferenceItem<>(LABEL_RemoveGotoEdges, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_Simplify, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CNF, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLE_PARTIAL_SKOLEMIZATION, DEF_SIMPLE_PARTIAL_SKOLEMIZATION, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DumpToFile, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DumpUnsatCoreTrackBenchmark, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DumpMainTrackBenchmark, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_Path, DEF_Path, PreferenceType.Directory), };
	}

	public static IPreferenceProvider getPreferences(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

}
