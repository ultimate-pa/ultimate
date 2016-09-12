/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimatetest.suites.translation;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Svcomp2016CTranslationTestSuite extends AbstractEvalTestSuite {

	private static final String[] ALL_C = new String[] { ".c", ".i" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;
	// @formatter:off
	
	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS = new Triple[] {
//			new Triple<>("AbstractInterpretationMk2CInline.xml", ALL_C, "ai/AI2_INT.epf"),
//			new Triple<>("AbstractInterpretationMk2C.xml", ALL_C, "ai/AI2_INT.epf"),
//			new Triple<>("AbstractInterpretationMk2.xml", BPL, "ai/AI2_INT.epf"),
			
//			new Triple<>("AbstractInterpretationMk2CInline.xml", ALL_C, "ai/AI2_PLT.epf"),
//			new Triple<>("AbstractInterpretationMk2C.xml", ALL_C, "ai/AI2_PLT.epf"),
//			new Triple<>("AbstractInterpretationMk2.xml", BPL, "ai/AI2_PLT.epf"),
			
//			new Triple<>("AbstractInterpretationMk2CInline.xml", ".c", "ai/AI2_CMP.epf"),
//			new Triple<>("AbstractInterpretationMk2C.xml", ".c", "ai/AI2_CMP.epf"),
//			new Triple<>("AbstractInterpretationMk2.xml", ".bpl", "ai/AI2_CMP.epf"),

//			new Triple<>("AbstractInterpretationv2CInline.xml", ALL_C, "ai/AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretationv2C.xml", ALL_C, "ai/AIv2_INT.epf"),
//			new Triple<>("AbstractInterpretationv2.xml", BPL, "ai/AIv2_INT.epf"),

			new Triple<>("CTranslationTest.xml", ALL_C, "svcomp2016/svcomp-Reach-64bit-Automizer_Default.epf"),

//			new Triple<>("AbstractInterpretationC.xml", ALL_C, "ai/AI.epf"),
//			new Triple<>("AbstractInterpretation.xml", BPL, "ai/AI.epf"),
			
//			new Triple<>("AutomizerCInline.xml", ".c", "EmptySettings.epf"),
//			new Triple<>("AutomizerC.xml", ".c", "EmptySettings.epf"),
//			new Triple<>("AutomizerBpl.xml", ".bpl", "EmptySettings.epf"), 
	};



	private static final String[] INPUT = new String[] {
			/* ULTIMATE repo */
			// "examples/programs/abstractInterpretation/",
			// "examples/programs/abstractInterpretationNoRec/",
//			 "examples/programs/regression/bpl/",
//			 "examples/programs/regression/c/",
//			// "examples/programs/recursive/regression",
//			
//			 /* SV-COMP repo */
//			"examples/svcomp/loops/", 
//			// "examples/svcomp/loopsSelection/",
//			// "examples/svcomp/eca/", 
			 "examples/svcomp/",
//			// "examples/svcomp/ecaSelection/",
//			// "examples/svcomp/systemc/", 
//			// "examples/svcomp/systemc1/",
//			// "examples/svcomp/systemc2/",
//			// "examples/svcomp/eca-rers2012/",
//			// "examples/svcomp/recursive/",
//			 "examples/svcomp/ssh-simplified/",
//			 "examples/svcomp/ntdrivers-simplified/",
			// "examples/svcomp/ssh/",
			 
			 //single files 
//			 "examples/programs/regression/bpl/BugFreshConstantInSSA.bpl",
//			 "examples/programs/regression/c/Enums01-Safe.c",
//			 "examples/programs/regression/c/Enums02-Safe.c",
//			 "examples/programs/regression/c/Enums04-Safe.c",
//			 "examples/programs/regression/bpl/BugModifiesChecker.bpl",
//			 
//			 //soundness
//			 "examples/programs/regression/bpl/interprocedural/BugBackwardPredicates04.bpl",
//			 "examples/programs/regression/c/NondeterministicLocalVarInitialValues.c"
			 
	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		return 10 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Total time", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new TranslationTestResultDecider(urd.selectPrimaryInputFile());
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
