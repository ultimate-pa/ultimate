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

package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessBugs extends AbstractEvalTestSuite {
	private static final String[] ALL_C = new String[] { ".c", ".i" };
	private static final String[] BPL = new String[] { ".bpl" };

	private static Collection<UltimateRunDefinition> createDefs() {
		Collection<UltimateRunDefinition> rtr = new ArrayList<>();
		rtr.addAll(verifyWitnessSV("loops"));
		rtr.addAll(verifyWitnessSV("product-lines"));
//		rtr.addAll(verifyWitnessSV("loops/array_true-unreach-call.i"));
//		rtr.addAll(produceWitnessSV("loops/trex02_true-unreach-call_true-termination.i"));
//		rtr.addAll(produceWitnessSV("recursive-simple/afterrec_true-unreach-call.c"));
//		rtr.addAll(produceWitness("examples/programs/toy/showcase/GoannaDoubleFree.c"));

		return rtr;
	}

	@Override
	protected long getTimeout() {
		return 60 * 1000;
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
		return new SafetyCheckTestResultDecider(urd, false);
	}

	/**
	 * Create test cases from quadruples (toolchain, fileendings, settingsfile, inputfiles)
	 */
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		addTestCase(createDefs());
		return super.createTestCases();
	}

	private static String sv(final String path) {
		return "examples/svcomp/" + path;
	}

	private static Collection<UltimateRunDefinition> produceWitnessSV(String example) {
		return produceWitness(sv(example));
	}

	private static Collection<UltimateRunDefinition> produceWitness(String example) {
		return UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { example }, ALL_C,
				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf",
				"AutomizerC_WitnessPrinter.xml");
	}
	
	private static Collection<UltimateRunDefinition> verifyWitnessSV(String example) {
		return verifyWitness(sv(example));
	}

	private static Collection<UltimateRunDefinition> verifyWitness(String example) {
		return UltimateRunDefinitionGenerator.getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(new String[] { example }, ALL_C,
				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf",
				"AutomizerC_WitnessPrinter.xml","F:/tmp/ultimate wip/correctness witnesses/results");
		
//		return UltimateRunDefinitionGenerator.getRunDefinitionFromTrunkWithWitnesses(new String[] { example }, ALL_C,
//				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf",
//				"AutomizerC_WitnessPrinter.xml");
	}
}
