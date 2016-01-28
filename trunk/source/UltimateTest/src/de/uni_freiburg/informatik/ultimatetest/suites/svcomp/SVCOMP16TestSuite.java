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
package de.uni_freiburg.informatik.ultimatetest.suites.svcomp;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP16TestSuite extends AbstractSVCOMPTestSuite {

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 60 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return 20;
	}

	@Override
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();
		//@formatter:off

		// available sets:
		//Arrays
		//BitVectors.set
		//Concurrency.set
		//ControlFlowInteger.set
		//DeviceDrivers64.set
		//DriverChallenges.set
		//ECA.set
		//Floats.set
		//HeapManipulation.set
		//Loops.set
		//MemorySafety.set
		//ProductLines.set
		//Recursive.set
		//Sequentialized.set
		//Simple.set
		//Stateful.set
		//Termination-crafted.set
		//Termination-ext.set
		//@formatter:on

		rtr.addAll(getForThree("ControlFlow"));
		rtr.addAll(getForThree("Simple"));
		rtr.addAll(getForThree("ECA"));
		rtr.addAll(getForThree("Loops"));
		rtr.addAll(getForThree("Recursive"));
		rtr.addAll(getForThree("ProductLines"));
		rtr.addAll(getForThree("Sequentialized"));

		return rtr;
	}

	private List<TestDefinition> getForThree(final String set) {
		final List<TestDefinition> rtr = new ArrayList<>();
		rtr.add(getTestDefinitionFromExamples(set, "AbstractInterpretationv2C.xml",
				"ai/svcomp-Reach-32bit-AIv2_INT.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples(set, "AutomizerC.xml", "ai/svcomp-Reach-32bit-Automizer_Default.epf",
				getTimeout()));
		rtr.add(getTestDefinitionFromExamples(set, "AutomizerC.xml",
				"ai/svcomp-Reach-32bit-Automizer_Default+AIv2_INT.epf", getTimeout()));
		return rtr;
	}

}
