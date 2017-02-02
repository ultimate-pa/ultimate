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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMPWitness extends AbstractSVCOMPTestSuite {

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 30 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return 15;
	}

	@Override
	protected List<SVCOMPTestDefinition> getTestDefinitions() {
		final List<SVCOMPTestDefinition> rtr = new ArrayList<>();

		/* Automizer */
//		rtr.add(getTestDefinitionFromExamples("ControlFlow.false-unreach-call", "AutomizerC.xml",
//				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops", "AutomizerC_WitnessPrinter.xml",
				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-call", "AutomizerC.xml",
//				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-call", "AutomizerC.xml",
//				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("BitVectorsReach.false-unreach-call", "AutomizerC.xml",
//				"svcomp2016/witness-verif/svcomp-Reach-32bit-Automizer_Default-Witness.epf", getTimeout()));


//		/* Kojak */
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));

		return rtr;
	}

}
