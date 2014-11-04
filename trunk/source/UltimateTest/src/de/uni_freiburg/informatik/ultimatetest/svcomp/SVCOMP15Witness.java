package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15Witness extends AbstractSVCOMP15TestSuite {

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
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();

		/* Automizer */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger.false-unreach-label", "AutomizerC.xml",
				"witness/svComp-32bit-precise-Automizer-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "AutomizerC.xml",
				"witness/svComp-32bit-precise-Automizer-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-label", "AutomizerC.xml",
				"witness/svComp-32bit-precise-Automizer-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "AutomizerC.xml",
				"witness/svComp-32bit-precise-Automizer-Witness.epf", getTimeout()));


//		/* Kojak */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger.false-unreach-label", "CodeCheckWithBE-C.xml",
				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "CodeCheckWithBE-C.xml",
				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-label", "CodeCheckWithBE-C.xml",
				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "CodeCheckWithBE-C.xml",
				"witness/svComp-32bit-precise-BE-Impulse-Witness.epf", getTimeout()));

		return rtr;
	}

}
