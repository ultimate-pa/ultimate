package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15MemSafety extends AbstractSVCOMP15TestSuite {

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 30 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return 150;
	}

	@Override
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();

		/* Automizer */
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-memsafety-Automizer.epf", getTimeout()));

		/* Kojak */
		// rtr.add(getTestDefinitionFromExamples("MemorySafety",
		// "CodeCheckWithBE-C.xml",
		// "svcomp2015/svComp-32bit-memsafety-BE-Kojak.epf", getTimeout()));

		/* Impulse */
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf", getTimeout()));

		return rtr;
	}

}
