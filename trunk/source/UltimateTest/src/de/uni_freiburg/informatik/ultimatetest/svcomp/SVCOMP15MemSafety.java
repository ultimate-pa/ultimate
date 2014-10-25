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
		return 120 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return -1;
	}

	@Override
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();
		//@formatter:off

		// available sets:
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

		/* Automizer */
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-memsafety.epf", getTimeout()));

		/* Kojak */
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-memsafety-BE-Kojak.epf", getTimeout()));

		/* Impulse */
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf", getTimeout()));

		return rtr;
	}

}
