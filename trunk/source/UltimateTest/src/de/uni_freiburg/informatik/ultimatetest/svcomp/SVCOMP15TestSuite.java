package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15TestSuite extends AbstractSVCOMP15TestSuite {

	@Override
	protected long getTimeout() {
		// Timeout for each test case in milliseconds
		return 120 * 1000;
	}

	@Override
	protected int getFilesPerCategory() {
		// -1 or value larger than 0
		return 30;
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
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ECA", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ProductLines", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Recursive", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Sequentialized", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "AutomizerC.xml",
				"svcomp2015/svComp-64bit-simple.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/BackwardPredicates_SvcompReachPreciseMM.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml", "svcomp2015/svComp-32bit-simple.epf",
				getTimeout()));
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml", "svcomp2015/svComp-32bit-memsafety.epf",
				getTimeout()));

		/* Kojak */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ECA", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ProductLines", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Recursive", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Sequentialized", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-64bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml", 
				"svcomp2015/svComp-32bit-memsafety-BE-Kojak.epf.epf", getTimeout()));

		/* Impulse */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ECA", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Loops", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("ProductLine", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Recursive", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Sequentialized", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-64bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", getTimeout()));
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml", 
				"svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf.epf", getTimeout()));


		return rtr;
	}

}
