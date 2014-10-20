package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.ArrayList;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15TestSuite extends AbstractSVCOMP15TestSuite {

	// Timeout for each test case in milliseconds
	private static long sTimeout = 60 * 1000;

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
				"svcomp2015/svComp-32bit-precise.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "AutomizerC.xml",
				"svcomp2015/svComp-64bit-simple.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/BackwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml", "svcomp2015/svComp-32bit-simple.epf",
				sTimeout));

		/* Kojak */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-64bit-precise-BE-Kojak.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Kojak.epf", sTimeout));

		/* Impulse */
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-64bit-precise-BE-Impulse.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "CodeCheckWithBE-C.xml",
				"svcomp2015/svComp-32bit-precise-BE-Impulse.epf", sTimeout));

		return rtr;
	}

}
