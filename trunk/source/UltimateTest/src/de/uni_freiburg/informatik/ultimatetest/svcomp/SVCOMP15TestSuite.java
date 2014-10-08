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
	private static long sTimeout = 20000;

	@Override
	protected List<TestDefinition> getTestDefinitions() {
		List<TestDefinition> rtr = new ArrayList<>();

//		rtr.add(getTestDefinitionFromExamples("BitVectors", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Concurrency", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64", "AutomizerC.xml",
				"svcomp2015/svComp-64bit-simple.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("DriverChallenges", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("ECA", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Floats", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("HeapManipulation", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-precise.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Loops", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("MemorySafety", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-memsafety.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("ProductLines", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("PropertyERROR.prp", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("PropertyMemSafety.prp", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("PropertyTermination.prp", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Recursive", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Sequentialized", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"automizer/BackwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
		rtr.add(getTestDefinitionFromExamples("Simple", "AutomizerC.xml",
				"svcomp2015/svComp-32bit-simple.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Stateful", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Termination-crafted", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));
//		rtr.add(getTestDefinitionFromExamples("Termination-ext", "AutomizerC.xml",
//				"automizer/ForwardPredicates_SvcompReachPreciseMM.epf", sTimeout));

		return rtr;
	}

}
