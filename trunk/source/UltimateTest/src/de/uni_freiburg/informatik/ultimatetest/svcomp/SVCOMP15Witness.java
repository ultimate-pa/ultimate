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
				"svcomp2015/svComp-32bit-precise-wit.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-wit.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-label", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-wit.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-precise-wit.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64.false-unreach-label", "AutomizerC.xml",
//				"svcomp2015/svComp-64bit-simple-wit.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Simple.false-unreach-label", "AutomizerC.xml",
//				"svcomp2015/svComp-32bit-simple-wit.epf", getTimeout()));

//		/* Kojak */
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLines.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Kojak.epf", getTimeout()));
//		
//		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-64bit-simple-wit-BE-Kojak.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Simple.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-simple-wit-BE-Kojak.epf", getTimeout()));
//
//		/* Impulse */
//		rtr.add(getTestDefinitionFromExamples("ControlFlowInteger.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Loops.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("ProductLine.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Sequentialized.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-precise-wit-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("DeviceDrivers64.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-64bit-simple-wit-BE-Impulse.epf", getTimeout()));
//		rtr.add(getTestDefinitionFromExamples("Simple.false-unreach-label", "CodeCheckWithBE-C.xml",
//				"svcomp2015/svComp-32bit-simple-wit-BE-Impulse.epf", getTimeout()));

		return rtr;
	}

}
