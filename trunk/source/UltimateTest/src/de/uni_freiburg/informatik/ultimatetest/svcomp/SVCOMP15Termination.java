package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TerminationAnalysisTestResultDecider;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15Termination extends AbstractSVCOMP15TestSuite {

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
		rtr.add(getTestDefinitionFromExamples("Termination-crafted", "BuchiAutomizerCWithBlockEncoding.xml",
				"svcomp2015/svComp-64bit-termination-Automizer", getTimeout()));

		return rtr;
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition urd) {
		return new TerminationAnalysisTestResultDecider(urd, true);
	}

}
