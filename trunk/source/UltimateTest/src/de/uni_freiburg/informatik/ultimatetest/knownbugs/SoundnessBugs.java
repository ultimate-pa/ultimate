package de.uni_freiburg.informatik.ultimatetest.knownbugs;

public class SoundnessBugs extends AbstractBugTestSuite {

	@Override
	protected void fillTestCases() {

		// addTestCasesFixed("AutomizerC.xml",
		// "svcomp2015/svComp-32bit-precise-Automizer.epf", testcases);
		// addTestCasesFixed("AutomizerC.xml",
		// "svcomp2015/svComp-64bit-simple-Automizer.epf", testcases);
		// addTestCasesFixed("AutomizerC.xml",
		// "svcomp2015/svComp-32bit-memsafety-Automizer.epf", testcases);
		// addTestCasesFixed("AutomizerC.xml",
		// "svcomp2015/svComp-32bit-simple-Automizer.epf", testcases);
	}

	@Override
	protected int getTimeout() {
		// default: 300 * 1000
		return super.getTimeout();
	}

	private void addAutomizer32bitPrecise(String file) {
		addTestCase("AutomizerC.xml", "svcomp2015/svComp-32bit-precise-Automizer-Witness.epf", file);
	}

	private void addImpulse32bitPrecise(String file) {
		addTestCase("CodeCheckWithBE-C.xml", "svcomp2015/svComp-32bit-precise-BE-Impulse.epf", file);
	}

	private void addImpulse64bitPrecise(String file) {
		addTestCase("CodeCheckWithBE-C.xml", "svcomp2015/svComp-64bit-precise-BE-Impulse.epf", file);
	}

	private void addImpulse32bitMemsafety(String file) {
		addTestCase("CodeCheckWithBE-C.xml", "svcomp2015/svComp-32bit-memsafety-BE-Impulse.epf", file);
	}
}
