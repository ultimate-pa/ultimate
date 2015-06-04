package de.uni_freiburg.informatik.ultimatetest.knownbugs;

import java.io.File;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

public class WitnessBugs extends AbstractBugTestSuite {

	@Override
	protected void fillTestCases() {

		// addAutomizer32bitPrecise("examples/svcomp/product-lines/email_spec6_product35_false-unreach-call.cil.c");

		//
		final List<File> files = TestUtil.getFiles(
				new File(TestUtil.getPathFromTrunk("examples/Backtranslation/regression/c/standard/")),
				new String[] { ".c" });
		addTestCases(getToolchainFile("AutomizerC.xml"),
				getSettingsFile("witness/svComp-32bit-precise-Automizer-ValidateCPA.epf"), files);

	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected long getTimeout() {
		// default: 300 * 1000
		return 900 * 1000;
		// return super.getTimeout();
	}

	private void addAutomizer32bitPrecise(String file) {
		addTestCase("AutomizerC.xml", "witness/svComp-32bit-precise-Automizer-Witness.epf", file);
	}

	private void addImpulse32bitPrecise(String file) {
		addTestCase("CodeCheckWithBE-C.xml", "witness/svComp-32bit-precise-BE-Impulse-Witness.epf", file);
	}
}
