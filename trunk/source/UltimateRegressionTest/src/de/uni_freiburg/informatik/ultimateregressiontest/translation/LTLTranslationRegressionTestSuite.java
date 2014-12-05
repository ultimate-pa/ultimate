package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class LTLTranslationRegressionTestSuite extends AbstractRegressionTestSuite {

	public LTLTranslationRegressionTestSuite() {
		mTimeout = 10 * 1000;
		mFiletypesToConsider = new String[] { ".c" };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new TranslationTestResultDecider(runDefinition.getInput());
	}

	@Override
	protected Collection<Pair> getRunConfiguration() {
		List<Pair> rtr = new ArrayList<>();

		rtr.add(getPair("examples/toolchains/LtlTranslationC.xml", "examples/settings/LtlSoftwareModelCheckingC.epf"));

		return rtr;
	}

	@Override
	protected Collection<File> getInputFiles(Pair runConfiguration) {
		return Util.getFiles(getPathFromTrunk("examples/LTL/rers/"), mFiletypesToConsider);
	}

	private Pair getPair(String toolchain, String setting) {
		return new Pair(getPathFromTrunk(toolchain), getPathFromTrunk(setting));
	}

	private File getPathFromTrunk(String path) {
		return new File(Util.getPathFromTrunk(path));
	}

}
