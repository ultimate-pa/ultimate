package de.uni_freiburg.informatik.ultimateregressiontest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public abstract class AbstractRegressionTestSuite extends UltimateTestSuite {

	protected long mTimeout;
	protected String mRootFolder;
	protected String mFilterRegex;
	protected String[] mFiletypesToConsider;

	public AbstractRegressionTestSuite() {
		mTimeout = 1000;
		mFilterRegex = ".*";
		mFiletypesToConsider = new String[] { ".c", ".bpl" };
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		ArrayList<UltimateTestCase> rtr = new ArrayList<UltimateTestCase>();

		Collection<Pair> runConfigurations = getRunConfiguration();

		for (Pair runConfiguration : runConfigurations) {
			Collection<File> inputFiles = getInputFiles(runConfiguration);

			for (File inputFile : inputFiles) {
				UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, runConfiguration.getSettingsFile(),
						runConfiguration.getToolchainFile());
				UltimateStarter starter = new UltimateStarter(urd, mTimeout, null, null);
				rtr.add(new UltimateTestCase(String.format("%s+%s: %s", runConfiguration.getToolchainFile().getName(),
						runConfiguration.getSettingsFile().getName(), inputFile.getAbsolutePath()),
						getTestResultDecider(urd), starter, urd, null, null));
			}
		}
		// return Util.firstN(rtr, 3);
		return rtr;
	}

	/**
	 * @return A collection of Pairs of Files, where the first file represents a
	 *         toolchain and the second represents settings.
	 */
	protected Collection<Pair> getRunConfiguration() {
		ArrayList<Pair> rtr = new ArrayList<>();

		File root = getRootFolder(mRootFolder);
		if (root == null) {
			return rtr;
		}

		Collection<File> toolchainFiles = Util.getFiles(root, new String[] { ".xml" });
		Collection<File> settingsFiles = Util.getFiles(root, new String[] { ".epf" });

		toolchainFiles = Util.filterFiles(toolchainFiles, ".*regression.*");
		toolchainFiles = Util.filterFiles(toolchainFiles, mFilterRegex);
		settingsFiles = Util.filterFiles(settingsFiles, ".*regression.*");
		settingsFiles = Util.filterFiles(settingsFiles, mFilterRegex);

		for (File toolchain : toolchainFiles) {
			String toolchainName = toolchain.getName().replaceAll("\\..*", "");
			for (File settings : settingsFiles) {
				String settingsName = settings.getName().replaceAll("\\..*", "");

				if (settingsName.startsWith(toolchainName)) {
					rtr.add(new Pair(toolchain, settings));
				}
			}
		}

		return rtr;
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[0];
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}

	/***
	 * 
	 * @return null if the path to the folder is invalid, a File representing
	 *         the path otherwise
	 */
	protected static File getRootFolder(String path) {
		if (path == null) {
			return null;
		}

		File root = new File(path);

		if (!root.exists() || !root.isDirectory()) {
			return null;
		}

		return root;
	}

	/**
	 * @return All the files that should be used in this test suite. The default
	 *         implementation uses all files that can be found recursively under
	 *         the folder in which the Toolchain file (specified in
	 *         runConfiguration) lies and that have the endings specified by
	 *         mFileTypesToConsider.
	 */
	protected Collection<File> getInputFiles(Pair runConfiguration) {
		return Util.getFiles(runConfiguration.getToolchainFile().getParentFile(), mFiletypesToConsider);
	}

	protected abstract ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition);

	public class Pair {

		public Pair(File toolchain, File settings) {
			mToolchainFile = toolchain;
			mSettingsFile = settings;
		}

		public File getToolchainFile() {
			return mToolchainFile;
		}

		public File getSettingsFile() {
			return mSettingsFile;
		}

		private File mToolchainFile;
		private File mSettingsFile;
	}

}
