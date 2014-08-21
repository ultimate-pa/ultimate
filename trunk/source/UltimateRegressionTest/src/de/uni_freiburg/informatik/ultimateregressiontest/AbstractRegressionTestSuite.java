package de.uni_freiburg.informatik.ultimateregressiontest;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
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
			Collection<File> inputFiles = getInputFiles(runConfiguration.ToolchainFile.getParentFile());

			for (File inputFile : inputFiles) {
				UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, runConfiguration.SettingsFile, runConfiguration.ToolchainFile);
				UltimateStarter starter = new UltimateStarter(urd, mTimeout, null, null);
				rtr.add(new UltimateTestCase(starter, getTestResultDecider(inputFile), null, String.format(
						"%s+%s: %s", runConfiguration.ToolchainFile.getName(), runConfiguration.SettingsFile.getName(),
						inputFile.getAbsolutePath()), urd));
			}
		}
//		return Util.firstN(rtr, 3);
		return rtr;
	}

	private Collection<Pair> getRunConfiguration() {
		ArrayList<Pair> rtr = new ArrayList<>();

		File root = getRootFolder(mRootFolder);
		if (root == null) {
			return rtr;
		}

		Collection<File> toolchainFiles = Util.getFiles(root, new String[] { ".xml" });
		Collection<File> settingsFiles = Util.getFiles(root, new String[] { ".epf" });

		toolchainFiles = Util.filter(toolchainFiles, ".*regression.*");
		toolchainFiles = Util.filter(toolchainFiles, mFilterRegex);
		settingsFiles = Util.filter(settingsFiles, ".*regression.*");
		settingsFiles = Util.filter(settingsFiles, mFilterRegex);

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

	protected Collection<File> getInputFiles(File rootFolder) {
		return Util.getFiles(rootFolder, mFiletypesToConsider);
	}

	protected abstract ITestResultDecider getTestResultDecider(File inputFile);

	private class Pair {

		private Pair(File toolchain, File settings) {
			ToolchainFile = toolchain;
			SettingsFile = settings;
		}

		private File ToolchainFile;
		private File SettingsFile;
	}

}
