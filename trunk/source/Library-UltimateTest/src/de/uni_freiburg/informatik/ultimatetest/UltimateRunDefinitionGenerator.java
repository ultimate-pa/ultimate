package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimateRunDefinitionGenerator {
	private static final String SETTINGS_PATH = "examples/settings/";
	private static final String TOOLCHAIN_PATH = "examples/toolchains/";

	private static File getSettingsFileFromTrunk(String settings) {
		return new File(TestUtil.getPathFromTrunk(SETTINGS_PATH + settings));
	}

	private static File getToolchainFileFromTrunk(String toolchain) {
		return new File(TestUtil.getPathFromTrunk(TOOLCHAIN_PATH + toolchain));
	}

	private static File getInputFileFromTrunk(String input) {
		return new File(TestUtil.getPathFromTrunk(input));
	}

	/**
	 * Get input files from directory. Do not take all files but only up to n pseudorandomly selected files.
	 */
	private static Collection<File> getInputFiles(File directory, String[] fileEndings, int n) {
		return TestUtil.limitFiles(TestUtil.getFiles(directory, fileEndings), n);
	}

	/**
	 * Get an {@link UltimateRunDefinition} from strings representing relative paths.
	 * 
	 * @param input
	 *            A relative path to a single input file.
	 * @param settings
	 *            A relative path to a settings file. May be null.
	 * @param toolchain
	 *            A relative path to a toolchain file.
	 */
	public static UltimateRunDefinition getRunDefinitionFromTrunk(final String input, final String settings,
			final String toolchain) {
		return new UltimateRunDefinition(getInputFileFromTrunk(input),
				settings == null ? null : getSettingsFileFromTrunk(settings), getToolchainFileFromTrunk(toolchain));
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> define a run definition with the settings file
	 * <code>settings</code> and the toolchain file <code>toolchain</code>. All files are defined by their paths
	 * relative to the Ultimate trunk directory.
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain) {
		return getRunDefinitionFromTrunk(directories, fileEndings, settings, toolchain, -1);
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * some files with a file ending from <code>fileEndings</code> define a run definition with the settings file
	 * <code>settings</code> and the toolchain file <code>toolchain</code>.
	 * 
	 * All files are defined by their paths relative to the Ultimate trunk directory.
	 * 
	 * For each directory, at most <code>limit</code> files are used. They are selected pseudo-randomly but
	 * deterministic (i.e., multiple runs with the same parameter generate the same result).
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain, int limit) {
		final File toolchainFile = getToolchainFileFromTrunk(toolchain);
		final File settingsFile = settings == null ? null : getSettingsFileFromTrunk(settings);
		return Arrays.stream(directories).map(a -> getInputFileFromTrunk(a))
				.map(a -> getInputFiles(a, fileEndings, limit)).flatMap(a -> a.stream()).distinct()
				.map(a -> new UltimateRunDefinition(a, settingsFile, toolchainFile)).collect(Collectors.toList());
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(String toolchain, String settings,
			DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		return Arrays.stream(directoryFileEndingsPairs)
				.map(a -> UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { a.getDirectory() },
						a.getFileEndings(), settings, toolchain, a.getLimit()))
				.flatMap(a -> a.stream()).collect(Collectors.toList());
	}
	
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(String toolchain, String settings,
			DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		return Arrays.stream(directoryFileEndingsPairs)
				.map(a -> UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { a.getDirectory() },
						a.getFileEndings(), settings, toolchain, a.getLimit()))
				.flatMap(a -> a.stream()).collect(Collectors.toList());
	}
}
