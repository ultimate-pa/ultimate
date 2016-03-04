package de.uni_freiburg.informatik.ultimatetest;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
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

	private static File getFileFromSettingsDir(String settings) {
		return new File(TestUtil.getPathFromTrunk(SETTINGS_PATH + settings));
	}

	private static File getFileFromToolchainDir(String toolchain) {
		return new File(TestUtil.getPathFromTrunk(TOOLCHAIN_PATH + toolchain));
	}

	private static File getFileFromTrunkDir(String input) {
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
		return new UltimateRunDefinition(getFileFromTrunkDir(input),
				settings == null ? null : getFileFromSettingsDir(settings), getFileFromToolchainDir(toolchain));
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
	 * Note:
	 * <ul>
	 * <li>All files are defined by their paths relative to the Ultimate trunk directory.
	 * <li>For each directory, at most <code>limit</code> files are used. They are selected pseudo-randomly but
	 * deterministic (i.e., multiple runs with the same parameter generate the same result).
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain, int limit) {
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);
		return Arrays.stream(directories).map(a -> getFileFromTrunkDir(a))
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

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> that have a witness in the same folder define a run
	 * definition with the settings file <code>settings</code> and the toolchain file <code>toolchain</code>.
	 * 
	 * Note:
	 * <ul>
	 * <li>All files are defined by their paths relative to the Ultimate trunk directory.
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file without their
	 * ending.
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain) {
		return getRunDefinitionFromTrunkWithWitnesses(directories, fileEndings, settings, toolchain, -1);
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> that have a witness in the same folder define a run
	 * definition with the settings file <code>settings</code> and the toolchain file <code>toolchain</code>.
	 * 
	 * Note:
	 * <ul>
	 * <li>All files are defined by their paths relative to the Ultimate trunk directory.
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file without their
	 * ending.
	 * <li>For each directory, at most <code>limit</code> files are used. They are selected pseudo-randomly but
	 * deterministic (i.e., multiple runs with the same parameter generate the same result).
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain, int limit) {
		return getRunDefinitionFromTrunkWithWitnesses(toolchain, settings,
				Arrays.stream(directories).map(a -> new DirectoryFileEndingsPair(a, fileEndings, limit))
						.toArray(size -> new DirectoryFileEndingsPair[size]));
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String toolchain,
			final String settings, final DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<UltimateRunDefinition>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);

		for (final DirectoryFileEndingsPair pair : directoryFileEndingsPairs) {
			final File dir = getFileFromTrunkDir(pair.getDirectory());
			final Collection<File> inputFiles = getInputFiles(dir, pair.getFileEndings(), pair.getLimit());
			final Collection<File> witnessCandidates;
			if (dir.isFile()) {
				witnessCandidates = TestUtil.getFiles(dir.getParentFile(), new String[] { ".graphml" });
			} else {
				witnessCandidates = TestUtil.getFiles(dir, new String[] { ".graphml" });
			}

			for (final File inputFile : inputFiles) {
				final String endingRegex = TestUtil.getRegexFromFileendings(pair.getFileEndings());
				final String nameWithoutEnding = inputFile.getName().replaceAll(endingRegex, "");
				final List<File> witnesses = witnessCandidates.stream()
						.filter(a -> a.getName().startsWith(nameWithoutEnding)).collect(Collectors.toList());
				for (final File witness : witnesses) {
					rtr.add(new UltimateRunDefinition(new File[] { inputFile, witness }, settingsFile, toolchainFile));
				}
			}
		}
		return rtr;
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> that have a witness in the folder
	 * <code>witnessFolder</code> define a run definition with the settings file <code>settings</code> and the toolchain
	 * file <code>toolchain</code>.
	 * 
	 * Note:
	 * <ul>
	 * <li><code>witnessFolder</code> is an absolute path.
	 * <li>All other files are defined by their paths relative to the Ultimate trunk directory.
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file without their
	 * ending.
	 * <li>For each directory, at most <code>limit</code> files are used. They are selected pseudo-randomly but
	 * deterministic (i.e., multiple runs with the same parameter generate the same result).
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String toolchain, final String settings, final DirectoryFileEndingsPair[] input,
			final String witnessFolder) {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<UltimateRunDefinition>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);

		final File witnessFolderFile = new File(witnessFolder);
		if (!witnessFolderFile.exists()) {
			throw new IllegalArgumentException(
					"Path to witness folder " + witnessFolderFile.getAbsolutePath() + " does not exist.");
		}
		final Collection<File> witnessCandidates;
		if (witnessFolderFile.isFile()) {
			witnessCandidates = TestUtil.getFiles(witnessFolderFile.getParentFile(), new String[] { ".graphml" });
		} else {
			witnessCandidates = TestUtil.getFiles(witnessFolderFile, new String[] { ".graphml" });
		}

		for (final DirectoryFileEndingsPair pair : input) {
			final File dir = getFileFromTrunkDir(pair.getDirectory());
			final Collection<File> inputFiles = getInputFiles(dir, pair.getFileEndings(), pair.getLimit());

			for (final File inputFile : inputFiles) {
				final String endingRegex = TestUtil.getRegexFromFileendings(pair.getFileEndings());
				final String nameWithoutEnding = inputFile.getName().replaceAll(endingRegex, "");
				final List<File> witnesses = witnessCandidates.stream()
						.filter(a -> a.getName().startsWith(nameWithoutEnding)).collect(Collectors.toList());
				for (final File witness : witnesses) {
					rtr.add(new UltimateRunDefinition(new File[] { inputFile, witness }, settingsFile, toolchainFile));
				}
			}
		}
		return rtr;
	}
}
