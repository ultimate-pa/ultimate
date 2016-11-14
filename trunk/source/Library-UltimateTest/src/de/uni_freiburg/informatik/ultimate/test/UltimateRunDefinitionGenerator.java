package de.uni_freiburg.informatik.ultimate.test;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimateRunDefinitionGenerator {
	private static final String SETTINGS_PATH = "examples/settings/";
	private static final String TOOLCHAIN_PATH = "examples/toolchains/";

	public static File getFileFromSettingsDir(final String settings) {
		return new File(TestUtil.getPathFromTrunk(SETTINGS_PATH + settings));
	}

	public static File getFileFromToolchainDir(final String toolchain) {
		return new File(TestUtil.getPathFromTrunk(TOOLCHAIN_PATH + toolchain));
	}

	public static File getFileFromTrunkDir(final String input) {
		return new File(TestUtil.getPathFromTrunk(input));
	}

	/**
	 * Get input files from directory. Do not take all files but only up to n pseudorandomly selected files.
	 */
	private static Collection<File> getInputFiles(final File directory, final String[] fileEndings, final int offset, final int n) {
		return TestUtil.limitFiles(TestUtil.getFiles(directory, fileEndings), offset, n);
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
		return getRunDefinitionFromTrunk(directories, fileEndings, settings, toolchain, 0, -1);
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
			final String[] fileEndings, final String settings, final String toolchain, final int offset, final int limit) {
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);
		return Arrays.stream(directories).map(a -> getFileFromTrunkDir(a))
				.map(a -> getInputFiles(a, fileEndings, offset, limit)).flatMap(a -> a.stream()).distinct()
				.map(a -> new UltimateRunDefinition(a, settingsFile, toolchainFile)).collect(Collectors.toList());
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String toolchain,
			final String settings, final DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		return Arrays.stream(directoryFileEndingsPairs)
				.map(a -> UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { a.getDirectory() },
						a.getFileEndings(), settings, toolchain, a.getOffset(), a.getLimit()))
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
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file.
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain) {
		return getRunDefinitionFromTrunkWithWitnesses(directories, fileEndings, settings, toolchain, 0, -1);
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> that have a witness in the same folder define a run
	 * definition with the settings file <code>settings</code> and the toolchain file <code>toolchain</code>.
	 *
	 * Note:
	 * <ul>
	 * <li>All files are defined by their paths relative to the Ultimate trunk directory.
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file.
	 * <li>For each directory, at most <code>limit</code> files are used. They are selected pseudo-randomly but
	 * deterministic (i.e., multiple runs with the same parameter generate the same result).
	 * </ul>
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain, final int offset, final int limit) {
		return getRunDefinitionFromTrunkWithWitnesses(toolchain, settings,
				Arrays.stream(directories).map(a -> new DirectoryFileEndingsPair(a, fileEndings, offset, limit))
						.toArray(size -> new DirectoryFileEndingsPair[size]));
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String toolchain,
			final String settings, final DirectoryFileEndingsPair[] directoryFileEndingsPairs) {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<UltimateRunDefinition>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);

		for (final DirectoryFileEndingsPair pair : directoryFileEndingsPairs) {
			final File dir = getFileFromTrunkDir(pair.getDirectory());
			final Collection<File> inputFiles = getInputFiles(dir, pair.getFileEndings(), pair.getOffset(), pair.getLimit());
			final Collection<File> witnessCandidates;
			if (dir.isFile()) {
				witnessCandidates = TestUtil.getFiles(dir.getParentFile(), new String[] { ".graphml" });
			} else {
				witnessCandidates = TestUtil.getFiles(dir, new String[] { ".graphml" });
			}

			for (final File inputFile : inputFiles) {
				final List<File> witnesses = witnessCandidates.stream()
						.filter(a -> a.getName().startsWith(inputFile.getName())).collect(Collectors.toList());
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
	 * <li>A witness is a file that ends in .graphml and begins with the name of the actual input file.
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
			final Collection<File> inputFiles = getInputFiles(dir, pair.getFileEndings(), pair.getOffset(), pair.getLimit());

			for (final File inputFile : inputFiles) {
				final List<File> witnesses = witnessCandidates.stream()
						.filter(a -> a.getName().startsWith(inputFile.getName())).collect(Collectors.toList());
				for (final File witness : witnesses) {
					rtr.add(new UltimateRunDefinition(new File[] { inputFile, witness }, settingsFile, toolchainFile));
				}
			}
		}
		return rtr;
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String[] directories, final String[] fileEndings, final String settings, final String toolchain,
			final String witnessFolder, final int offset, final int limit) {
		return getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(toolchain, settings,
				Arrays.stream(directories).map(a -> new DirectoryFileEndingsPair(a, fileEndings, offset, limit))
						.toArray(size -> new DirectoryFileEndingsPair[size]),
				witnessFolder);
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String[] directories, final String[] fileEndings, final String settings, final String toolchain,
			final String witnessFolder) {
		return getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(directories, fileEndings, settings, toolchain,
				witnessFolder, 0, -1);
	}
}
