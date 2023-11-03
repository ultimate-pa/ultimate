/*
 * Copyright (C) 2014-2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import com.amihaiemil.eoyaml.Yaml;
import com.amihaiemil.eoyaml.YamlInput;
import com.amihaiemil.eoyaml.YamlMapping;
import com.amihaiemil.eoyaml.YamlNode;
import com.amihaiemil.eoyaml.YamlSequence;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class UltimateRunDefinitionGenerator {

	private static final String SETTINGS_PATH = "examples/settings/";
	private static final String TOOLCHAIN_PATH = "examples/toolchains/";

	private enum SvcompArchitecture { ILP32, LP64 };

	private UltimateRunDefinitionGenerator() {
		// do not instantiate utility class
	}

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
	private static Collection<File> getInputFiles(final File directory, final String[] fileEndings, final int offset,
			final int n) {
		return TestUtil.limitFiles(TestUtil.getFiles(directory, fileEndings), offset, n);
	}

	/**
	 * Get input files from directory. Do not take all files but only up to n pseudorandomly selected files.
	 */
	private static Collection<File> getInputFilesRegex(final File directory, final String[] regexes, final int offset,
			final int n) {
		return TestUtil.limitFiles(TestUtil.getFilesRegex(directory, regexes), offset, n);
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
	 * @param timelimit
	 *            A timelimit in ms.
	 */
	public static UltimateRunDefinition getRunDefinitionFromTrunk(final String input, final String settings,
			final String toolchain, final long timelimit) {
		return new UltimateRunDefinition(getFileFromTrunkDir(input),
				settings == null ? null : getFileFromSettingsDir(settings), getFileFromToolchainDir(toolchain),
				timelimit);
	}

	/**
	 * Get a {@link Collection} of {@link UltimateRunDefinition}s where for each directory in <code>directories</code>
	 * all files with a file ending from <code>fileEndings</code> define a run definition with the settings file
	 * <code>settings</code> and the toolchain file <code>toolchain</code>. All files are defined by their paths
	 * relative to the Ultimate trunk directory.
	 *
	 * @param timeout
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String[] directories,
			final String[] fileEndings, final String settings, final String toolchain, final long timeout) {
		return getRunDefinitionFromTrunk(directories, fileEndings, settings, toolchain, timeout, 0, -1);
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
			final String[] fileEndings, final String settings, final String toolchain, final long timeout,
			final int offset, final int limit) {
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);
		return Arrays.stream(directories).map(a -> getFileFromTrunkDir(a))
				.map(a -> getInputFiles(a, fileEndings, offset, limit)).flatMap(a -> a.stream()).distinct()
				.map(a -> new UltimateRunDefinition(a, settingsFile, toolchainFile, timeout))
				.collect(Collectors.toList());
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionsFromTrunkRegex(final String[] directories,
			final String[] regexes, final String settings[], final String toolchain, final long timeout,
			final int offset, final int limit) {
		final List<UltimateRunDefinition> result = new ArrayList<>();
		for (final String directory : directories) {
			final File toolchainFile = getFileFromToolchainDir(toolchain);
			for (final File dirFile : getInputFilesRegex(getFileFromTrunkDir(directory), regexes, offset, limit)) {
				for (final String setting : settings) {
					final File settingsFile = settings == null ? null : getFileFromSettingsDir(setting);
					result.add(new UltimateRunDefinition(dirFile, settingsFile, toolchainFile, timeout));
				}
			}
		}
		return result;
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunk(final String toolchain,
			final String settings, final DirectoryFileEndingsPair[] directoryFileEndingsPairs, final long timeout) {
		return Arrays.stream(directoryFileEndingsPairs)
				.map(a -> UltimateRunDefinitionGenerator.getRunDefinitionFromTrunk(new String[] { a.getDirectory() },
						a.getFileEndings(), settings, toolchain, timeout, a.getOffset(), a.getLimit()))
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
			final String[] fileEndings, final String settings, final String toolchain, final long timeout) {
		return getRunDefinitionFromTrunkWithWitnesses(directories, fileEndings, settings, toolchain, timeout, 0, -1);
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
			final String[] fileEndings, final String settings, final String toolchain, final long timeout,
			final int offset, final int limit) {
		return getRunDefinitionFromTrunkWithWitnesses(toolchain, settings,
				Arrays.stream(directories).map(a -> new DirectoryFileEndingsPair(a, fileEndings, offset, limit))
						.toArray(size -> new DirectoryFileEndingsPair[size]),
				timeout);
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnesses(final String toolchain,
			final String settings, final DirectoryFileEndingsPair[] directoryFileEndingsPairs, final long timelimit) {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);
		final File settingsFile = settings == null ? null : getFileFromSettingsDir(settings);

		for (final DirectoryFileEndingsPair pair : directoryFileEndingsPairs) {
			final File dir = getFileFromTrunkDir(pair.getDirectory());
			final Collection<File> inputFiles =
					getInputFiles(dir, pair.getFileEndings(), pair.getOffset(), pair.getLimit());
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
					rtr.add(new UltimateRunDefinition(new File[] { inputFile, witness }, settingsFile, toolchainFile,
							timelimit));
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
	 *
	 * @param timelimit
	 */
	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String toolchain, final String settings, final DirectoryFileEndingsPair[] input,
			final String witnessFolder, final long timelimit) {
		final Collection<UltimateRunDefinition> rtr = new ArrayList<>();
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
			final Collection<File> inputFiles =
					getInputFiles(dir, pair.getFileEndings(), pair.getOffset(), pair.getLimit());

			for (final File inputFile : inputFiles) {
				final List<File> witnesses = witnessCandidates.stream()
						.filter(a -> a.getName().startsWith(inputFile.getName())).collect(Collectors.toList());
				for (final File witness : witnesses) {
					rtr.add(new UltimateRunDefinition(new File[] { inputFile, witness }, settingsFile, toolchainFile,
							timelimit));
				}
			}
		}
		return rtr;
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String[] directories, final String[] fileEndings, final String settings, final String toolchain,
			final String witnessFolder, final long timeout, final int offset, final int limit) {
		return getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(toolchain, settings,
				Arrays.stream(directories).map(a -> new DirectoryFileEndingsPair(a, fileEndings, offset, limit))
						.toArray(size -> new DirectoryFileEndingsPair[size]),
				witnessFolder, timeout);
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(
			final String[] directories, final String[] fileEndings, final String settings, final String toolchain,
			final String witnessFolder, final long timeout) {
		return getRunDefinitionFromTrunkWithWitnessesFromSomeFolder(directories, fileEndings, settings, toolchain,
				witnessFolder, timeout, 0, -1);
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionsFromSvcompYamlWithWitnesses(
			final SvcompFolderSubset sfs, final Pair<String, String> settingsPair[], final String toolchain,
			final long timeout) {
		final List<UltimateRunDefinition> result = new ArrayList<>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);

		final File dir = getFileFromTrunkDir(sfs.getDirectory());
		final Map<File, SvcompArchitecture> inputFileToArchitecture =
				getInputFilesFromYamlFiles(TestUtil.getFiles(dir, ".yml"), sfs.getProperty(), sfs.getExpectedResult());
		final List<File[]> sourceAndWitnesses = new ArrayList<>();
		for (final File witness : TestUtil.getFiles(dir, ".graphml", ".yaml")) {
			for (final File source : inputFileToArchitecture.keySet()) {
				if (witness.getPath().startsWith(source.getPath())) {
					sourceAndWitnesses.add(new File[] { source, witness });
					break;
				}
			}
		}
		final Collection<File[]> inputFiles = TestUtil.limitFiles(sourceAndWitnesses, sfs.getOffset(), sfs.getLimit());

		for (final File[] input : inputFiles) {
			for (final Pair<String, String> settingPair : settingsPair) {
				final File settingsFile = selectSetting(settingPair, inputFileToArchitecture.get(input[0]));
				result.add(new UltimateRunDefinition(input, settingsFile, toolchainFile, timeout));
			}
		}
		return result;
	}

	public static Collection<UltimateRunDefinition> getRunDefinitionsFromSvcompYaml(final SvcompFolderSubset sfs,
			final Pair<String, String> settingsPair[], final String toolchain, final long timeout) {
		final List<UltimateRunDefinition> result = new ArrayList<>();
		final File toolchainFile = getFileFromToolchainDir(toolchain);

		final Collection<File> selectedYamlFiles =
				TestUtil.getFilesRegex(getFileFromTrunkDir(sfs.getDirectory()), new String[] { ".*\\.yml" });
		final Map<File, SvcompArchitecture> inputFileToArchitecture =
				getInputFilesFromYamlFiles(selectedYamlFiles, sfs.getProperty(), sfs.getExpectedResult());
		final Collection<File> inputFiles =
				TestUtil.limitFiles(inputFileToArchitecture.keySet(), sfs.getOffset(), sfs.getLimit());

		for (final File input : inputFiles) {
			for (final Pair<String, String> settingPair : settingsPair) {
				final File settingsFile = selectSetting(settingPair, inputFileToArchitecture.get(input));
				result.add(new UltimateRunDefinition(input, settingsFile, toolchainFile, timeout));
			}
		}
		return result;
	}

	private static File selectSetting(final Pair<String, String> settingPair, final SvcompArchitecture architecture) {
		final String setting;
		switch (architecture) {
		case ILP32:
			setting = settingPair.getFirst();
			break;
		case LP64:
			setting = settingPair.getSecond();
			break;
		default:
			throw new AssertionError();
		}
		return getFileFromSettingsDir(setting);
	}

	private static Map<File, SvcompArchitecture> getInputFilesFromYamlFiles(final Collection<File> selectedYamlFiles,
			final String property, final Boolean expectedResult) {
		final Map<File, SvcompArchitecture> result = new HashMap<>();
		for (final File yamlFile : selectedYamlFiles) {
			try {
				final Pair<File, SvcompArchitecture> inputFile =
						getInputFileFromYamlFile(yamlFile, property, expectedResult);
				if (inputFile != null) {
					result.put(inputFile.getFirst(), inputFile.getSecond());
				}
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
		return result;
	}

	private static Pair<File, SvcompArchitecture> getInputFileFromYamlFile(final File yamlFile,
			final String propertyFile, final Boolean expectedResult) throws IOException {
		final YamlInput yamlInput = Yaml.createYamlInput(yamlFile);
		final YamlMapping rootMapping = yamlInput.readYamlMapping();
		if (hasProperty(rootMapping, propertyFile, expectedResult)) {
			final String cFilename = rootMapping.string("input_files");
			final String filename = yamlFile.getParent() + System.getProperty("file.separator") + cFilename;
			final YamlMapping optionsMapping = rootMapping.yamlMapping("options");
			final String architectureString = optionsMapping.string("data_model");
			final SvcompArchitecture architecture = SvcompArchitecture.valueOf(architectureString);
			return new Pair<>(new File(filename), architecture);
		}
		return null;
	}

	private static boolean hasProperty(final YamlMapping rootMapping, final String propertyFile,
			final Boolean expectedResult) {
		final YamlSequence propertySequence = rootMapping.yamlSequence("properties");
		for (final YamlNode propertyNode : propertySequence) {
			final YamlMapping yamlMapForPropery = propertyNode.asMapping();
			final String prp = yamlMapForPropery.string("property_file");
			if (prp.endsWith(propertyFile)) {
				if (expectedResult == null) {
					return true;
				}
				final String expectedVerdict = yamlMapForPropery.string("expected_verdict");
				return (Boolean.valueOf(expectedVerdict) == expectedResult);
			}
		}
		return false;
	}
}
