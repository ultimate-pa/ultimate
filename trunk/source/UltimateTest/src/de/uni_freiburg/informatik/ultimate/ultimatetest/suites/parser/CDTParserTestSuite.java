/*
 * Copyright (C) 2023 Manuel Bentele
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.parser;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.cdt.parser.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractParserTestSuite;

/**
 * Test suite for the CDTParser to test parsing of C projects.
 * 
 * @author Manuel Bentele
 */
public class CDTParserTestSuite extends AbstractParserTestSuite {

	private static final String[] ALL_C = new String[] { ".c" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	/**
	 * Relative path to the standard test include directory starting from trunk.
	 */
	// @formatter:off
	private static final String[] INCLUDE_STD_DIR = new String[] {
			"examples/CParser/include"
	};
	// @formatter:on

	/**
	 * Relative path to the extended test include directories starting from trunk.
	 */
	// @formatter:off
	private static final String[] INCLUDE_EXD_DIRS = new String[] {
			"examples/CParser/include",
			"examples/CParser/include/subdirectory"
	};
	// @formatter:on

	/**
	 * List of toolchains on which CDT parser test cases should be executed.
	 */
	// @formatter:off
	private static final String[] TOOLCHAINS = new String[] {
			"CTranslationAndBoogiePreprocessor.xml"
	};
	// @formatter:on

	@Override
	protected long getTimeout() {
		return 10 * 1000;
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		// @formatter:off
		/**
		 * Test program includes local header files that are located in the same directory as the program itself.
		 */
		addParserTestCase("examples/CParser/includeHeadersLocal.c");
		/**
		 * Test program includes header files that are located in the specified {@link INCLUDE_STD_DIR}.
		 */
		addParserTestCase("examples/CParser/includeHeadersNonRecursiveSimple.c",       false, INCLUDE_STD_DIR);
		/**
		 * Test program includes header files that are located in the specified {@link INCLUDE_EXD_DIRS}. This test
		 * case corresponds to the command call 'gcc -I ${INCLUDE_EXD_DIRS[0]} -I ${INCLUDE_EXD_DIRS[1]} ...'.
		 */
		addParserTestCase("examples/CParser/includeHeadersNonRecursiveSubdirectory.c", false, INCLUDE_EXD_DIRS);
		/**
		 * Test program includes header files that are located in the specified include directory and its
		 * subdirectories. This test case corresponds to the command call 'gcc -I ${INCLUDE_STD_DIR[0]} ...'.
		 */
		addParserTestCase("examples/CParser/includeHeadersRecursive.c",                true,  INCLUDE_STD_DIR);
		// @formatter:on

		return super.createTestCases();
	}

	/**
	 * Add simple CDT parser test case for an input C-file.
	 * 
	 * The test case commands the CDT implementation to parse the input C-file while the parser does not consider any
	 * include paths and their recursive header file search.
	 * 
	 * @param inputFilename
	 *            Relative file name to the input C-file starting from trunk.
	 */
	protected void addParserTestCase(final String inputFilename) {
		addParserTestCase(inputFilename, false, new String[] {});
	}

	/**
	 * Add CDT parser test case for an input C-file while considering include paths and their recursive header file
	 * search.
	 * 
	 * The test case commands the CDT implementation to parse the input C-file while the parser considers the specified
	 * include paths and their recursive header file search.
	 * 
	 * @param inputFilename
	 *            Relative file name to the input file starting from trunk.
	 * @param recursive
	 *            Add include files recursively from subdirectories of include paths for parsing as well.
	 * @param includeDirectories
	 *            List of include paths that will be parsed with the given input C-file.
	 */
	protected void addParserTestCase(final String inputFilename, final boolean recursive,
			final String[] includeDirectories) {

		// determine absolute file paths of include paths
		final String[] absolutePathsIncDirs = Arrays.stream(includeDirectories).map(includeDir -> {
			final File includeDirectoryFile = UltimateRunDefinitionGenerator.getFileFromTrunkDir(includeDir);
			return includeDirectoryFile.getAbsolutePath().toString();
		}).toArray(String[]::new);

		// define function to dynamically customize CDT parser settings for each test case
		final Function<IUltimateServiceProvider, IUltimateServiceProvider> customizeCdtParserSettings = services -> {
			final String cdtParserPluginId = de.uni_freiburg.informatik.ultimate.cdt.parser.Activator.PLUGIN_ID;
			final IUltimateServiceProvider overlay = services.registerPreferenceLayer(getClass(), cdtParserPluginId);
			final IPreferenceProvider prefProvider = overlay.getPreferenceProvider(cdtParserPluginId);

			final String includePaths = String.join(File.pathSeparator, absolutePathsIncDirs);

			prefProvider.put(PreferenceInitializer.INCLUDE_PATHS, includePaths);
			prefProvider.put(PreferenceInitializer.RECURSIVE, recursive);

			return overlay;
		};

		// add test case with customized CDT parser settings (include paths, etc.) for all toolchains
		for (final String toolchain : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] inputFiles =
					{ new DirectoryFileEndingsPair(inputFilename, ALL_C, DEFAULT_LIMIT) };
			addTestCase(toolchain, null, inputFiles, customizeCdtParserSettings);
		}
	}
}
