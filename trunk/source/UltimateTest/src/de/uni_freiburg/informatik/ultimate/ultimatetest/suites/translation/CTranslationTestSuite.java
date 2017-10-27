/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.translation;

import java.io.File;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CTranslationTestSuite extends AbstractEvalTestSuite {

	private static final String[] ALL_C = new String[] { ".c", ".i" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	// @formatter:off

	@SuppressWarnings("unchecked")
	private static final String[] TOOLCHAINS = new String[] {
			"CTranslationTest.xml","CTranslationBETest.xml"
	};

	private static final String[] INPUT = new String[] {
//			 "examples/svcomp/",
			 "examples/CToBoogieTranslation/ClassCast.c", //#100
			 "examples/CToBoogieTranslation/RValueArrayType.c", //#59
			 "examples/CToBoogieTranslation/Stackoverflow.c", //#61
			 "examples/CToBoogieTranslation/MultidimensionalArrays.c", //#58
			 "examples/CToBoogieTranslation/innerouterAssertionError.c", //#68
			 "examples/CToBoogieTranslation/floatToInt.c", //#65
			 "examples/CToBoogieTranslation/unnamedFieldInStruct.c", //#69

	};

	// @formatter:on

	@Override
	protected long getTimeout() {
		return 60 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Total time", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new TranslationTestResultDecider(urd.selectPrimaryInputFile());
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		final String[] settingsDirs = { "default/automizer", "translation" };
		final LinkedHashSet<File> settingsFiles = new LinkedHashSet<>();
		for (final String settingsDir : settingsDirs) {
			final File dirFile = UltimateRunDefinitionGenerator.getFileFromSettingsDir(settingsDir);
			settingsFiles.addAll(TestUtil.getFiles(dirFile, "epf"));
		}

		final List<String> settingsFileNames = settingsFiles.stream().map(a -> a.getAbsolutePath())
				.map(TestUtil::removeTrunkSettingsPrefix).collect(Collectors.toList());

		for (final String toolchain : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], ALL_C, DEFAULT_LIMIT);
			}

			for (final String setting : settingsFileNames) {
				addTestCase(toolchain, setting, pairs);
			}
		}
		return super.createTestCases();
	}

}
