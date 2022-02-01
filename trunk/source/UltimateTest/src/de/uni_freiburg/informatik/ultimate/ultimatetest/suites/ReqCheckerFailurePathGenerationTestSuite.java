/*
 * Copyright (C) 2020 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Regression Test Library.
 *
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Regression Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Formatter;
import java.util.List;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.PatternUtil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.preferences.PeaExampleGeneratorPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoErrorTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Regression tests for Requirements Checker.
 *
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class ReqCheckerFailurePathGenerationTestSuite extends AbstractEvalTestSuite {

	@Override
	protected long getTimeout() {
		return 1000_000;
	}

	private static final String TOOLCHAIN = "ReqCheckFailurePathGeneration.xml";
	private static final String SETTINGS = "default/reqcheck/ReqCheck-ReqToTest.epf";
	private static final String REQ_DIR = "examples/Requirements/failure-paths";
	private static final String IMG_DIR = "/img";

	private static final String[] REQ = new String[] { ".req" };
	private static final String LINE_SEP = CoreUtil.getPlatformLineSeparator();

	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition ultimateRunDefinition) {
		return new NoErrorTestResultDecider(ultimateRunDefinition);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		createReqFiles(PatternUtil.createAllPatterns(true).getFirst());
		addTestCase(TOOLCHAIN, SETTINGS, new DirectoryFileEndingsPair[] { new DirectoryFileEndingsPair(REQ_DIR, REQ) },
				this::overwriteSettings);
		return super.createTestCases();
	}

	private IUltimateServiceProvider overwriteSettings(final IUltimateServiceProvider services) {

		final String peaExGeneratorId =
				de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.Activator.PLUGIN_ID;

		final String absPathReqDir = TestUtil.getPathFromTrunk(REQ_DIR + IMG_DIR);
		final String absPathPythonScript =
				TestUtil.getPathFromTrunk("../releaseScripts/default/adds/timing_diagram.py");

		final IUltimateServiceProvider overlay = services.registerPreferenceLayer(getClass(), peaExGeneratorId);
		final IPreferenceProvider prefProvider = overlay.getPreferenceProvider(peaExGeneratorId);
		prefProvider.put(PeaExampleGeneratorPreferenceInitializer.LABEL_OUTPUT_DIRECTORY, absPathReqDir);
		prefProvider.put(PeaExampleGeneratorPreferenceInitializer.LABEL_PYTHON_SCRIPT, absPathPythonScript);

		return overlay;
	}

	private static void createReqFiles(final List<? extends PatternType<?>> patterns) {
		final File absPathReqDir = new File(TestUtil.createPathFromTrunk(REQ_DIR));
		final File absPathImgDir = new File(TestUtil.createPathFromTrunk(REQ_DIR + IMG_DIR));
		assert absPathImgDir.isDirectory() || absPathImgDir.mkdirs() : "Failed to create directory: " + absPathImgDir;
		Stream.of(absPathReqDir.listFiles()).filter(a -> a.getName().endsWith(".req")).forEach(a -> a.delete());
		Stream.of(absPathImgDir.listFiles()).filter(a -> a.getName().endsWith(".svg")).forEach(a -> a.delete());

		for (final PatternType<?> pattern : patterns) {
			final File file = Paths.get(absPathReqDir.getAbsolutePath(),
					pattern.getName() + "_" + pattern.getScope().getName() + ".req").toFile();

			final CDD[] cdds = pattern.getCddsAsArray();
			final CDD[] scopeCdds = new CDD[] { pattern.getScope().getCdd1(), pattern.getScope().getCdd2() };

			final Formatter fmt = new Formatter();
			fmt.format("// %s %s%s", pattern.getName(), pattern.getScope().getName(), LINE_SEP);
			for (final CDD cdd : scopeCdds) {
				if (cdd != null) {
					fmt.format("INPUT %s is bool%s", cdd, LINE_SEP);
				}
			}
			for (int i = 0; i < cdds.length; i++) {
				fmt.format("%s %s is bool%s", i == 0 ? "OUTPUT" : "INPUT", cdds[i], LINE_SEP);
			}
			fmt.format("req1: %s%s", pattern.toString().replace(pattern.getId() + ": ", ""), LINE_SEP);

			try {
				final BufferedWriter writer = new BufferedWriter(new FileWriter(file, false));
				writer.write(fmt.toString());
				writer.close();
			} catch (final IOException e) {
				throw new RuntimeException(e.getMessage());
			} finally {
				fmt.close();
			}
		}
	}

}
