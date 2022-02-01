/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Formatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DotWriterNew;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.PatternUtil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternScopeNotImplemented;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Dumps {@link PatternType} to dot and markdown files used in hanfor documentation.
 *
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 */
@RunWith(Parameterized.class)
public class PeaToDotTestSuite {
	// Set to true, if you want to create new svg and markdown files for the hanfor documentation.
	private static final boolean CREATE_NEW_FILES = false;

	private static final File ROOT_DIR = new File("/mnt/Data/Developement/hanfor/documentation");
	private static final File DOCS_DIR = new File(ROOT_DIR + "/docs");
	private static final File MARKDOWN_DIR = new File(ROOT_DIR + "/includes/patterns");
	private static final File PEA_IMAGE_DIR = new File(DOCS_DIR + "/img/patterns");
	private static final File POS_FAILURE_IMAGE_DIR = new File(DOCS_DIR + "/img/failure_paths/positive");
	private static final File NEG_FAILURE_IMAGE_DIR = new File(DOCS_DIR + "/img/failure_paths/negative");
	private static final File ULTIMATE_REVISION_FILE = new File(MARKDOWN_DIR + "/ultimate_revision.txt");

	private static final String LINE_SEP = CoreUtil.getPlatformLineSeparator();

	private final IUltimateServiceProvider mServiceProvider;
	private final ILogger mLogger;

	private final PatternType<?> mPattern;
	private final String mPatternName;
	private final String mPatternString;
	private final String mScopeName;
	private final Durations mDurations;

	public PeaToDotTestSuite(final PatternType<?> pattern, final Durations durations) {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("");

		mDurations = durations;
		mPattern = pattern;
		mPatternName = pattern.getClass().getSimpleName();
		mPatternString = pattern.toString().replace(pattern.getId() + ": ", "");
		mScopeName = pattern.getScope().getClass().getSimpleName()
				.replace(pattern.getScope().getClass().getSuperclass().getSimpleName(), "");
	}

	@Test
	public void testDot() throws IOException, InterruptedException {

		if (!CREATE_NEW_FILES || mPatternName.equals("BndEntryConditionPattern")) {
			return;
		}
		
		// Do not add deprecated patterns to documentation.
		if (mPatternName.equals("BndEntryConditionPattern")) {
			return;
		}

		final ReqPeas reqPeas;
		try {
			reqPeas = mPattern.transformToPea(mLogger, mDurations);
		} catch (final PatternScopeNotImplemented e) {
			mLogger.fatal("Pattern not implemented: " + mPattern.getId());
			return; // Oops, somebody forgot to implement this
		}

		final List<Entry<CounterTrace, PhaseEventAutomata>> ctsToPea = reqPeas.getCounterTrace2Pea();
		for (final Entry<CounterTrace, PhaseEventAutomata> entry : ctsToPea) {
			writeSvgFile(DotWriterNew.createDotString(entry.getValue()));
		}
		writeMarkdownFile(ctsToPea.stream().map(e -> e.getKey().toString()).collect(Collectors.toList()));
	}

	private void writeSvgFile(final String dot) throws IOException, InterruptedException {

		final int numPea =
				PEA_IMAGE_DIR.listFiles((d, n) -> n.startsWith(mPatternName + "_" + mScopeName + "_")).length;

		final File file = new File(PEA_IMAGE_DIR + "/" + mPatternName + "_" + mScopeName + "_" + numPea + ".svg");

		final String[] command = new String[] { "dot", "-Tsvg", "-o", file.toString() };
		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServiceProvider);
		final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));

		writer.write(dot.toString());
		writer.close();

		final int returnCode = process.waitfor().getReturnCode();
		if (returnCode != 0) {
			throw new RuntimeException(String.format("%s did return %s. Stdout: %s Stderr: %s",
					Arrays.stream(command).collect(Collectors.joining(" ")), returnCode,
					CoreUtil.convertStreamToString(process.getInputStream()),
					CoreUtil.convertStreamToString(process.getErrorStream())));
		}
	}

	private void writeMarkdownFile(final List<String> cts) throws IOException {
		String patternNameShort = mPatternName.replaceAll("Pattern", "");
		final File markdownFile = new File(MARKDOWN_DIR + "/" + patternNameShort + ".md");
		final int numPea =
				PEA_IMAGE_DIR.listFiles((d, n) -> n.startsWith(mPatternName + "_" + mScopeName + "_")).length;
		final Formatter fmt = new Formatter();

		final File[] posFailureImages =
				POS_FAILURE_IMAGE_DIR.listFiles((d, n) -> n.startsWith(mPatternName + "_" + mScopeName + "_"));
		final File[] negFailureImages =
				NEG_FAILURE_IMAGE_DIR.listFiles((d, n) -> n.startsWith(mPatternName + "_" + mScopeName + "_"));

		if (!markdownFile.exists()) {
			fmt.format("<!-- Auto generated file, do not make any changes here. -->%s%s", LINE_SEP, LINE_SEP);
			
			fmt.format("## %s%s", patternNameShort, LINE_SEP);
		}
		fmt.format(LINE_SEP);

		fmt.format("### %s %s%s", patternNameShort, mScopeName, LINE_SEP);
		fmt.format("```%s%s%s```%s", LINE_SEP, mPatternString, LINE_SEP, LINE_SEP);
		fmt.format(LINE_SEP);

		fmt.format("#### Countertraces%s", LINE_SEP);
		fmt.format("```%s", LINE_SEP);
		fmt.format("%s", cts.stream().collect(Collectors.joining(LINE_SEP)));
		fmt.format("%s```%s", LINE_SEP, LINE_SEP);
		fmt.format(LINE_SEP);

		fmt.format("#### Phase Event Automata%s", LINE_SEP);
		assert (numPea == cts.size());
		for (int i = numPea; i > 0; i--) {
			fmt.format("![](../%s/%s_%s_%d.svg)%s", DOCS_DIR.toPath().relativize(PEA_IMAGE_DIR.toPath()), mPatternName,
					mScopeName, (numPea - i), LINE_SEP);
		}
		fmt.format(LINE_SEP);

		if (posFailureImages.length > 0) {
			fmt.format("??? Example \"Positive Examples: %s - %s\"%s", patternNameShort, mScopeName, LINE_SEP);
		}

		for (int i = 0; i < posFailureImages.length; i++) {
			String img = "";

			if (i < posFailureImages.length) {
				img = "    ![](../" + DOCS_DIR.toPath().relativize(POS_FAILURE_IMAGE_DIR.toPath()) + "/" + mPatternName
						+ "_" + mScopeName + "_" + String.valueOf(i) + ".svg){ loading=lazy width=47% align=left }";
			}

			fmt.format("%s", img, LINE_SEP);
			fmt.format(LINE_SEP);
		}

		// TODO: uncomment once negative failure paths examples are fixed
//		if (negFailureImages.length > 0) {
//			fmt.format("??? Example \"Negative Examples: %s - %s\"%s", patternNameShort, mScopeName, LINE_SEP);
//		}
//
//		for (int i = 0; i < negFailureImages.length; i++) {
//			String img = "";
//
//			if (i < posFailureImages.length) {
//				img = "    ![](../" + DOCS_DIR.toPath().relativize(NEG_FAILURE_IMAGE_DIR.toPath()) + "/" + mPatternName
//						+ "_" + mScopeName + "_" + String.valueOf(i) + ".svg){ loading=lazy width=47% align=left }";
//			}
//
//			fmt.format("%s", img, LINE_SEP);
//			fmt.format(LINE_SEP);
//		}
		fmt.format(LINE_SEP);

		final BufferedWriter writer = new BufferedWriter(new FileWriter(markdownFile, true));
		writer.write(fmt.toString());
		writer.close();
		fmt.close();
	}

	@BeforeClass
	public static void beforeClass() {
		if (!CREATE_NEW_FILES) {
			return;
		}

		// Check if root directory exists.
		assert Files.isDirectory(ROOT_DIR.toPath()) : "Directory not found: " + ROOT_DIR;

		// Check if markdown, pea image directory exist, otherwise create them.
		assert PEA_IMAGE_DIR.isDirectory() || PEA_IMAGE_DIR.mkdirs() : "Failed to create directory: " + PEA_IMAGE_DIR;
		assert MARKDOWN_DIR.isDirectory() || MARKDOWN_DIR.mkdirs() : "Failed to create directory: " + MARKDOWN_DIR;

		// Delete auto generated files.
		Stream.of(PEA_IMAGE_DIR.listFiles()).filter(a -> a.getName().endsWith(".svg")).forEach(a -> a.delete());
		Stream.of(MARKDOWN_DIR.listFiles()).filter(a -> a.getName().endsWith(".md")).forEach(a -> a.delete());
	}

	@AfterClass
	public static void afterClass() throws IOException {
		if (!CREATE_NEW_FILES) {
			return;
		}

		final Formatter fmt = new Formatter();
		fmt.format("<!-- Auto generated file, do not make any changes here. -->%s%s", LINE_SEP, LINE_SEP);

		if (ULTIMATE_REVISION_FILE.canRead()) {
			final BufferedReader reader = new BufferedReader(new FileReader(ULTIMATE_REVISION_FILE));
			final String ultimateRevision = reader.readLine();
			reader.close();

			// fmt.format("### Ultimate revision at GitHub%s", LINE_SEP);
			fmt.format("Ultimate revision on Github that corresponds to this documention: %s", LINE_SEP);
			fmt.format("[%s](https://github.com/ultimate-pa/ultimate/tree/%s \"%s\")%s%s", ultimateRevision,
					ultimateRevision, ultimateRevision, LINE_SEP, LINE_SEP);
		}

		final String markdownDir = ROOT_DIR.toPath().relativize(MARKDOWN_DIR.toPath()).toString();
		Arrays.stream(MARKDOWN_DIR.list()).filter(e -> e.endsWith(".md"))
				.forEach(e -> fmt.format("--8<-- \"%s/%s\"%s", markdownDir, e, LINE_SEP));

		final File file = new File(MARKDOWN_DIR + "/includeAllPatterns.md");
		final BufferedWriter writer = new BufferedWriter(new FileWriter(file));
		writer.write(fmt.toString());
		writer.close();
		fmt.close();
	}

	@Parameters()
	public static Collection<Object[]> data() {
		final Pair<List<? extends PatternType<?>>, Durations> pair = PatternUtil.createAllPatterns(false);

		return pair.getFirst().stream().sorted(new PatternNameComparator())
				.map(a -> new Object[] { a, pair.getSecond() }).collect(Collectors.toList());
	}

	private static final class PatternNameComparator implements Comparator<PatternType<?>> {
		private static final Map<Class<? extends SrParseScope<?>>, Integer> SCOPE_ORDER = new HashMap<>();

		static {
			SCOPE_ORDER.put(SrParseScopeGlobally.class, 0);
			SCOPE_ORDER.put(SrParseScopeBefore.class, 1);
			SCOPE_ORDER.put(SrParseScopeAfter.class, 2);
			SCOPE_ORDER.put(SrParseScopeBetween.class, 3);
			SCOPE_ORDER.put(SrParseScopeAfterUntil.class, 4);
		}

		@Override
		public int compare(final PatternType<?> lhs, final PatternType<?> rhs) {
			final int order = lhs.getClass().getSimpleName().compareTo(rhs.getClass().getSimpleName());

			if (order != 0) {
				return order;
			}

			return SCOPE_ORDER.get(lhs.getScope().getClass()) - SCOPE_ORDER.get(rhs.getScope().getClass());
		}
	}
}
