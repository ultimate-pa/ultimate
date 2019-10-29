package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.util.Collection;
import java.util.Comparator;
import java.util.Formatter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfter;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeAfterUntil;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBefore;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeBetween;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScopeGlobally;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternScopeNotImplemented;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Dumps {@link PatternType} to dot and markdown files used in hanfor
 * documentation.
 *
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
@RunWith(Parameterized.class)
public class PeaToDotTestSuite {

	private static final File ROOT_DIR = new File("/media/ubuntu/Daten/Projects/hanfor/documentation/docs");
	private static final File MARKDOWN_DIR = new File(ROOT_DIR + "/usage/patterns");

	private static final String IMAGE_DIR_RELATIVE = "/img/patterns";
	private static final File IMAGE_DIR = new File(ROOT_DIR + IMAGE_DIR_RELATIVE);

	private static final String LINE_SEP = System.lineSeparator();

	private final IUltimateServiceProvider mServiceProvider;
	private final ILogger mLogger;

	private final PatternType mPattern;
	private final String mPatternName;
	private final String mPatternString;
	private final String mScopeName;
	private final Map<String, Integer> mDurationToBounds;

	public PeaToDotTestSuite(final PatternType pattern, final Map<String, Integer> durationToBounds) {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("");

		mDurationToBounds = durationToBounds;
		mPattern = pattern;
		mPatternName = pattern.getClass().getSimpleName();
		mPatternString = pattern.toString().replace(pattern.getId() + ": ", "");

		final String scopeName = pattern.getScope().getClass().getSimpleName();
		final String scopePrefix = pattern.getScope().getClass().getSuperclass().getSimpleName();
		mScopeName = scopeName.replace(scopePrefix, "");
	}

	@Test
	public void testDot() throws IOException, InterruptedException {
		final PhaseEventAutomata pea;
		final CounterTrace counterTrace;

		try {
			pea = mPattern.transformToPea(mLogger, mDurationToBounds);
			counterTrace = mPattern.constructCounterTrace(mDurationToBounds);
		} catch (final PatternScopeNotImplemented e) {
			return; // Oops, somebody forgot to implement that sh.. ;-)
		}

		mLogger.info(DotWriterNew.createDotString(pea));

		writeSvgFile(DotWriterNew.createDotString(pea));
		writeMarkdownFile(counterTrace.toString());
	}

	private void writeSvgFile(final String dot) throws IOException, InterruptedException {
		final File file = new File(IMAGE_DIR + "/" + mPatternName + "_" + mScopeName + ".svg");
		mLogger.info(file.toString());
		final String[] command = new String[] { "dot", "-Tsvg", "-o", file.toString() };

		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServiceProvider);
		final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
		writer.write(dot.toString());
		writer.close();

		process.waitfor();
	}

	private void writeMarkdownFile(final String counterTrace) throws IOException {
		final File file = new File(MARKDOWN_DIR + "/" + mPatternName + ".md");
		final StringBuilder stringBuilder = new StringBuilder();
		final Formatter fmt = new Formatter(stringBuilder);

		if (!file.exists()) {
			fmt.format("toc_depth: 2%s%s", LINE_SEP, LINE_SEP);
			fmt.format("<!-- Auto generated file, do not make changes here. -->%s%s", LINE_SEP, LINE_SEP);
		}

		fmt.format("## %s %s%s", mPatternName, mScopeName, LINE_SEP);
		fmt.format("```%s%s%s```%s", LINE_SEP, mPatternString, LINE_SEP, LINE_SEP);
		fmt.format("```%s%s%s```%s", LINE_SEP, counterTrace, LINE_SEP, LINE_SEP);
		fmt.format("![](%s/%s_%s.svg)%s", IMAGE_DIR_RELATIVE, mPatternName, mScopeName, LINE_SEP);
		fmt.close();

		final BufferedWriter writer = new BufferedWriter(new FileWriter(file, true));
		writer.write(stringBuilder.toString());
		writer.close();
	}

	@BeforeClass
	public static void beforeClass() throws IOException {
		// Check if root directory exists.
		assert (Files.isDirectory(ROOT_DIR.toPath())) : "Directory not found: " + ROOT_DIR;

		// Check if parent directories exist.
		assert (IMAGE_DIR.getParentFile().isDirectory()) : "Directory not found: " + IMAGE_DIR.getParentFile();
		assert (MARKDOWN_DIR.getParentFile().isDirectory()) : "Directory not found: " + MARKDOWN_DIR.getParentFile();

		// Check if markdown, image directory exist, otherwise create them.
		assert (IMAGE_DIR.isDirectory() || IMAGE_DIR.mkdir()) : "Failed to create directory: " + IMAGE_DIR;
		assert (MARKDOWN_DIR.isDirectory() || MARKDOWN_DIR.mkdir()) : "Failed to create directory: " + MARKDOWN_DIR;

		// Delete auto generated files.
		Stream.of(IMAGE_DIR.listFiles()).filter(a -> a.getName().endsWith(".svg")).forEach(a -> a.delete());
		Stream.of(MARKDOWN_DIR.listFiles()).filter(a -> a.getName().endsWith(".md")).forEach(a -> a.delete());
	}

	@AfterClass
	public static void afterClass() throws IOException {

	}

	@Parameters()
	public static Collection<Object[]> data() {
		final Pair<List<PatternType>, Map<String, Integer>> pair = PatternUtil.createAllPatterns();

		return pair.getFirst().stream().sorted(new PatternNameComparator())
				.map(a -> new Object[] { a, pair.getSecond() }).collect(Collectors.toList());
	}

	private static final class PatternNameComparator implements Comparator<PatternType> {
		private static final Map<Class<? extends SrParseScope>, Integer> SCOPE_ORDER = new HashMap<>();

		static {
			SCOPE_ORDER.put(SrParseScopeGlobally.class, 0);
			SCOPE_ORDER.put(SrParseScopeBefore.class, 1);
			SCOPE_ORDER.put(SrParseScopeAfter.class, 2);
			SCOPE_ORDER.put(SrParseScopeBetween.class, 3);
			SCOPE_ORDER.put(SrParseScopeAfterUntil.class, 4);
		}

		@Override
		public int compare(final PatternType lhs, final PatternType rhs) {
			final int order = lhs.getClass().getSimpleName().compareTo(rhs.getClass().getSimpleName());

			if (order != 0) {
				return order;
			}

			return SCOPE_ORDER.get(lhs.getScope().getClass()) - SCOPE_ORDER.get(rhs.getScope().getClass());
		}
	}
}
