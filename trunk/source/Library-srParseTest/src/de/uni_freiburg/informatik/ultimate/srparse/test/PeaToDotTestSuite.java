package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.junit.AfterClass;
import org.junit.BeforeClass;
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

@RunWith(Parameterized.class)
public class PeaToDotTestSuite {

	private static final String ROOT_DIR = "/media/ubuntu/Daten/Projects/hanfor/documentation/docs/";
	// private static final String ROOT_DIR = "F:/repos/hanfor/documentation/docs/";
	private static final String MARKDOWN_DIR = "usage/patterns/";
	private static final String IMAGE_DIR = "img/patterns/";

	private final IUltimateServiceProvider mServiceProvider;
	private final ILogger mLogger;
	private final PatternType mPattern;
	private final Map<String, Integer> mDurationToBounds;
	private final String mName;
	private final String mScope;

	public PeaToDotTestSuite(final PatternType pattern, final Map<String, Integer> durationToBounds) {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO);
		mLogger = mServiceProvider.getLoggingService().getLogger("");

		mPattern = pattern;
		mDurationToBounds = durationToBounds;
		mName = pattern.getClass().getSimpleName();

		final Class<?> scope = pattern.getScope().getClass();
		mScope = scope.getSimpleName().replace(scope.getSuperclass().getSimpleName(), "");
	}

	// @Test
	public void testDot() throws IOException, InterruptedException {
		final PhaseEventAutomata pea;
		final CounterTrace counterTrace;
		try {
			pea = mPattern.transformToPea(mLogger, mDurationToBounds);
			counterTrace = mPattern.constructCounterTrace(mDurationToBounds);
		} catch (final PatternScopeNotImplemented e) {
			return; // Oops, somebody forgot to implement that sh.. ;-)
		}

		// mLogger.info(DotWriterNew.createDotString(pea));
		// mLogger.info(counterTrace.toString());

		writeDotToSvg(DotWriterNew.createDotString(pea));
		writeMarkdown(counterTrace.toString());
	}

	private void writeDotToSvg(final StringBuilder dot) throws IOException, InterruptedException {
		final File file = new File(ROOT_DIR + IMAGE_DIR + mName + "_" + mScope + ".svg");
		final String[] command = new String[] { "dot", "-Tsvg", "-o", file.toString() };

		final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServiceProvider);
		final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
		writer.write(dot.toString());
		writer.close();

		process.waitfor();
	}

	private void writeMarkdown(final String counterTrace) throws IOException {
		final File file = new File(ROOT_DIR + MARKDOWN_DIR + mName + ".md");
		final StringBuilder markdown = new StringBuilder();

		if (!file.exists()) {
			markdown.append("toc_depth: 2" + "\n\n");
		}

		markdown.append("## " + mName + " " + mScope + "\n");
		markdown.append("```" + "\n" + mPattern.toString().replace(mPattern.getId() + ": ", "") + "\n" + "```" + "\n");
		markdown.append("```" + "\n" + counterTrace + "\n" + "```" + "\n");
		markdown.append("![](/" + IMAGE_DIR + mName + "_" + mScope + ".svg)" + "\n\n");

		final BufferedWriter writer = new BufferedWriter(new FileWriter(file, true));
		writer.write(markdown.toString());
		writer.close();
	}

	@BeforeClass
	public static void beforeClass() throws IOException {
		// Check if root directory exists.
		assert (Files.isDirectory(Paths.get(ROOT_DIR))) : "Directory not found: '" + ROOT_DIR + "'";

		final File image_dir = new File(ROOT_DIR + IMAGE_DIR);
		final File markdown_dir = new File(ROOT_DIR + MARKDOWN_DIR);

		// Check if parent directories exist.
		assert (image_dir.getParentFile().isDirectory()) : "Directory not found: '" + image_dir.getParentFile() + "'";
		assert (markdown_dir.getParentFile().isDirectory()) : "Directory not found: '" + markdown_dir.getParentFile()
				+ "'";

		// Check if markdown, image directory exist. If not create them.
		assert (image_dir.isDirectory() || image_dir.mkdir()) : "Could not create directory: '" + image_dir + "'";
		assert (markdown_dir.isDirectory() || markdown_dir.mkdir()) : "Could not create directory: '" + markdown_dir
				+ "'";

		// Delete auto-generated markdown and image files.
		Stream.of(markdown_dir.listFiles()).filter(a -> a.getName().endsWith(".md")).forEach(a -> a.delete());
		Stream.of(image_dir.listFiles()).filter(a -> a.getName().endsWith(".svg")).forEach(a -> a.delete());
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
