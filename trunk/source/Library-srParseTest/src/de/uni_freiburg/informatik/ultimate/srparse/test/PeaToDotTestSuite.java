package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DotWriterNew;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternScopeNotImplemented;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

@RunWith(Parameterized.class)
public class PeaToDotTestSuite {

	private static final String SCOPE_PREFIX = "SrParseScope";
	private static final String PATH = "/home/ubuntu/Desktop/Patterns/";

	private final IUltimateServiceProvider mServiceProvider;
	private final ILogger mLogger;
	private final PatternType mPattern;
	private final Map<String, Integer> mDuration2Bounds;
	private final String mName;

	public PeaToDotTestSuite(final PatternType pattern, final Map<String, Integer> duration2Bounds, final String name) {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServiceProvider.getLoggingService().getLogger("");
		mPattern = pattern;
		mDuration2Bounds = duration2Bounds;
		mName = name;
	}

	@Test
	public void testDot() throws IOException, InterruptedException {
		final String scope = mPattern.getScope().getClass().getSimpleName().replace(SCOPE_PREFIX, "");
		final String filename = PATH + mName + "_" + scope + ".dot";

		StringBuilder sb;
		try {
			final PhaseEventAutomata pea = mPattern.transformToPea(mLogger, mDuration2Bounds);
			sb = DotWriterNew.createDotString(pea);
		} catch (final PatternScopeNotImplemented e) {
			// Ooops, somebody forgot to implement that sh.. ;-)
			return;
		}

		final String formula = mPattern.toString().replace(mPattern.getId() + ": ", "");

		final MonitoredProcess mp = MonitoredProcess.exec(new String[] { "dot", "-c", "even more useful arguments" },
				null, null, mServiceProvider);
		final BufferedWriter dotWriter = new BufferedWriter(new OutputStreamWriter(mp.getOutputStream()));
		dotWriter.write(sb.toString());
		final MonitoredProcessState result = mp.waitfor();
		dotWriter.close();

	}

	@Parameters(name = "{2}")
	public static Collection<Object[]> data() {
		final Pair<List<PatternType>, Map<String, Integer>> pair = PatternUtil.createAllPatterns();
		return pair.getFirst().stream().map(a -> new Object[] { a, pair.getSecond(), a.getClass().getSimpleName() })
				.collect(Collectors.toList());
	}
}
