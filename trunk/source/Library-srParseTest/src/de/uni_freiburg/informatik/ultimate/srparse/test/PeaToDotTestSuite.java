package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

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

	private final IUltimateServiceProvider mServiceProvider;
	private final ILogger mLogger;
	private final PatternType mPattern;
	Map<String, Integer> mDuration2Bounds;
	String mName;

	public PeaToDotTestSuite(final PatternType pattern, final Map<String, Integer> duration2Bounds, final String name) {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServiceProvider.getLoggingService().getLogger("");
		mPattern = pattern;
		mDuration2Bounds = duration2Bounds;
		mName = name;
	}

	// @Test
	public void testDot() throws Exception {
		final String name = mPattern.getClass().getSimpleName();
		final String scope = mPattern.getScope().getClass().getSimpleName().replace("SrParseScope", "");
		final String filename = "/home/ubuntu/Desktop/Patterns/" + name + "_" + scope + ".dot";

		try {
			final PhaseEventAutomata pea = mPattern.transformToPea(mLogger, mDuration2Bounds);
			DotWriterNew.write(filename, true, pea, mLogger);
		} catch (final PatternScopeNotImplemented e) {

		}
	}

	@Parameters(name = "{2}")
	public static Collection<Object[]> data() {
		final Pair<List<PatternType>, Map<String, Integer>> pair = PatternUtil.createAllPatterns();
		return pair.getFirst().stream().map(a -> new Object[] { a, pair.getSecond(), a.getClass().getSimpleName() })
				.collect(Collectors.toList());
	}
}
