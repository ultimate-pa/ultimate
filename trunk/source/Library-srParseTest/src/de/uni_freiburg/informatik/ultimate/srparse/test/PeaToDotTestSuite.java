package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.DotWriterNew;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.srparse.test.BoogieRequirementsParserTestAllPatterns.Testpurpose;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class PeaToDotTestSuite {

	private IUltimateServiceProvider mServiceProvider;
	private ILogger mLogger;

	final String[] patterns = { "it is never the case that \"y >= 5\" holds" };

	final String[] names = { "InstAbsPattern" };

	@Before
	public void setUp() throws Exception {
		mServiceProvider = UltimateMocks.createUltimateServiceProviderMock(LogLevel.DEBUG);
		mLogger = mServiceProvider.getLoggingService().getLogger("");

		final List<String> strings = getPatterns();
		final String str = strings.get(5);

		mLogger.info("PATTERN: " + str);

		final StringReader stringReader = new StringReader(str);
		final ReqParser reqParser = new ReqParser(mServiceProvider,
				mServiceProvider.getLoggingService().getLogger(getClass()), stringReader, "");
		final Symbol goal = reqParser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		final PhaseEventAutomata pea = patterns[0].transformToPea(mLogger, new HashMap<String, Integer>());

		DotWriterNew.write("/home/ubuntu/Schreibtisch/graph.dot", true, pea, mLogger);
	}

	private static List<String> getPatterns() {
		final List<String> result = new ArrayList<>();

		for (final Object[] objects : BoogieRequirementsParserTestAllPatterns.data()) {
			assert (objects.length == 1);

			final String string = ((Testpurpose) objects[0]).mTestString;
			result.add(string);
		}

		return result;
	}

	@Test
	public void testDot() throws Exception {
		final List<String> strings = getPatterns();
		final String str = strings.get(5);

		mLogger.info("PATTERN: " + str);

		final StringReader stringReader = new StringReader(str);
		final ReqParser reqParser = new ReqParser(mServiceProvider,
				mServiceProvider.getLoggingService().getLogger(getClass()), stringReader, "");
		final Symbol goal = reqParser.parse();
		final PatternType[] patterns = (PatternType[]) goal.value;

		final PhaseEventAutomata pea = patterns[0].transformToPea(mLogger, new HashMap<String, Integer>());

		// DotWriterNew.write("/home/ubuntu/Schreibtisch/graph.dot", true, pea, mLogger);
	}
}
