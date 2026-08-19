package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.io.StringReader;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.CountertracePattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests for countertrace notation integrated into the requirements parser.
 *
 * <p>
 * These tests verify that the ReqParser (via Requirements.cup) correctly parses countertrace notation like
 * {@code req1: ⌈R⌉;⌈¬R⌉ ∧ ℓ < 10;true} directly in .req-style input.
 * </p>
 */
public class CountertraceNotationTest {

	private static final String CEIL = "\u2308";
	private static final String RFLOOR = "\u2309";
	private static final String AND = "\u2227";
	private static final String ELL = "\u2113";
	private static final String LEQ = "\u2264";
	private static final String GEQ = "\u2265";
	private static final String SUB0 = "\u2080";

	private PatternType<?>[] parse(final String input) throws Exception {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		final StringReader sr = new StringReader(input);
		final ReqParser parser = new ReqParser(services.getLoggingService().getLogger(getClass()), sr, "");
		final Symbol goal = parser.parse();
		return (PatternType<?>[]) goal.value;
	}

	private CountertracePattern parseCountertrace(final String input) throws Exception {
		final PatternType<?>[] patterns = parse(input);
		for (final PatternType<?> p : patterns) {
			if (p instanceof CountertracePattern) {
				return (CountertracePattern) p;
			}
		}
		Assert.fail("No CountertracePattern found in parsed result: " + Arrays.toString(patterns));
		return null;
	}

	// ===== Basic parsing tests =====

	@Test
	public void testSinglePhaseWithTrue() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CDD.TRUE, phase.getEntryEvents());
		Assert.assertFalse(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_NONE, phase.getBoundType());
		Assert.assertEquals("!R", phase.getInvariant().toString());
	}

	@Test
	public void testMultiplePhases() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + ";true")
						.getCounterTrace();
		Assert.assertEquals(4, ct.getPhases().length);
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("S", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!S", ct.getPhases()[2].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[3].isAllowEmpty());
		Assert.assertEquals(CDD.TRUE, ct.getPhases()[3].getInvariant());
	}

	@Test
	public void testStartsWithTrue() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: true;" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertTrue(ct.getPhases()[0].isAllowEmpty());
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[2].isAllowEmpty());
	}

	// ===== Bound tests =====

	@Test
	public void testPhaseWithBoundLessEq() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_LESSEQUAL, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
		Assert.assertFalse(phase.isAllowEmpty());
	}

	@Test
	public void testPhaseWithBoundLess() throws Exception {
		final CounterTrace ct =
				parseCountertrace("req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " < 3;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_LESS, phase.getBoundType());
		Assert.assertEquals(3, phase.getBound());
	}

	@Test
	public void testPhaseWithBoundGreaterEq() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + " 7;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_GREATEREQUAL, phase.getBoundType());
		Assert.assertEquals(7, phase.getBound());
	}

	@Test
	public void testPhaseWithBoundGreater() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " > 2;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_GREATER, phase.getBoundType());
		Assert.assertEquals(2, phase.getBound());
	}

	// ===== allowEmpty (subzero) tests =====

	@Test
	public void testInvariantWithAllowEmptyLess() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " <" + SUB0 + " 5;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_LESS, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
		Assert.assertEquals("!R", phase.getInvariant().toString());
	}

	@Test
	public void testInvariantWithAllowEmptyLessEq() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_LESSEQUAL, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
	}

	@Test
	public void testInvariantWithAllowEmptyGreaterEq() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + SUB0 + " 3;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_GREATEREQUAL, phase.getBoundType());
		Assert.assertEquals(3, phase.getBound());
	}

	@Test
	public void testInvariantWithAllowEmptyGreater() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " >" + SUB0 + " 2;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_GREATER, phase.getBoundType());
		Assert.assertEquals(2, phase.getBound());
	}

	// ===== Complex expression tests =====

	@Test
	public void testComplexExpression() throws Exception {
		final CounterTrace ct = parseCountertrace(
				"req1: " + CEIL + "A " + GEQ + " B && C + 3 == D - 3" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertNotNull(phase.getInvariant());
		Assert.assertNotEquals(CDD.TRUE, phase.getInvariant());
		Assert.assertNotEquals(CDD.FALSE, phase.getInvariant());
	}

	@Test
	public void testOrExpression() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "A || B" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		Assert.assertNotNull(ct.getPhases()[0].getInvariant());
	}

	@Test
	public void testNotExpression() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
	}

	@Test
	public void testAndExpression() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "A && B" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals("(A && B)", ct.getPhases()[0].getInvariant().toString());
	}

	@Test
	public void testImplicationExpression() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "A ==> B" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals("(B || !A)", ct.getPhases()[0].getInvariant().toString());
	}

	// ===== Mixed req + countertrace tests =====

	@Test
	public void testMixedReqAndCountertrace() throws Exception {
		final String input = "Input R is bool\n" + "Output S is bool\n"
				+ "req1: Globally, it is never the case that \"R\" holds\n"
				+ "req2: " + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true\n";
		final PatternType<?>[] patterns = parse(input);
		Assert.assertEquals(4, patterns.length);
		Assert.assertTrue(patterns[0] instanceof DeclarationPattern);
		Assert.assertTrue(patterns[1] instanceof DeclarationPattern);
		// patterns[2] is a regular req pattern (AbsencePattern)
		Assert.assertTrue(patterns[3] instanceof CountertracePattern);
	}

	@Test
	public void testDeclarationsAndCountertraces() throws Exception {
		final String input = "Input R is bool\n" + "Output S is bool\n" + "Const c is 5\n" + "req1: " + CEIL + "!R"
				+ RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true\n" + "req2: " + CEIL + "!S" + RFLOOR + ";true\n";
		final PatternType<?>[] patterns = parse(input);
		Assert.assertEquals(5, patterns.length);
		Assert.assertTrue(patterns[0] instanceof DeclarationPattern);
		Assert.assertEquals("R", patterns[0].getId());
		Assert.assertEquals(VariableCategory.IN, ((DeclarationPattern) patterns[0]).getCategory());
		Assert.assertTrue(patterns[3] instanceof CountertracePattern);
		Assert.assertEquals("req1", patterns[3].getId());
		Assert.assertTrue(patterns[4] instanceof CountertracePattern);
		Assert.assertEquals("req2", patterns[4].getId());
	}

	// ===== Round-trip tests =====

	@Test
	public void testRoundTripSimple() throws Exception {
		final String input = "req1: " + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR
				+ ";true";
		final CounterTrace ct1 = parseCountertrace(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseCountertrace("req1: " + str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripWithBounds() throws Exception {
		final String input = "req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;" + CEIL + "S"
				+ RFLOOR + " " + AND + " " + ELL + " > 3;" + CEIL + "!S" + RFLOOR + ";true";
		final CounterTrace ct1 = parseCountertrace(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseCountertrace("req1: " + str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripWithAllowEmpty() throws Exception {
		final String input = "req1: " + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;" + CEIL
				+ "S" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + SUB0 + " 2;true";
		final CounterTrace ct1 = parseCountertrace(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseCountertrace("req1: " + str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	// ===== Pattern-based countertrace tests =====

	@Test
	public void testPatternAbsenceGlobally() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: true;" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertTrue(ct.getPhases()[0].isAllowEmpty());
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[2].isAllowEmpty());
	}

	@Test
	public void testPatternResponseGlobally() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "!P" + RFLOOR + ";" + CEIL + "!P && R && !S"
				+ RFLOOR + ";" + CEIL + "!P && !S" + RFLOOR + ";" + CEIL + "P" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(5, ct.getPhases().length);
		Assert.assertEquals("!P", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("(!P && (R && !S))", ct.getPhases()[1].getInvariant().toString());
	}

	@Test
	public void testPatternInvarianceGlobally() throws Exception {
		final CounterTrace ct =
				parseCountertrace("req1: true;" + CEIL + "R && !S" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals("(R && !S)", ct.getPhases()[1].getInvariant().toString());
	}

	@Test
	public void testPatternInitializationGlobally() throws Exception {
		final CounterTrace ct = parseCountertrace("req1: " + CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[1].isAllowEmpty());
	}
}
