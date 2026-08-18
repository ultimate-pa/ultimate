/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CountertraceParser test plug-in.
 *
 * The ULTIMATE CountertraceParser test plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CountertraceParser test plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CountertraceParser test plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CountertraceParser test plug-in, or any covered work, by linking
 * or combining with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CountertraceParser test plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.countertrace.parser.test;

import java.io.StringReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.countertrace.parser.CountertraceFileResult;
import de.uni_freiburg.informatik.ultimate.countertrace.parser.CountertraceParserResult;
import de.uni_freiburg.informatik.ultimate.countertrace.parser.CtParser;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;

/**
 * Tests for the countertrace parser. All tests parse bare countertraces (as produced by
 * {@link CounterTrace#toString()}).
 */
public class CountertraceParserTest {

	// Unicode constants for readability
	private static final String CEIL = "\u2308"; // ⌈
	private static final String RFLOOR = "\u2309"; // ⌉
	private static final String AND = "\u2227"; // ∧
	private static final String ELL = "\u2113"; // ℓ
	private static final String LEQ = "\u2264"; // ≤
	private static final String GEQ = "\u2265"; // ≥
	private static final String SUB0 = "\u2080"; // ₀

	private CountertraceParserResult parseString(final String input) throws Exception {
		final ILogger logger = ILogger.getDummyLogger();
		final CtParser parser = new CtParser(logger, new StringReader(input), "test");
		final Symbol goal = parser.parse();
		return (CountertraceParserResult) goal.value;
	}

	private CountertraceFileResult parseFile(final String content) throws Exception {
		final ILogger logger = ILogger.getDummyLogger();
		final Path tmp = Files.createTempFile("countertrace_test_", ".ct");
		Files.write(tmp, content.getBytes(StandardCharsets.UTF_8));
		try {
			return CtParser.parseFile(logger, tmp.toString());
		} finally {
			Files.deleteIfExists(tmp);
		}
	}

	// ===== Basic parsing tests (bare countertraces) =====

	@Test
	public void testSinglePhaseWithTrue() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CDD.TRUE, phase.getEntryEvents());
		Assert.assertFalse(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_NONE, phase.getBoundType());
		Assert.assertEquals("!R", phase.getInvariant().toString());
	}

	@Test
	public void testMultiplePhases() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + ";true")
						.getCounterTrace();
		Assert.assertEquals(4, ct.getPhases().length);
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("S", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!S", ct.getPhases()[2].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[3].isAllowEmpty());
		Assert.assertEquals(CDD.TRUE, ct.getPhases()[3].getInvariant());
	}

	@Test(expected = Exception.class)
	public void testRejectsMissingTrueAtEnd() throws Exception {
		// Countertrace must always end with true
		parseString(CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR);
	}

	@Test(expected = Exception.class)
	public void testRejectsMissingTrueAtEndSinglePhase() throws Exception {
		// Even a single phase must be followed by true
		parseString(CEIL + "!R" + RFLOOR);
	}

	// ===== Bound tests (bare countertraces) =====

	@Test
	public void testPhaseWithBoundLessEq() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_LESSEQUAL, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
		Assert.assertFalse(phase.isAllowEmpty());
	}

	@Test
	public void testPhaseWithBoundLess() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " < 3;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_LESS, phase.getBoundType());
		Assert.assertEquals(3, phase.getBound());
	}

	@Test
	public void testPhaseWithBoundGreaterEq() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + " 7;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_GREATEREQUAL, phase.getBoundType());
		Assert.assertEquals(7, phase.getBound());
	}

	@Test
	public void testPhaseWithBoundGreater() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " > 2;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertEquals(CounterTrace.BOUND_GREATER, phase.getBoundType());
		Assert.assertEquals(2, phase.getBound());
	}

	// ===== allowEmpty (subzero) tests (bare countertraces) =====

	@Test
	public void testInvariantWithAllowEmptyLess() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " <" + SUB0 + " 5;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_LESS, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
		Assert.assertEquals("!R", phase.getInvariant().toString());
	}

	@Test
	public void testInvariantWithAllowEmptyLessEq() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;true")
				.getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_LESSEQUAL, phase.getBoundType());
		Assert.assertEquals(5, phase.getBound());
	}

	@Test
	public void testInvariantWithAllowEmptyGreaterEq() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + SUB0 + " 3;true")
				.getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_GREATEREQUAL, phase.getBoundType());
		Assert.assertEquals(3, phase.getBound());
	}

	@Test
	public void testInvariantWithAllowEmptyGreater() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " >" + SUB0 + " 2;true").getCounterTrace();
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertTrue(phase.isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_GREATER, phase.getBoundType());
		Assert.assertEquals(2, phase.getBound());
	}

	// ===== Complex expression tests (bare countertraces) =====

	@Test
	public void testComplexExpression() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "A " + GEQ + " B && C + 3 == D - 3" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		final DCPhase phase = ct.getPhases()[0];
		Assert.assertNotNull(phase.getInvariant());
		Assert.assertNotEquals(CDD.TRUE, phase.getInvariant());
		Assert.assertNotEquals(CDD.FALSE, phase.getInvariant());
	}

	@Test
	public void testOrExpression() throws Exception {
		final CounterTrace ct = parseString(CEIL + "A || B" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		Assert.assertNotNull(ct.getPhases()[0].getInvariant());
	}

	@Test
	public void testNotExpression() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
	}

	@Test
	public void testAndExpression() throws Exception {
		final CounterTrace ct = parseString(CEIL + "A && B" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals("(A && B)", ct.getPhases()[0].getInvariant().toString());
	}

	@Test
	public void testImplicationExpression() throws Exception {
		final CounterTrace ct = parseString(CEIL + "A ==> B" + RFLOOR + ";true").getCounterTrace();
		// NNF conversion: A ==> B becomes (B || !A)
		Assert.assertEquals("(B || !A)", ct.getPhases()[0].getInvariant().toString());
	}

	// ===== File parsing tests (bare countertraces) =====

	@Test
	public void testParseFileMultipleLines() throws Exception {
		final String content = "// comment line\n" + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true" + "\n"
				+ "\n" + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true" + "\n";
		final List<CountertraceParserResult> results = parseFile(content).getCountertraces();
		Assert.assertEquals(2, results.size());
		Assert.assertEquals(3, results.get(0).getCounterTrace().getPhases().length);
		Assert.assertEquals(3, results.get(1).getCounterTrace().getPhases().length);
	}

	@Test
	public void testParseFileWithComments() throws Exception {
		final String content = "// first countertrace\n" + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true"
				+ "\n" + "// second countertrace\n" + CEIL + "!S" + RFLOOR + ";true" + "\n";
		final List<CountertraceParserResult> results = parseFile(content).getCountertraces();
		Assert.assertEquals(2, results.size());
		Assert.assertEquals(CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true",
				results.get(0).getCounterTrace().toString());
		Assert.assertEquals(2, results.get(1).getCounterTrace().getPhases().length);
		Assert.assertTrue(results.get(1).getCounterTrace().getPhases()[1].isAllowEmpty());
	}

	// ===== Round-trip tests (parse → toString → parse → compare) =====
	// CounterTrace.toString() produces bare form, which the parser accepts directly.

	@Test
	public void testRoundTripSimple() throws Exception {
		final String input = CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + ";true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripWithBounds() throws Exception {
		final String input = CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;" + CEIL + "S" + RFLOOR
				+ " " + AND + " " + ELL + " > 3;" + CEIL + "!S" + RFLOOR + ";true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripWithAllowEmpty() throws Exception {
		final String input = CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;" + CEIL + "S"
				+ RFLOOR + " " + AND + " " + ELL + " " + GEQ + SUB0 + " 2;true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripComplexExpression() throws Exception {
		final String input = CEIL + "A " + GEQ + " B && C + 3 == D - 3" + RFLOOR + ";" + CEIL + "!R || S" + RFLOOR + ";"
				+ CEIL + "!(A && B)" + RFLOOR + ";true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	@Test
	public void testRoundTripMixedAllFeatures() throws Exception {
		final String input = CEIL + "!R" + RFLOOR + ";" + CEIL + "!R && S" + RFLOOR + " " + AND + " " + ELL + " " + LEQ
				+ " 5;" + CEIL + "!S" + RFLOOR + " " + AND + " " + ELL + " >" + SUB0 + " 3;true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
	}

	// ===== toString() output tests =====

	@Test
	public void testToString() throws Exception {
		final CounterTrace ct = parseString(
				CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;true")
						.getCounterTrace();
		final String expected =
				CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + " 5;true";
		Assert.assertEquals(expected, ct.toString());
	}

	@Test
	public void testToStringWithAllowEmpty() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;"
				+ CEIL + "S" + RFLOOR + " " + AND + " " + ELL + " >" + SUB0 + " 3;true").getCounterTrace();
		final String expected = CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " " + LEQ + SUB0 + " 5;" + CEIL + "S"
				+ RFLOOR + " " + AND + " " + ELL + " >" + SUB0 + " 3;true";
		Assert.assertEquals(expected, ct.toString());
	}

	// ===== ID parsing tests =====

	@Test
	public void testParseWithId() throws Exception {
		final CountertraceParserResult result = parseString("ID000: " + CEIL + "!R" + RFLOOR + ";true");
		Assert.assertEquals("ID000", result.getId());
		Assert.assertEquals(2, result.getCounterTrace().getPhases().length);
		Assert.assertEquals("!R", result.getCounterTrace().getPhases()[0].getInvariant().toString());
	}

	@Test
	public void testParseWithoutId() throws Exception {
		final CountertraceParserResult result = parseString(CEIL + "!R" + RFLOOR + ";true");
		Assert.assertNull(result.getId());
		Assert.assertEquals(2, result.getCounterTrace().getPhases().length);
	}

	@Test
	public void testParseFileWithIds() throws Exception {
		final String content = "// with IDs\n" + "ID000: " + CEIL + "!R" + RFLOOR + ";true" + "\n" + "ID001: " + CEIL
				+ "S" + RFLOOR + ";true" + "\n";
		final List<CountertraceParserResult> results = parseFile(content).getCountertraces();
		Assert.assertEquals(2, results.size());
		Assert.assertEquals("ID000", results.get(0).getId());
		Assert.assertEquals("ID001", results.get(1).getId());
	}

	@Test
	public void testParseFileWithSameId() throws Exception {
		final String content = "// same ID, multiple CTs\n" + "ID001: " + CEIL + "!R" + RFLOOR + ";true" + "\n"
				+ "ID001: " + CEIL + "S" + RFLOOR + ";true" + "\n";
		final List<CountertraceParserResult> results = parseFile(content).getCountertraces();
		Assert.assertEquals(2, results.size());
		Assert.assertEquals("ID001", results.get(0).getId());
		Assert.assertEquals("ID001", results.get(1).getId());
	}

	@Test
	public void testParseFileMixedIdsAndBare() throws Exception {
		final String content = "// with ID\n" + "ID000: " + CEIL + "!R" + RFLOOR + ";true" + "\n" + "// without ID\n"
				+ CEIL + "S" + RFLOOR + ";true" + "\n";
		final List<CountertraceParserResult> results = parseFile(content).getCountertraces();
		Assert.assertEquals(2, results.size());
		Assert.assertEquals("ID000", results.get(0).getId());
		Assert.assertNull(results.get(1).getId());
	}

	@Test
	public void testResultToStringWithId() throws Exception {
		final CountertraceParserResult result = parseString("ID000: " + CEIL + "!R" + RFLOOR + ";true");
		Assert.assertEquals("ID000: " + CEIL + "!R" + RFLOOR + ";true", result.toString());
	}

	@Test
	public void testResultToStringWithoutId() throws Exception {
		final CountertraceParserResult result = parseString(CEIL + "!R" + RFLOOR + ";true");
		Assert.assertEquals(CEIL + "!R" + RFLOOR + ";true", result.toString());
	}

	// ===== Declaration parsing tests =====

	@Test
	public void testParseInputDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Input R is bool\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("R", decls.get(0).getId());
		Assert.assertEquals("bool", decls.get(0).getType());
		Assert.assertEquals(VariableCategory.IN, decls.get(0).getCategory());
	}

	@Test
	public void testParseOutputDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Output S is int\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("S", decls.get(0).getId());
		Assert.assertEquals("int", decls.get(0).getType());
		Assert.assertEquals(VariableCategory.OUT, decls.get(0).getCategory());
	}

	@Test
	public void testParseInternalDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Internal x is bool\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals(VariableCategory.HIDDEN, decls.get(0).getCategory());
	}

	@Test
	public void testParseConstIntDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Const c is 5\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("c", decls.get(0).getId());
		Assert.assertEquals(VariableCategory.CONST, decls.get(0).getCategory());
		Assert.assertNotNull(decls.get(0).getExpression());
	}

	@Test
	public void testParseConstRealDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Const d is 3.14\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("d", decls.get(0).getId());
		Assert.assertEquals("real", decls.get(0).getType());
	}

	@Test
	public void testParseConstBoolDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Const b is true\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("bool", decls.get(0).getType());
	}

	@Test
	public void testParseConstNegativeIntDeclaration() throws Exception {
		final List<DeclarationPattern> decls = parseFile("Const n is -42\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals("int", decls.get(0).getType());
	}

	@Test
	public void testParseDeclarationsAndCountertraces() throws Exception {
		final String content = "// declarations\n" + "Input R is bool\n" + "Output S is bool\n" + "Const c is 5\n"
				+ "// countertraces\n" + "ID000: " + CEIL + "!R" + RFLOOR + ";" + CEIL + "S" + RFLOOR + ";true\n"
				+ "ID001: " + CEIL + "!S" + RFLOOR + ";true\n";
		final CountertraceFileResult result = parseFile(content);
		Assert.assertEquals(3, result.getDeclarations().size());
		Assert.assertEquals(2, result.getCountertraces().size());
		Assert.assertEquals("R", result.getDeclarations().get(0).getId());
		Assert.assertEquals(VariableCategory.IN, result.getDeclarations().get(0).getCategory());
		Assert.assertEquals("S", result.getDeclarations().get(1).getId());
		Assert.assertEquals(VariableCategory.OUT, result.getDeclarations().get(1).getCategory());
		Assert.assertEquals("c", result.getDeclarations().get(2).getId());
		Assert.assertEquals(VariableCategory.CONST, result.getDeclarations().get(2).getCategory());
		Assert.assertEquals("ID000", result.getCountertraces().get(0).getId());
		Assert.assertEquals("ID001", result.getCountertraces().get(1).getId());
	}

	@Test
	public void testParseDeclarationCaseInsensitive() throws Exception {
		final List<DeclarationPattern> decls = parseFile("input R is bool\n").getDeclarations();
		Assert.assertEquals(1, decls.size());
		Assert.assertEquals(VariableCategory.IN, decls.get(0).getCategory());
	}

	// ===== Pattern-based countertrace tests =====
	// These countertraces are adapted from the hardcoded phase sequences in
	// Library-srParse pattern classes (AbsencePattern, ResponsePattern, etc.).
	// They represent real-world requirement patterns and make excellent test cases.
	// Variables P, Q, R, S are used as in the original patterns.

	// AbsencePattern globally: phaseT(), phase(R), phaseT()
	@Test
	public void testPatternAbsenceGlobally() throws Exception {
		final CounterTrace ct = parseString("true;" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertTrue(ct.getPhases()[0].isAllowEmpty());
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[2].isAllowEmpty());
	}

	// AbsencePattern before: phase(P.negate()), phase(P.negate().and(R)), phaseT()
	@Test
	public void testPatternAbsenceBefore() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!P" + RFLOOR + ";" + CEIL + "!P && R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals("!P", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("(!P && R)", ct.getPhases()[1].getInvariant().toString());
	}

	// AbsencePattern after-until: phaseT(), phase(P), phase(Q.negate()),
	// phase(Q.negate().and(R)), phaseT()
	@Test
	public void testPatternAbsenceAfterUntil() throws Exception {
		final CounterTrace ct = parseString(
				"true;" + CEIL + "P" + RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "!Q && R" + RFLOOR + ";true")
						.getCounterTrace();
		Assert.assertEquals(5, ct.getPhases().length);
		Assert.assertEquals("P", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!Q", ct.getPhases()[2].getInvariant().toString());
		Assert.assertEquals("(!Q && R)", ct.getPhases()[3].getInvariant().toString());
	}

	// AbsencePattern after: phaseT(), phase(P), phaseT(), phase(R), phaseT()
	@Test
	public void testPatternAbsenceAfter() throws Exception {
		final CounterTrace ct =
				parseString("true;" + CEIL + "P" + RFLOOR + ";true;" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(5, ct.getPhases().length);
		Assert.assertTrue(ct.getPhases()[0].isAllowEmpty());
		Assert.assertEquals("P", ct.getPhases()[1].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[2].isAllowEmpty());
		Assert.assertEquals("R", ct.getPhases()[3].getInvariant().toString());
	}

	// AbsencePattern between: phaseT(), phase(P.and(Q.negate())),
	// phase(Q.negate()), phase(Q.negate().and(R)), phase(Q.negate()),
	// phase(Q), phaseT()
	@Test
	public void testPatternAbsenceBetween() throws Exception {
		final CounterTrace ct =
				parseString("true;" + CEIL + "P && !Q" + RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "!Q && R"
						+ RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "Q" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(7, ct.getPhases().length);
		Assert.assertEquals("(P && !Q)", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("Q", ct.getPhases()[5].getInvariant().toString());
	}

	// ResponsePattern globally: phase(P.negate()),
	// phase(P.negate().and(R).and(S.negate())),
	// phase(P.negate().and(S.negate())), phase(P), phaseT()
	@Test
	public void testPatternResponseGlobally() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!P" + RFLOOR + ";" + CEIL + "!P && R && !S" + RFLOOR + ";" + CEIL
				+ "!P && !S" + RFLOOR + ";" + CEIL + "P" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(5, ct.getPhases().length);
		Assert.assertEquals("!P", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("(!P && (R && !S))", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("(!P && !S)", ct.getPhases()[2].getInvariant().toString());
		Assert.assertEquals("P", ct.getPhases()[3].getInvariant().toString());
	}

	// InvariancePattern globally: phaseT(), phase(R.and(S.negate())), phaseT()
	@Test
	public void testPatternInvarianceGlobally() throws Exception {
		final CounterTrace ct = parseString("true;" + CEIL + "R && !S" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals("(R && !S)", ct.getPhases()[1].getInvariant().toString());
	}

	// UniversalityPattern globally: phaseT(), phase(R.negate()), phaseT()
	@Test
	public void testPatternUniversalityGlobally() throws Exception {
		final CounterTrace ct = parseString("true;" + CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals("!R", ct.getPhases()[1].getInvariant().toString());
	}

	// PersistencePattern globally: phaseT(), phase(R), phase(R.negate()), phaseT()
	@Test
	public void testPatternPersistenceGlobally() throws Exception {
		final CounterTrace ct =
				parseString("true;" + CEIL + "R" + RFLOOR + ";" + CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(4, ct.getPhases().length);
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!R", ct.getPhases()[2].getInvariant().toString());
	}

	// PrecedencePattern globally: phase(S.negate()), phase(R), phaseT()
	@Test
	public void testPatternPrecedenceGlobally() throws Exception {
		final CounterTrace ct =
				parseString(CEIL + "!S" + RFLOOR + ";" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals("!S", ct.getPhases()[0].getInvariant().toString());
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
	}

	// InitializationPattern globally: phase(R.negate()), phaseT()
	@Test
	public void testPatternInitializationGlobally() throws Exception {
		final CounterTrace ct = parseString(CEIL + "!R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(2, ct.getPhases().length);
		Assert.assertEquals("!R", ct.getPhases()[0].getInvariant().toString());
		Assert.assertTrue(ct.getPhases()[1].isAllowEmpty());
	}

	// ExistenceBoundUPattern globally: phaseT(), phase(R), phase(R.negate()),
	// phase(R), phase(R.negate()), phase(R), phaseT()
	@Test
	public void testPatternExistenceBoundUGlobally() throws Exception {
		final CounterTrace ct = parseString("true;" + CEIL + "R" + RFLOOR + ";" + CEIL + "!R" + RFLOOR + ";" + CEIL
				+ "R" + RFLOOR + ";" + CEIL + "!R" + RFLOOR + ";" + CEIL + "R" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(7, ct.getPhases().length);
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!R", ct.getPhases()[2].getInvariant().toString());
		Assert.assertEquals("R", ct.getPhases()[3].getInvariant().toString());
		Assert.assertEquals("!R", ct.getPhases()[4].getInvariant().toString());
		Assert.assertEquals("R", ct.getPhases()[5].getInvariant().toString());
	}

	// BndEntryConditionPattern globally: phaseT(),
	// phase(R, BoundTypes.GREATEREQUAL, c1), phase(S.negate()), phaseT()
	@Test
	public void testPatternBndEntryConditionGlobally() throws Exception {
		final CounterTrace ct = parseString("true;" + CEIL + "R" + RFLOOR + " " + AND + " " + ELL + " " + GEQ + " 5;"
				+ CEIL + "!S" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(4, ct.getPhases().length);
		Assert.assertTrue(ct.getPhases()[0].isAllowEmpty());
		Assert.assertEquals(CounterTrace.BOUND_GREATEREQUAL, ct.getPhases()[1].getBoundType());
		Assert.assertEquals(5, ct.getPhases()[1].getBound());
		Assert.assertEquals("R", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!S", ct.getPhases()[2].getInvariant().toString());
	}

	// ReccurrenceBoundLPattern globally: phaseT(),
	// phase(R.negate(), BoundTypes.GREATER, c1), phaseT()
	@Test
	public void testPatternReccurrenceBoundLGlobally() throws Exception {
		final CounterTrace ct =
				parseString("true;" + CEIL + "!R" + RFLOOR + " " + AND + " " + ELL + " > 3;true").getCounterTrace();
		Assert.assertEquals(3, ct.getPhases().length);
		Assert.assertEquals(CounterTrace.BOUND_GREATER, ct.getPhases()[1].getBoundType());
		Assert.assertEquals(3, ct.getPhases()[1].getBound());
		Assert.assertEquals("!R", ct.getPhases()[1].getInvariant().toString());
	}

	// ResponseDelayPattern globally: phaseT(), phase(R.and(S.negate())),
	// phase(S.negate(), BoundTypes.GREATER, c1), phaseT()
	@Test
	public void testPatternResponseDelayGlobally() throws Exception {
		final CounterTrace ct = parseString(
				"true;" + CEIL + "R && !S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + " " + AND + " " + ELL + " > 7;true")
						.getCounterTrace();
		Assert.assertEquals(4, ct.getPhases().length);
		Assert.assertEquals("(R && !S)", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals(CounterTrace.BOUND_GREATER, ct.getPhases()[2].getBoundType());
		Assert.assertEquals(7, ct.getPhases()[2].getBound());
		Assert.assertEquals("!S", ct.getPhases()[2].getInvariant().toString());
	}

	// InvarianceDelayPattern globally (two CTs):
	// CT1: phaseT(), phase(R.and(S)), phase(R.and(S.negate())), phaseT()
	// CT2: phaseT(), phase(R.and(S.negate())),
	// phase(S.negate(), BoundTypes.GREATER, c1), phaseT()
	@Test
	public void testPatternInvarianceDelayGlobally() throws Exception {
		final String ct1 = "true;" + CEIL + "R && S" + RFLOOR + ";" + CEIL + "R && !S" + RFLOOR + ";true";
		final String ct2 =
				"true;" + CEIL + "R && !S" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + " " + AND + " " + ELL + " > 10;true";
		final CounterTrace trace1 = parseString(ct1).getCounterTrace();
		final CounterTrace trace2 = parseString(ct2).getCounterTrace();
		Assert.assertEquals(4, trace1.getPhases().length);
		Assert.assertEquals("(R && S)", trace1.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("(R && !S)", trace1.getPhases()[2].getInvariant().toString());
		Assert.assertEquals(4, trace2.getPhases().length);
		Assert.assertEquals(CounterTrace.BOUND_GREATER, trace2.getPhases()[2].getBoundType());
		Assert.assertEquals(10, trace2.getPhases()[2].getBound());
	}

	// PrecedencePattern after: phaseT(), phase(P), phase(S.negate()),
	// phase(R), phaseT()
	@Test
	public void testPatternPrecedenceAfter() throws Exception {
		final CounterTrace ct = parseString(
				"true;" + CEIL + "P" + RFLOOR + ";" + CEIL + "!S" + RFLOOR + ";" + CEIL + "R" + RFLOOR + ";true")
						.getCounterTrace();
		Assert.assertEquals(5, ct.getPhases().length);
		Assert.assertEquals("P", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("!S", ct.getPhases()[2].getInvariant().toString());
		Assert.assertEquals("R", ct.getPhases()[3].getInvariant().toString());
	}

	// ResponsePattern between: phaseT(), phase(P.and(Q.negate())),
	// phase(Q.negate()), phase(Q.negate().and(R).and(S.negate())),
	// phase(Q.negate().and(S.negate())), phase(Q), phaseT()
	@Test
	public void testPatternResponseBetween() throws Exception {
		final CounterTrace ct = parseString(
				"true;" + CEIL + "P && !Q" + RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "!Q && R && !S" + RFLOOR
						+ ";" + CEIL + "!Q && !S" + RFLOOR + ";" + CEIL + "Q" + RFLOOR + ";true").getCounterTrace();
		Assert.assertEquals(7, ct.getPhases().length);
		Assert.assertEquals("(P && !Q)", ct.getPhases()[1].getInvariant().toString());
		Assert.assertEquals("(!Q && (R && !S))", ct.getPhases()[3].getInvariant().toString());
		Assert.assertEquals("Q", ct.getPhases()[5].getInvariant().toString());
	}

	// Round-trip test with a pattern-based CT
	@Test
	public void testRoundTripPatternAbsenceBetween() throws Exception {
		final String input = "true;" + CEIL + "P && !Q" + RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "!Q && R"
				+ RFLOOR + ";" + CEIL + "!Q" + RFLOOR + ";" + CEIL + "Q" + RFLOOR + ";true";
		final CounterTrace ct1 = parseString(input).getCounterTrace();
		final String str1 = ct1.toString();
		final CounterTrace ct2 = parseString(str1).getCounterTrace();
		Assert.assertEquals(str1, ct2.toString());
		Assert.assertEquals(7, ct2.getPhases().length);
	}
}
