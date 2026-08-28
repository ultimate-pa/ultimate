/*
 * Copyright (C) 2026 Manuel Bentele
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE
 * CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE CACSL2BoogieTranslator plug-in,
 * or any covered work, by linking or combining with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE
 * CACSL2BoogieTranslator plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.acsl.parser.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLAllExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptMasking;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptServiceRoutine;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral;

/**
 * Tests for parsing ACSL interrupt annotations such as:
 * <ul>
 * <li>{@code //@ interrupt service routine GPIO;}</li>
 * <li>{@code //@ interrupt masking enable \all;}</li>
 * <li>{@code //@ interrupt masking disable GPIO;}</li>
 * </ul>
 *
 * <p>
 * These tests exercise the ACSL lexer and parser (CUP grammar) to validate that interrupt comments are correctly parsed
 * into the corresponding {@link InterruptStatement} AST nodes.
 * </p>
 *
 * @author Manuel Bentele
 */
public class InterruptCommentParserTest {

	private static ACSLNode parse(final String acsl) throws Exception {
		return Parser.parseComment(acsl, 0, 0);
	}

	private static Contract parseContract(final String acsl) throws Exception {
		final ACSLNode node = parse(acsl);
		assertNotNull("Parser returned null for: " + acsl, node);
		assertTrue("Expected a Contract node but got " + node.getClass().getSimpleName(), node instanceof Contract);
		return (Contract) node;
	}

	private static InterruptStatement[] parseInterrupts(final String acsl) throws Exception {
		final Contract contract = parseContract(acsl);
		final InterruptStatement[] stmts = contract.getInterruptStmt();
		assertNotNull("Contract has no interrupt statements", stmts);
		return stmts;
	}

	// ── ISR annotations ──────────────────────────────────────────────────────

	@Test
	public void testParseIsrGpio() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt service routine GPIO;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptServiceRoutine);

		final var isr = (InterruptServiceRoutine) stmts[0];
		assertTrue(isr.getIdentifier() instanceof StringLiteral);
		assertEquals("GPIO", ((StringLiteral) isr.getIdentifier()).getValue());
	}

	@Test
	public void testParseIsrAdc0() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt service routine ADC0;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptServiceRoutine);

		final var isr = (InterruptServiceRoutine) stmts[0];
		assertEquals("ADC0", ((StringLiteral) isr.getIdentifier()).getValue());
	}

	@Test
	public void testParseMultipleIsrs() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt service routine GPIO; interrupt service routine ADC0;");
		assertEquals(2, stmts.length);

		// The CUP grammar is right-recursive: statements appear in reverse input order
		assertTrue(stmts[0] instanceof InterruptServiceRoutine);
		assertEquals("ADC0", ((StringLiteral) ((InterruptServiceRoutine) stmts[0]).getIdentifier()).getValue());

		assertTrue(stmts[1] instanceof InterruptServiceRoutine);
		assertEquals("GPIO", ((StringLiteral) ((InterruptServiceRoutine) stmts[1]).getIdentifier()).getValue());
	}

	// ── Masking enable/disable \all ──────────────────────────────────────────

	@Test
	public void testParseMaskingEnableAll() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt masking enable \\all;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptMasking);

		final var masking = (InterruptMasking) stmts[0];
		assertTrue("enable should be true", masking.getEnabled());
		assertTrue("Identifier should be ACSLAllExpression", masking.getIdentifier() instanceof ACSLAllExpression);
	}

	@Test
	public void testParseMaskingDisableAll() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt masking disable \\all;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptMasking);

		final var masking = (InterruptMasking) stmts[0];
		assertTrue("enable should be false", !masking.getEnabled());
		assertTrue(masking.getIdentifier() instanceof ACSLAllExpression);
	}

	// ── Masking enable/disable named IRQ ─────────────────────────────────────

	@Test
	public void testParseMaskingEnableGpio() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt masking enable GPIO;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptMasking);

		final var masking = (InterruptMasking) stmts[0];
		assertTrue(masking.getEnabled());
		assertTrue(masking.getIdentifier() instanceof StringLiteral);
		assertEquals("GPIO", ((StringLiteral) masking.getIdentifier()).getValue());
	}

	@Test
	public void testParseMaskingDisableGpio() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt masking disable GPIO;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptMasking);

		final var masking = (InterruptMasking) stmts[0];
		assertTrue("enable should be false", !masking.getEnabled());
		assertEquals("GPIO", ((StringLiteral) masking.getIdentifier()).getValue());
	}

	// ── Masking with parameter (enum-based IRQ) ──────────────────────────────

	@Test
	public void testParseMaskingEnableIrqParam() throws Exception {
		final var stmts = parseInterrupts("lstart interrupt masking enable irq ;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptMasking);

		final var masking = (InterruptMasking) stmts[0];
		assertTrue(masking.getEnabled());
		assertTrue(masking.getIdentifier() instanceof StringLiteral);
		assertEquals("irq", ((StringLiteral) masking.getIdentifier()).getValue());
	}

	// ── Combined: all annotation types from the user's example ───────────────

	@Test
	public void testParseAllAnnotationTypes() throws Exception {
		final var acsl = "lstart " + "interrupt service routine GPIO; " + "interrupt service routine ADC0; "
				+ "interrupt masking enable \\all; " + "interrupt masking disable \\all; "
				+ "interrupt masking enable GPIO; " + "interrupt masking disable GPIO; "
				+ "interrupt masking enable irq;";
		final var stmts = parseInterrupts(acsl);
		assertEquals(7, stmts.length);

		// The CUP grammar is right-recursive: statements appear in reverse input order
		// Input order: ISR GPIO, ISR ADC0, enable \all, disable \all, enable GPIO, disable GPIO, enable irq
		// List order: enable irq, disable GPIO, enable GPIO, disable \all, enable \all, ISR ADC0, ISR GPIO

		// enable irq (parameter-based) — last in input, first in list
		assertTrue(stmts[0] instanceof InterruptMasking);
		assertTrue(((InterruptMasking) stmts[0]).getEnabled());
		assertEquals("irq", ((StringLiteral) ((InterruptMasking) stmts[0]).getIdentifier()).getValue());

		// disable GPIO
		assertTrue(stmts[1] instanceof InterruptMasking);
		assertTrue(!((InterruptMasking) stmts[1]).getEnabled());
		assertEquals("GPIO", ((StringLiteral) ((InterruptMasking) stmts[1]).getIdentifier()).getValue());

		// enable GPIO
		assertTrue(stmts[2] instanceof InterruptMasking);
		assertTrue(((InterruptMasking) stmts[2]).getEnabled());
		assertEquals("GPIO", ((StringLiteral) ((InterruptMasking) stmts[2]).getIdentifier()).getValue());

		// disable \all
		assertTrue(stmts[3] instanceof InterruptMasking);
		assertTrue(!((InterruptMasking) stmts[3]).getEnabled());
		assertTrue(((InterruptMasking) stmts[3]).getIdentifier() instanceof ACSLAllExpression);

		// enable \all
		assertTrue(stmts[4] instanceof InterruptMasking);
		assertTrue(((InterruptMasking) stmts[4]).getEnabled());
		assertTrue(((InterruptMasking) stmts[4]).getIdentifier() instanceof ACSLAllExpression);

		// ISR ADC0
		assertTrue(stmts[5] instanceof InterruptServiceRoutine);
		assertEquals("ADC0", ((StringLiteral) ((InterruptServiceRoutine) stmts[5]).getIdentifier()).getValue());

		// ISR GPIO — first in input, last in list
		assertTrue(stmts[6] instanceof InterruptServiceRoutine);
		assertEquals("GPIO", ((StringLiteral) ((InterruptServiceRoutine) stmts[6]).getIdentifier()).getValue());
	}

	// ── Global vs local context ──────────────────────────────────────────────

	@Test
	public void testParseGlobalContext() throws Exception {
		final var stmts = parseInterrupts("gstart interrupt service routine GPIO;");
		assertEquals(1, stmts.length);
		assertTrue(stmts[0] instanceof InterruptServiceRoutine);
		assertEquals("GPIO", ((StringLiteral) ((InterruptServiceRoutine) stmts[0]).getIdentifier()).getValue());
	}

	@Test
	public void testParseMixedWithRequires() throws Exception {
		final var acsl = "lstart requires \\true ; interrupt service routine GPIO;";
		final var contract = parseContract(acsl);
		assertNotNull(contract.getInterruptStmt());
		assertEquals(1, contract.getInterruptStmt().length);
		assertTrue(contract.getInterruptStmt()[0] instanceof InterruptServiceRoutine);
	}

	// ── Empty contract has no interrupts ─────────────────────────────────────

	@Test
	public void testParseNoInterrupts() throws Exception {
		final var contract = parseContract("lstart requires \\true;");
		final var stmts = contract.getInterruptStmt();
		assertEquals("Expected empty interrupt array, not null", 0, stmts.length);
	}
}
