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

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InterruptPostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.IInterruptFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptMaskingFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequestHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.reference.AllInterrupts;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.reference.StaticInterrupt;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLAllExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptMasking;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptServiceRoutine;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral;

/**
 * Tests that verify the {@link InterruptPostProcessor} obtains correctly parsed {@link IInterruptFunction} objects from
 * the {@link InterruptFunctionHandler}.
 *
 * <p>
 * These tests simulate the full pipeline that the {@code ACSLHandler} performs:
 * </p>
 * <ol>
 * <li>Parse ACSL interrupt annotations using the ACSL parser</li>
 * <li>Translate parsed AST nodes into {@link InterruptServiceFunction} and {@link InterruptMaskingFunction} objects
 * (mirroring {@code ACSLHandler.visit()})</li>
 * <li>Register them in an {@link InterruptFunctionHandler}</li>
 * <li>Verify that the query patterns used by {@link InterruptPostProcessor} ({@code getIsrs()},
 * {@code getFunctions(InterruptMaskingFunction.class)}, {@code IInterruptReference.resolve()}) return correct results
 * </li>
 * </ol>
 *
 * @author Manuel Bentele
 */
public class InterruptPostProcessorTest {

	private static final ILocation IGNORE_LOC = LocationFactory.createIgnoreCLocation();

	private static Procedure createProcedure(final String name) {
		return new Procedure(IGNORE_LOC, new Attribute[0], name, new String[0], new VarList[0], new VarList[0],
				new Specification[0], null);
	}

	/**
	 * Parses ACSL and translates interrupt statements into IInterruptFunction objects, mirroring what ACSLHandler does.
	 * Registers them in the given handler and uses the given IRQ handler for reference resolution.
	 */
	private static void parseAndRegister(final String acsl, final InterruptFunctionHandler funcHandler,
			final InterruptRequestHandler irqHandler) throws Exception {
		final ACSLNode node = Parser.parseComment(acsl, 0, 0);
		assertNotNull("Parser returned null", node);
		assertTrue("Expected Contract, got " + node.getClass().getSimpleName(), node instanceof Contract);
		final Contract contract = (Contract) node;
		final InterruptStatement[] stmts = contract.getInterruptStmt();
		assertNotNull(stmts);

		for (final InterruptStatement stmt : stmts) {
			if (stmt instanceof final InterruptServiceRoutine isrNode) {
				final String irqName = ((StringLiteral) isrNode.getIdentifier()).getValue();
				if (!irqHandler.hasIrq(irqName)) {
					irqHandler.register(irqName);
				}
				final var staticIrq = new StaticInterrupt(irqHandler.getIrq(irqName));
				final var isrFunc = new InterruptServiceFunction(staticIrq);
				funcHandler.register(isrFunc);
			} else if (stmt instanceof final InterruptMasking maskingNode) {
				final IInterruptReference ref;
				if (maskingNode.getIdentifier() instanceof ACSLAllExpression) {
					ref = new AllInterrupts();
				} else {
					final String irqName = ((StringLiteral) maskingNode.getIdentifier()).getValue();
					if (!irqHandler.hasIrq(irqName)) {
						irqHandler.register(irqName);
					}
					ref = new StaticInterrupt(irqHandler.getIrq(irqName));
				}
				final var op = maskingNode.getEnabled() ? InterruptMaskingFunction.Operation.ENABLE
						: InterruptMaskingFunction.Operation.DISABLE;
				final var maskingFunc = new InterruptMaskingFunction(ref, op);
				funcHandler.register(maskingFunc);
			}
		}
	}

	// ── ISR retrieval (getIsrs) ───────────────────────────────────────────────

	@Test
	public void testGetIsrsSingleGpio() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO;", funcHandler, irqHandler);

		final var isrs = funcHandler.getIsrs();
		assertEquals(1, isrs.size());
		assertEquals("GPIO", isrs.get(0).getIrqReference().getIrq().getName());
		assertTrue(isrs.get(0).isServiceFunction());
	}

	@Test
	public void testGetIsrsMultiple() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO; interrupt service routine ADC0;", funcHandler,
				irqHandler);

		final var isrs = funcHandler.getIsrs();
		assertEquals(2, isrs.size());
		// Right-recursive grammar: ADC0 first, GPIO second
		assertTrue(isrs.stream().anyMatch(isr -> isr.getIrqReference().getIrq().getName().equals("GPIO")));
		assertTrue(isrs.stream().anyMatch(isr -> isr.getIrqReference().getIrq().getName().equals("ADC0")));
	}

	@Test
	public void testGetIsrsExcludesMaskingFunctions() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister(
				"lstart interrupt service routine GPIO; interrupt masking enable GPIO; interrupt masking disable GPIO;",
				funcHandler, irqHandler);

		final var isrs = funcHandler.getIsrs();
		assertEquals("Only ISRs should be returned, not masking functions", 1, isrs.size());
		assertEquals("GPIO", isrs.get(0).getIrqReference().getIrq().getName());
	}

	// ── Masking function retrieval (getFunctions) ─────────────────────────────

	@Test
	public void testGetMaskingFunctionsEnableAll() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt masking enable \\all;", funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(1, maskingFuncs.size());
		assertEquals(InterruptMaskingFunction.Operation.ENABLE, maskingFuncs.get(0).getOperation());
		assertTrue(maskingFuncs.get(0).getIrqReference() instanceof AllInterrupts);
	}

	@Test
	public void testGetMaskingFunctionsDisableAll() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt masking disable \\all;", funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(1, maskingFuncs.size());
		assertEquals(InterruptMaskingFunction.Operation.DISABLE, maskingFuncs.get(0).getOperation());
		assertTrue(maskingFuncs.get(0).getIrqReference() instanceof AllInterrupts);
	}

	@Test
	public void testGetMaskingFunctionsEnableGpio() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt masking enable GPIO;", funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(1, maskingFuncs.size());
		assertEquals(InterruptMaskingFunction.Operation.ENABLE, maskingFuncs.get(0).getOperation());
		assertTrue(maskingFuncs.get(0).getIrqReference() instanceof StaticInterrupt);
		assertEquals("GPIO", ((StaticInterrupt) maskingFuncs.get(0).getIrqReference()).getIrq().getName());
	}

	@Test
	public void testGetMaskingFunctionsSeparateEnableDisable() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister(
				"lstart interrupt masking enable GPIO; interrupt masking disable GPIO; interrupt masking enable \\all;",
				funcHandler, irqHandler);

		final var allMasking = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(3, allMasking.size());

		final var enableFuncs =
				allMasking.stream().filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.ENABLE).toList();
		assertEquals(2, enableFuncs.size());

		final var disableFuncs = allMasking.stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.DISABLE).toList();
		assertEquals(1, disableFuncs.size());
	}

	@Test
	public void testGetMaskingFunctionsExcludesIsrs() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO; interrupt masking enable GPIO;", funcHandler,
				irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals("Only masking functions, not ISRs", 1, maskingFuncs.size());
	}

	// ── IRQ reference resolution (IInterruptReference.resolve) ────────────────

	@Test
	public void testResolveStaticInterruptGpio() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO;", funcHandler, irqHandler);

		final var isrs = funcHandler.getIsrs();
		final var ref = isrs.get(0).getIrqReference();
		assertTrue(ref instanceof StaticInterrupt);

		final var resolved = ref.resolve(irqHandler);
		assertNotNull(resolved);
		assertEquals(1, resolved.size());
		assertEquals("GPIO", resolved.get(0).getName());
		assertEquals(1, resolved.get(0).getNum());
	}

	@Test
	public void testResolveAllInterrupts() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister(
				"lstart interrupt service routine GPIO; interrupt service routine ADC0; interrupt masking enable \\all;",
				funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(1, maskingFuncs.size());
		final var ref = maskingFuncs.get(0).getIrqReference();
		assertTrue(ref instanceof AllInterrupts);

		final var resolved = ref.resolve(irqHandler);
		assertNotNull(resolved);
		assertEquals("AllInterrupts should resolve to all registered IRQs", 2, resolved.size());
		assertTrue(resolved.stream().anyMatch(irq -> irq.getName().equals("GPIO")));
		assertTrue(resolved.stream().anyMatch(irq -> irq.getName().equals("ADC0")));
	}

	@Test
	public void testResolveStaticInterruptIrqNum() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister(
				"lstart interrupt service routine GPIO; interrupt service routine ADC0; interrupt masking enable ADC0;",
				funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(1, maskingFuncs.size());
		final var ref = maskingFuncs.get(0).getIrqReference();
		assertTrue(ref instanceof StaticInterrupt);

		final var resolved = ref.resolve(irqHandler);
		assertNotNull(resolved);
		assertEquals(1, resolved.size());
		assertEquals("ADC0", resolved.get(0).getName());
		// Right-recursive grammar: ADC0 is processed first (as part of the masking annotation), gets IRQ 1
		assertEquals(1, resolved.get(0).getNum());
	}

	// ── resolveMaskingFunctionProcedures simulation ──────────────────────────
	// Mirrors what InterruptPostProcessor.resolveMaskingFunctionProcedures() does

	@Test
	public void testResolveMaskingProceduresEnableSpecific() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO; interrupt service routine ADC0; "
				+ "interrupt masking enable GPIO;", funcHandler, irqHandler);

		// Simulate resolveMaskingFunctionProcedures(ENABLE)
		final var enableFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class).stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.ENABLE).toList();

		assertEquals(1, enableFuncs.size());
		final var resolved = enableFuncs.get(0).getIrqReference().resolve(irqHandler);
		assertNotNull(resolved);
		assertEquals(1, resolved.size());
		assertEquals("GPIO", resolved.get(0).getName());
		assertEquals(1, resolved.get(0).getNum());
	}

	@Test
	public void testResolveMaskingProceduresEnableAllExpands() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO; interrupt service routine ADC0; "
				+ "interrupt masking enable \\all;", funcHandler, irqHandler);

		// Simulate resolveMaskingFunctionProcedures(ENABLE)
		final var enableFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class).stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.ENABLE).toList();

		assertEquals(1, enableFuncs.size());
		final var resolved = enableFuncs.get(0).getIrqReference().resolve(irqHandler);
		assertNotNull(resolved);
		assertEquals("\\all should expand to all registered IRQs", 2, resolved.size());
	}

	@Test
	public void testResolveMaskingProceduresDisableSeparate() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO; interrupt service routine ADC0; "
				+ "interrupt masking enable GPIO; interrupt masking disable ADC0;", funcHandler, irqHandler);

		final var enableFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class).stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.ENABLE).toList();
		final var disableFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class).stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.DISABLE).toList();

		assertEquals(1, enableFuncs.size());
		assertEquals("GPIO", enableFuncs.get(0).getIrqReference().resolve(irqHandler).get(0).getName());

		assertEquals(1, disableFuncs.size());
		assertEquals("ADC0", disableFuncs.get(0).getIrqReference().resolve(irqHandler).get(0).getName());
	}

	// ── Full user example ─────────────────────────────────────────────────────

	@Test
	public void testFullUserExample() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart " + "interrupt service routine GPIO; " + "interrupt service routine ADC0; "
				+ "interrupt masking enable \\all; " + "interrupt masking disable \\all; "
				+ "interrupt masking enable GPIO; " + "interrupt masking disable GPIO; "
				+ "interrupt masking enable irq;", funcHandler, irqHandler);

		// Verify ISRs
		final var isrs = funcHandler.getIsrs();
		assertEquals(2, isrs.size());
		assertTrue(isrs.stream().anyMatch(f -> f.getIrqReference().getIrq().getName().equals("GPIO")));
		assertTrue(isrs.stream().anyMatch(f -> f.getIrqReference().getIrq().getName().equals("ADC0")));

		// Verify masking functions
		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		assertEquals(5, maskingFuncs.size());

		final var enableFuncs = maskingFuncs.stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.ENABLE).toList();
		assertEquals(3, enableFuncs.size());

		final var disableFuncs = maskingFuncs.stream()
				.filter(f -> f.getOperation() == InterruptMaskingFunction.Operation.DISABLE).toList();
		assertEquals(2, disableFuncs.size());

		// Verify \all expands to all registered IRQs (irq=1, GPIO=2, ADC0=3 due to right-recursive grammar)
		final var allEnable = enableFuncs.stream().filter(f -> f.getIrqReference() instanceof AllInterrupts).toList();
		assertEquals(1, allEnable.size());
		final var allResolved = allEnable.get(0).getIrqReference().resolve(irqHandler);
		assertEquals(3, allResolved.size());

		// Verify GPIO masking resolves to IRQ 2 (registered second due to reversed grammar order)
		final var gpioEnable = enableFuncs.stream().filter(f -> f.getIrqReference() instanceof StaticInterrupt
				&& ((StaticInterrupt) f.getIrqReference()).getIrq().getName().equals("GPIO")).toList();
		assertEquals(1, gpioEnable.size());
		assertEquals(2, gpioEnable.get(0).getIrqReference().resolve(irqHandler).get(0).getNum());

		// Verify irq parameter resolves to IRQ 1 (registered first due to reversed grammar order)
		final var irqEnable = enableFuncs.stream().filter(f -> f.getIrqReference() instanceof StaticInterrupt
				&& ((StaticInterrupt) f.getIrqReference()).getIrq().getName().equals("irq")).toList();
		assertEquals(1, irqEnable.size());
		assertEquals(1, irqEnable.get(0).getIrqReference().resolve(irqHandler).get(0).getNum());
	}

	// ── Procedure assignment ──────────────────────────────────────────────────

	@Test
	public void testProcedureAssignmentOnIsr() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt service routine GPIO;", funcHandler, irqHandler);

		final var isrs = funcHandler.getIsrs();
		final var isr = isrs.get(0);

		// Simulate what CHandler does: assign the C function's procedure
		final var proc = createProcedure("isr_gpio");
		isr.setProcedure(proc);
		assertEquals("isr_gpio", isr.getProcedure().getIdentifier());
	}

	@Test
	public void testProcedureAssignmentOnMaskingFunction() throws Exception {
		final var funcHandler = new InterruptFunctionHandler();
		final var irqHandler = new InterruptRequestHandler();
		parseAndRegister("lstart interrupt masking enable GPIO;", funcHandler, irqHandler);

		final var maskingFuncs = funcHandler.getFunctions(InterruptMaskingFunction.class);
		final var func = maskingFuncs.get(0);

		final var proc = createProcedure("irq_gpio_enable");
		func.setProcedure(proc);
		assertEquals("irq_gpio_enable", func.getProcedure().getIdentifier());
	}
}
