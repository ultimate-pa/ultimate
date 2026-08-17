/*
 * Copyright (C) 2026 Matthias Zumkeller
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
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE
 * CACSL2BoogieTranslator plug-in grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.InterruptRequest;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.irq.reference.StaticInterrupt;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Tests for {@link InterruptFunctionBoogieData}.
 *
 * @author Matthias Zumkeller
 */
public class InterruptFunctionBoogieDataTest {

	private static final ILocation IGNORE_LOC = LocationFactory.createIgnoreCLocation();

	private static InterruptServiceFunction createIsr(final String procName, final int irqNum) {
		final var irq = new InterruptRequest("irq" + irqNum, irqNum);
		final var staticIrq = new StaticInterrupt(irq);
		final var proc = new Procedure(IGNORE_LOC, new Attribute[0], procName, new String[0], new VarList[0],
				new VarList[0], new Specification[0], null);
		return new InterruptServiceFunction(proc, staticIrq);
	}

	@Test
	public void testConstructSingleIsr() {
		final var isr = createIsr("isr_gpio", 1);
		final var data = InterruptFunctionBoogieData.construct(isr);

		assertNotNull(data);
		assertEquals(1, data.getIrqNum());
		assertEquals("#isr_1_enabled", data.getEnabledVarName());
		assertNotNull(data.getEnabledExpression());
		assertNotNull(data.getEnabledDeclaration());
		assertNotNull(data.getEnabledLhs());
		assertNull(data.getThreadProcedure());
	}

	@Test
	public void testConstructMultipleIsrsIndependent() {
		final var isr1 = createIsr("isr_gpio", 1);
		final var isr2 = createIsr("isr_timer", 2);

		final var data1 = InterruptFunctionBoogieData.construct(isr1);
		final var data2 = InterruptFunctionBoogieData.construct(isr2);

		assertNotEquals(data1.getEnabledVarName(), data2.getEnabledVarName());
		assertEquals("#isr_1_enabled", data1.getEnabledVarName());
		assertEquals("#isr_2_enabled", data2.getEnabledVarName());
		assertNotEquals(data1.getIrqNum(), data2.getIrqNum());
		assertEquals(1, data1.getIrqNum());
		assertEquals(2, data2.getIrqNum());
	}

	@Test
	public void testVariableNamePattern() {
		assertEquals("#isr_0_enabled", InterruptFunctionBoogieData.constructEnabledVarName(0));
		assertEquals("#isr_1_enabled", InterruptFunctionBoogieData.constructEnabledVarName(1));
		assertEquals("#isr_42_enabled", InterruptFunctionBoogieData.constructEnabledVarName(42));
		assertEquals("#isr_100_enabled", InterruptFunctionBoogieData.constructEnabledVarName(100));
	}

	@Test
	public void testEnabledExpressionIsIdentifier() {
		final var isr = createIsr("isr_gpio", 3);
		final var data = InterruptFunctionBoogieData.construct(isr);

		final var expr = data.getEnabledExpression();
		assertTrue("Enabled expression should be an IdentifierExpression",
				expr instanceof IdentifierExpression);
		final var idExpr = (IdentifierExpression) expr;
		assertEquals("#isr_3_enabled", idExpr.getIdentifier());
	}

	@Test
	public void testDeclarationType() {
		final var isr = createIsr("isr_gpio", 5);
		final var data = InterruptFunctionBoogieData.construct(isr);

		final var decl = data.getEnabledDeclaration();
		assertNotNull(decl);
		assertTrue("Declaration should be a VariableDeclaration", decl instanceof VariableDeclaration);
		assertEquals(1, decl.getVariables().length);
		final var varList = decl.getVariables()[0];
		assertEquals(1, varList.getIdentifiers().length);
		assertEquals("#isr_5_enabled", varList.getIdentifiers()[0]);
		assertTrue("Variable type should be PrimitiveType", varList.getType() instanceof PrimitiveType);
		final var primType = (PrimitiveType) varList.getType();
		assertEquals("bool", primType.getName());
	}

	@Test
	public void testEnabledLhs() {
		final var isr = createIsr("isr_gpio", 7);
		final var data = InterruptFunctionBoogieData.construct(isr);

		final var lhs = data.getEnabledLhs();
		assertNotNull(lhs);
		assertEquals("#isr_7_enabled", lhs.getIdentifier());
	}

	@Test
	public void testConstructThreadName() {
		final var isr = createIsr("isr_gpio", 1);
		final var data = InterruptFunctionBoogieData.construct(isr);

		assertEquals("#isr_1_isr_gpio_thread", data.constructThreadName());
	}

	@Test
	public void testConstructThreadNameDifferentIsrs() {
		final var isr1 = createIsr("isr_gpio", 1);
		final var isr2 = createIsr("isr_timer", 2);

		final var data1 = InterruptFunctionBoogieData.construct(isr1);
		final var data2 = InterruptFunctionBoogieData.construct(isr2);

		assertNotEquals(data1.constructThreadName(), data2.constructThreadName());
		assertEquals("#isr_1_isr_gpio_thread", data1.constructThreadName());
		assertEquals("#isr_2_isr_timer_thread", data2.constructThreadName());
	}

	@Test
	public void testSetThreadProcedure() {
		final var isr = createIsr("isr_gpio", 1);
		final var data = InterruptFunctionBoogieData.construct(isr);

		assertNull(data.getThreadProcedure());

		final var threadProc = new Procedure(IGNORE_LOC, new Attribute[0], "#isr_1_isr_gpio_thread",
				new String[0], new VarList[0], new VarList[0], new Specification[0], null);
		data.setThreadProcedure(threadProc);

		assertEquals(threadProc, data.getThreadProcedure());
		assertEquals("#isr_1_isr_gpio_thread", data.getThreadProcedure().getIdentifier());
	}

	@Test
	public void testGetIsr() {
		final var isr = createIsr("isr_gpio", 1);
		final var data = InterruptFunctionBoogieData.construct(isr);

		assertEquals(isr, data.getIsr());
	}
}
