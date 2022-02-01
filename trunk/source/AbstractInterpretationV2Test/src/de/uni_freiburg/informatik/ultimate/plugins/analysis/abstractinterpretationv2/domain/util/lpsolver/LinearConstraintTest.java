/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver;

import static org.junit.Assert.assertTrue;

import java.math.BigDecimal;

import org.junit.Test;

/**
 * Test class for {@link LinearConstraint}s.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class LinearConstraintTest {

	@Test
	public void TestLinearConstraint() {
		final LinearConstraint<BigDecimal> xconstr = new LinearConstraint<>("x-constraint");

		xconstr.addCoefficient("x", BigDecimal.ONE);
		xconstr.addCoefficient("y", BigDecimal.ZERO);
		xconstr.setLower(BigDecimal.ZERO);
		xconstr.setUpper(BigDecimal.TEN);

		assertTrue(xconstr.getName() == "x-constraint");
		assertTrue(xconstr.getVariableCount() == 2);
		assertTrue(xconstr.getCoefficient("x").equals(BigDecimal.ONE));
		assertTrue(xconstr.getCoefficient("y").equals(BigDecimal.ZERO));
		assertTrue(xconstr.getLower().equals(BigDecimal.ZERO));
		assertTrue(xconstr.getUpper().equals(BigDecimal.TEN));

		System.out.println(xconstr.toLogString());
	}
}
