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
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.ojalgo.OjAlgoSolver;
import de.uni_freiburg.informatik.ultimate.test.mocks.ConsoleLogger;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class LpSolverTest {

	final ILogger logger = new ConsoleLogger();

	@Test
	public void testojAlgoLpSolver() {

		final OjAlgoSolver<BigDecimal> solver = new OjAlgoSolver<>(logger, BigDecimal.class);
		final List<String> variables = new ArrayList<>();
		variables.add("x");
		variables.add("y");
		solver.createNewLpInstance(variables);

		final List<LinearConstraint<BigDecimal>> constraintList = new ArrayList<>();

		final LinearConstraint<BigDecimal> constrX = new LinearConstraint<>("x-constraint");
		constrX.addCoefficient("x", BigDecimal.ONE);
		constrX.addCoefficient("y", BigDecimal.ZERO);
		constrX.setLower(BigDecimal.ZERO);
		constrX.setUpper(new BigDecimal(4));
		constraintList.add(constrX);

		final LinearConstraint<BigDecimal> constrY = new LinearConstraint<>("y-constraint");
		constrY.addCoefficient("x", BigDecimal.ZERO);
		constrY.addCoefficient("y", BigDecimal.ONE);
		constrY.setLower(BigDecimal.ZERO);
		constrY.setUpper(new BigDecimal(4));
		constraintList.add(constrY);

		final LinearConstraint<BigDecimal> slope = new LinearConstraint<>("slope");
		slope.addCoefficient("x", new BigDecimal("0.75"));
		slope.addCoefficient("y", BigDecimal.ONE);
		slope.setUpper(new BigDecimal(3));
		constraintList.add(slope);

		solver.addVariableConstraints(constraintList);

		final BigDecimal maxX = solver.getMaximumValue("x");
		final BigDecimal maxY = solver.getMaximumValue("y");
		final BigDecimal minX = solver.getMinimumValue("x");
		final BigDecimal minY = solver.getMinimumValue("y");

		logger.info("Computed max value for x: " + maxX);
		logger.info("Computed max value for y: " + maxY);
		logger.info("Computed min value for x: " + minX);
		logger.info("Computed min value for y: " + minY);

		solver.deleteLpInstance();

		assertTrue(maxX.compareTo(new BigDecimal(4)) == 0);
		assertTrue(minX.compareTo(BigDecimal.ZERO) == 0);
		assertTrue(maxY.compareTo(new BigDecimal(3)) == 0);
		assertTrue(minY.compareTo(BigDecimal.ZERO) == 0);
	}

	@Test
	public void testojAlgoLpSolverNegative() {
		final OjAlgoSolver<BigDecimal> solver = new OjAlgoSolver<>(logger, BigDecimal.class);
		final List<String> variables = new ArrayList<>();
		variables.add("x");
		variables.add("y");
		solver.createNewLpInstance(variables);

		final List<LinearConstraint<BigDecimal>> constraintList = new ArrayList<>();

		final LinearConstraint<BigDecimal> constrX = new LinearConstraint<>("x-constraint");
		constrX.addCoefficient("x", BigDecimal.ONE);
		constrX.addCoefficient("y", BigDecimal.ZERO);
		constrX.setLower(new BigDecimal(-3));
		constrX.setUpper(new BigDecimal(-1));
		constraintList.add(constrX);

		final LinearConstraint<BigDecimal> constrY = new LinearConstraint<>("y-constraint");
		constrY.addCoefficient("x", BigDecimal.ZERO);
		constrY.addCoefficient("y", BigDecimal.ONE);
		constrY.setLower(BigDecimal.ONE);
		constrY.setUpper(new BigDecimal(4));
		constraintList.add(constrY);

		final LinearConstraint<BigDecimal> slope = new LinearConstraint<>("slope");
		slope.addCoefficient("x", new BigDecimal(-1));
		slope.addCoefficient("y", BigDecimal.ONE);
		slope.setUpper(new BigDecimal(3));
		constraintList.add(slope);

		solver.addVariableConstraints(constraintList);

		final BigDecimal maxX = solver.getMaximumValue("x");
		final BigDecimal maxY = solver.getMaximumValue("y");
		final BigDecimal minX = solver.getMinimumValue("x");
		final BigDecimal minY = solver.getMinimumValue("y");

		logger.info("Computed max value for x: " + maxX);
		logger.info("Computed max value for y: " + maxY);
		logger.info("Computed min value for x: " + minX);
		logger.info("Computed min value for y: " + minY);

		solver.deleteLpInstance();

		assertTrue(maxX.compareTo(new BigDecimal(-1)) == 0);
		assertTrue(minX.compareTo(new BigDecimal(-2)) == 0);
		assertTrue(maxY.compareTo(new BigDecimal(2)) == 0);
		assertTrue(minY.compareTo(BigDecimal.ONE) == 0);
	}

	@Test
	public void testojAlgoLpSolverUnbounded() {
		final OjAlgoSolver<BigDecimal> solver = new OjAlgoSolver<>(logger, BigDecimal.class);
		final List<String> variables = new ArrayList<>();
		variables.add("x");
		variables.add("y");
		solver.createNewLpInstance(variables);

		final List<LinearConstraint<BigDecimal>> constraintList = new ArrayList<>();

		final LinearConstraint<BigDecimal> constrX = new LinearConstraint<>("x-constraint");
		constrX.addCoefficient("x", BigDecimal.ONE);
		constrX.addCoefficient("y", BigDecimal.ZERO);
		constrX.setLower(BigDecimal.ONE);
		constraintList.add(constrX);

		final LinearConstraint<BigDecimal> constrY = new LinearConstraint<>("y-constraint");
		constrY.addCoefficient("x", BigDecimal.ZERO);
		constrY.addCoefficient("y", BigDecimal.ONE);
		constrY.setLower(BigDecimal.ONE);
		constraintList.add(constrY);

		final LinearConstraint<BigDecimal> slope = new LinearConstraint<>("slope");
		slope.addCoefficient("x", BigDecimal.ONE);
		slope.addCoefficient("y", BigDecimal.ONE);
		slope.setUpper(new BigDecimal(3));
		constraintList.add(slope);

		solver.addVariableConstraints(constraintList);

		final BigDecimal maxX = solver.getMaximumValue("x");
		final BigDecimal maxY = solver.getMaximumValue("y");
		final BigDecimal minX = solver.getMinimumValue("x");
		final BigDecimal minY = solver.getMinimumValue("y");

		logger.info("Computed max value for x: " + maxX);
		logger.info("Computed max value for y: " + maxY);
		logger.info("Computed min value for x: " + minX);
		logger.info("Computed min value for y: " + minY);

		solver.deleteLpInstance();

		assertTrue(maxX.compareTo(new BigDecimal(2)) == 0);
		assertTrue(minX.compareTo(BigDecimal.ONE) == 0);
		assertTrue(maxY.compareTo(new BigDecimal(2)) == 0);
		assertTrue(minY.compareTo(BigDecimal.ONE) == 0);
	}

	@Test
	public void testojAlgoLpSolverUnbounded1() {
		final OjAlgoSolver<BigDecimal> solver = new OjAlgoSolver<>(logger, BigDecimal.class);
		final List<String> variables = new ArrayList<>();
		variables.add("x");
		variables.add("y");
		solver.createNewLpInstance(variables);

		final List<LinearConstraint<BigDecimal>> constraintList = new ArrayList<>();

		final LinearConstraint<BigDecimal> constrX = new LinearConstraint<>("x-constraint");
		constrX.addCoefficient("x", BigDecimal.ONE);
		constrX.addCoefficient("y", BigDecimal.ZERO);
		constrX.setLower(BigDecimal.ZERO);
		constraintList.add(constrX);

		final LinearConstraint<BigDecimal> constrY = new LinearConstraint<>("y-constraint");
		constrY.addCoefficient("x", BigDecimal.ZERO);
		constrY.addCoefficient("y", BigDecimal.ONE);
		constrY.setLower(BigDecimal.ZERO);
		constraintList.add(constrY);

		final LinearConstraint<BigDecimal> slope = new LinearConstraint<>("slope");
		slope.addCoefficient("x", BigDecimal.ONE);
		slope.addCoefficient("y", BigDecimal.ONE);
		slope.setLower(new BigDecimal(2));
		constraintList.add(slope);

		solver.addVariableConstraints(constraintList);

		final BigDecimal maxX = solver.getMaximumValue("x");
		final BigDecimal maxY = solver.getMaximumValue("y");
		final BigDecimal minX = solver.getMinimumValue("x");
		final BigDecimal minY = solver.getMinimumValue("y");

		logger.info("Computed max value for x: " + maxX);
		logger.info("Computed max value for y: " + maxY);
		logger.info("Computed min value for x: " + minX);
		logger.info("Computed min value for y: " + minY);

		solver.deleteLpInstance();

		assertTrue(maxX == null);
		assertTrue(minX.compareTo(BigDecimal.ZERO) == 0);
		assertTrue(maxY == null);
		assertTrue(minY.compareTo(BigDecimal.ZERO) == 0);
	}
}
