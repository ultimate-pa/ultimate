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

import java.math.BigDecimal;
import java.util.List;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface ILpSolver<T extends Number> {

	/**
	 * Creates a new Linear Program Solver instance with a set of variables.
	 * 
	 * @param variables
	 *            The list of variables occurring in the linear program.
	 */
	public void createNewLpInstance(List<String> variables);

	/**
	 * Deletes the Linear Program Solver instance. This method should be called when the linear program is not needed
	 * anymore. Some solvers will free memory when instructed to delete the linear program.
	 * 
	 * <p>
	 * Note: After {@link #deleteLpInstance()} is called, no operations can be performed on the linear program anymore.
	 * </p>
	 */
	public void deleteLpInstance();

	/**
	 * Adds a constraint in the form of a {@link LinearConstraint} to the linear program.
	 * 
	 * @param constraint
	 *            The constraint to add to the linear program.
	 */
	public void addVariableConstraint(LinearConstraint<T> constraint);

	/**
	 * Adds a list of {@link LinearConstraint}s to the linear program.
	 * 
	 * @param constraintList
	 *            The list of {@link LinearConstraint}s.
	 */
	public void addVariableConstraints(List<LinearConstraint<T>> constraintList);

	/**
	 * Returns the computed maximum for the variable with name <code>name</code>. If the value corresponds to &infin;,
	 * the returned value will be <code>null</code>.
	 * 
	 * <p>
	 * Note: You must call {@link #createNewLpInstance(List)} first, in order to be able to run this function.
	 * </p>
	 * 
	 * @param name
	 *            The name of the variable.
	 * @return The computed maximum value for the variable, or <code>null</code> if the value is unbounded (&infin;).
	 */
	public BigDecimal getMaximumValue(String name);

	/**
	 * Returns the computed miminum for the variable with name <code>name</code>. If the value corresponds to &infin;,
	 * the returned value will be <code>null</code>.
	 * 
	 * <p>
	 * Note: You must call {@link #createNewLpInstance(List)} first, in order to be able to run this function.
	 * </p>
	 * 
	 * @param name
	 *            The name of the variable.
	 * @return The computed minimum value for the variable, or <code>null</code> if the value is unbounded (&infin;).
	 */
	public BigDecimal getMinimumValue(String name);

}
