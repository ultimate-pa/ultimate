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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.ojalgo;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.ojalgo.array.Array1D;
import org.ojalgo.optimisation.Expression;
import org.ojalgo.optimisation.ExpressionsBasedModel;
import org.ojalgo.optimisation.Optimisation.Result;
import org.ojalgo.optimisation.Variable;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.ILpSolver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.lpsolver.LinearConstraint;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class OjAlgoSolver<T extends Number> implements ILpSolver<T> {

	private final ILogger mLogger;

	private ExpressionsBasedModel mModel;

	private boolean mModelIsPresent = false;

	private final Class<T> mType;

	private Result mMaximizationResult;
	private Result mMinimizationResult;

	private List<Variable> mVariableList;

	private Map<String, Integer> mVariableIndexMap;
	private Map<Integer, String> mVariableNameMap;

	public OjAlgoSolver(ILogger logger, Class<T> type) {
		mLogger = logger;
		mModelIsPresent = false;
		mType = type;
	}

	@Override
	public void createNewLpInstance(List<String> variables) {
		if (mModelIsPresent) {
			throw new UnsupportedOperationException(
			        "A linear program model is already present. Delete the model first.");
		}

		mVariableList = new ArrayList<>();
		mVariableIndexMap = new HashMap<>();
		mVariableNameMap = new HashMap<>();

		int index = 0;
		for (final String var : variables) {
			final Integer lastIndex = mVariableIndexMap.put(var, index);
			final String lastName = mVariableNameMap.put(index++, var);
			if (lastIndex != null || lastName != null) {
				throw new UnsupportedOperationException(
				        "The variable " + var + " is already present and cannot be added again.");
			}

			mVariableList.add(Variable.make(var));
		}

		if (mVariableList.isEmpty()) {
			throw new UnsupportedOperationException("The variable list to be added to the model must not be empty.");
		}

		mModel = new ExpressionsBasedModel(mVariableList);
		mModelIsPresent = true;
		mLogger.debug("Created new linear program instance.");
	}

	@Override
	public void addVariableConstraint(LinearConstraint<T> constraint) {
		assert mModelIsPresent : "The model has not been initialized, yet. You need to call createNewLpInstance first.";
		assert constraint != null;

		mLogger.debug("Adding constraint: " + constraint.toLogString());

		final String expressionName = constraint.getName();

		final Expression exp = mModel.addExpression(expressionName);

		if (constraint.isLowerBounded()) {
			exp.lower(constraint.getLower());
		}

		if (constraint.isUpperBounded()) {
			exp.upper(constraint.getUpper());
		}

		final int numVars = constraint.getVariableCount();
		Array1D<?> factors;

		if (mType.equals(BigDecimal.class)) {
			factors = Array1D.BIG.makeZero(numVars);
		} else if (mType.equals(Double.class)) {
			factors = Array1D.PRIMITIVE.makeZero(numVars);
		} else {
			throw new UnsupportedOperationException("The type " + mType.getName() + " cannot be handled.");
		}

		for (final String var : constraint.getVariableNames()) {
			final Integer index = mVariableIndexMap.get(var);
			final T coeff = constraint.getCoefficient(var);

			factors.set(index, coeff);
		}

		exp.setLinearFactors(mVariableList, factors);
	}

	@Override
	public void deleteLpInstance() {
		mModel.dispose();
		mModel = null;
		mModelIsPresent = false;
		mLogger.debug("Linear program instance deleted.");
	}

	@Override
	public void addVariableConstraints(List<LinearConstraint<T>> constraintList) {
		for (final LinearConstraint<T> constraint : constraintList) {
			addVariableConstraint(constraint);
		}
	}

	private void maximize() {
		mLogger.debug("Starting maximization...");
		mMaximizationResult = mModel.maximise();
		mLogger.debug("Optimization result for maximization: " + mMaximizationResult.getState());
	}

	private void minimize() {
		mLogger.debug("Starting minimization...");
		mMinimizationResult = mModel.minimise();
		mLogger.debug("Optimization result for minimization: " + mMinimizationResult.getState());
	}

	@Override
	public BigDecimal getMaximumValue(String name) {
		if (mMaximizationResult == null) {
			maximize();
		}

		final Integer index = mVariableIndexMap.get(name);
		if (index == null) {
			throw new InternalError("The variable " + name + " does not occur in the variable index map.");
		}

		return mModel.getVariable(index).getUpperLimit();
	}

	@Override
	public BigDecimal getMinimumValue(String name) {
		if (mMinimizationResult == null) {
			minimize();
		}

		final Integer index = mVariableIndexMap.get(name);
		if (index == null) {
			throw new InternalError("The variable " + name + " does not occur in the variable index map.");
		}

		return mModel.getVariable(index).getLowerLimit();
	}
}
