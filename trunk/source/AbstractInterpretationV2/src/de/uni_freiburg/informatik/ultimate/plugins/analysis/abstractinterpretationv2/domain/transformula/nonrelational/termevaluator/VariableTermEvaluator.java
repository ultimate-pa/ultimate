/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Evaluator for variable terms.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class VariableTermEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends NonrelationalState<STATE, VALUE>>
		implements ITermEvaluator<VALUE, STATE> {

	private final String mVariable;
	private final Set<String> mVariableNames;
	private final Sort mSort;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;
	private IProgramVarOrConst mVar;

	private boolean mContainsBoolean = false;

	protected VariableTermEvaluator(final String variableName, final Sort sort,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		mVariable = variableName;
		mVariableNames = Collections.singleton(variableName);
		mSort = sort;
		mNonrelationalValueFactory = nonrelationalValueFactory;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final List<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		VALUE val;
		BooleanValue returnBool = BooleanValue.TOP;

		for (final IProgramVarOrConst stateVar : currentState.getVariables()) {
			if (stateVar.getGloballyUniqueId().equals(mVariable)) {
				mVar = stateVar;
				break;
			}
		}
		if (mVar == null) {
			throw new UnsupportedOperationException("Variable " + mVariable + " was not found in current state.");
		}

		// TODO: Add array support.
		final Function<IProgramVarOrConst, Triple<VALUE, BooleanValue, Boolean>> varFunction =
				var -> new Triple<>(currentState.getValue(var), BooleanValue.TOP, false);
		final Function<IProgramVarOrConst, Triple<VALUE, BooleanValue, Boolean>> boolFunction =
				var -> new Triple<>(mNonrelationalValueFactory.createTopValue(), currentState.getBooleanValue(var),
						true);

		final Triple<VALUE, BooleanValue, Boolean> valueTriple =
				TypeUtils.applyVariableFunction(varFunction, boolFunction, null, mVar);

		val = valueTriple.getFirst();
		if (valueTriple.getThird()) {
			returnBool = valueTriple.getSecond();
			mContainsBoolean = true;
		}

		if (val.isBottom() || returnBool.isBottom()) {
			returnList.add(new NonrelationalEvaluationResult<>(mNonrelationalValueFactory.createBottomValue(),
					BooleanValue.BOTTOM));
		} else {
			returnList.add(new NonrelationalEvaluationResult<>(val, returnBool));
		}

		return returnList;
	}

	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE state) {
		assert computedValue != null;
		assert state != null;

		final List<STATE> returnList = new ArrayList<>();

		if (mContainsBoolean) {
			returnList.add(state.setBooleanValue(mVar, computedValue.getBooleanValue()));
		} else {
			returnList.add(state.setValue(mVar, computedValue.getValue()));
		}
		return returnList;
	}

	@Override
	public void addSubEvaluator(final ITermEvaluator<VALUE, STATE> evaluator) {
		throw new UnsupportedOperationException("Cannot add sub evaluator to variable term evaluators.");
	}

	@Override
	public boolean hasFreeOperands() {
		return false;
	}

	@Override
	public boolean containsBool() {
		return mContainsBoolean;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableNames;
	}

	@Override
	public String toString() {
		return mVariable;
	}

}
