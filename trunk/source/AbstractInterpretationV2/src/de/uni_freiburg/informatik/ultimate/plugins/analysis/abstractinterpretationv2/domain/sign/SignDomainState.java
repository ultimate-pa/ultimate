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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;

/**
 * Implementation of an abstract state of the {@link SignDomain}.
 * 
 * <p>
 * Such a state stores {@link SignDomainValue}s.
 * </p>
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class SignDomainState<ACTION, VARDECL> implements IAbstractState<ACTION, VARDECL>,
        IEvaluationResult<SignDomainState<ACTION, VARDECL>> {

	private static int sId;
	private final int mId;

	private final Map<String, VARDECL> mVariablesMap;
	private final Map<String, SignDomainValue> mValuesMap;

	private boolean mIsFixpoint;

	private SignStateConverter<ACTION, VARDECL> mStateConverter;

	protected SignDomainState() {
		this(null);
	}

	protected SignDomainState(SignStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>();
		mValuesMap = new HashMap<String, SignDomainValue>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
	}

	protected SignDomainState(SignStateConverter<ACTION, VARDECL> stateConverter, Map<String, VARDECL> variablesMap,
	        Map<String, SignDomainValue> valuesMap, boolean isFixpoint) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>(variablesMap);
		mValuesMap = new HashMap<String, SignDomainValue>(valuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
	}

	protected void setStateConverter(SignStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final VARDECL old = newVarMap.put(name, variable);
		if (old != null) {
			throw new UnsupportedOperationException("Variable names must be disjoint.");
		}

		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.put(name, new SignDomainValue(Values.TOP));

		return new SignDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.remove(name);

		return new SignDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newVarMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names must be disjoint.");
			}
			newValMap.put(entry.getKey(), new SignDomainValue(Values.TOP));
		}

		return new SignDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
		}

		return new SignDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public boolean containsVariable(String name) {
		return mVariablesMap.containsKey(name);
	}

	@Override
	public boolean isEmpty() {
		return mVariablesMap.isEmpty();
	}

	@Override
	public boolean isBottom() {
		for (final Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			if (entry.getValue().getResult() == Values.BOTTOM) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> setFixpoint(boolean value) {
		return new SignDomainState<ACTION, VARDECL>(mStateConverter, mVariablesMap, mValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = value1; var2 : type2 = value2; ...".
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuffer = new StringBuilder();
		for (final Entry<String, VARDECL> entry : mVariablesMap.entrySet()) {
			stringBuffer.append(entry.getKey()).append(':').append(entry.getValue()).append(" = ")
			        .append(mValuesMap.get(entry.getKey()).getResult().toString()).append("; ");
		}
		return stringBuffer.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public int hashCode() {
		return mId;
	}

	@Override
	public boolean equals(Object other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (this.getClass() != other.getClass()) {
			return false;
		}

		@SuppressWarnings("unchecked")
		final SignDomainState<ACTION, VARDECL> comparableOther = (SignDomainState<ACTION, VARDECL>) other;

		return isEqualTo(comparableOther);
	}

	@Override
	public boolean isEqualTo(IAbstractState<ACTION, VARDECL> other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		final SignDomainState<ACTION, VARDECL> comparableOther = mStateConverter.getCheckedState(other);
		for (final Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			final SignDomainValue otherValue = comparableOther.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).getResult().equals(otherValue.getResult())) {
				return false;
			}
		}

		return true;
	}

	protected boolean hasSameVariables(IAbstractState<ACTION, VARDECL> other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof SignDomainState)) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		final SignDomainState<ACTION, VARDECL> comparableOther = mStateConverter.getCheckedState(other);
		if (comparableOther.mVariablesMap.size() != mVariablesMap.size()) {
			return false;
		}

		for (final Entry<String, VARDECL> entry : mVariablesMap.entrySet()) {
			final VARDECL otherType = comparableOther.mVariablesMap.get(entry.getKey());
			if (!entry.getValue().equals(otherType)) {
				return false;
			}
		}

		return true;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> copy() {
		return new SignDomainState<ACTION, VARDECL>(mStateConverter, new HashMap<String, VARDECL>(mVariablesMap),
		        new HashMap<String, SignDomainValue>(mValuesMap), mIsFixpoint);
	}

	protected Map<String, VARDECL> getVariables() {
		return new HashMap<String, VARDECL>(mVariablesMap);
	}

	protected Map<String, SignDomainValue> getValues() {
		return new HashMap<String, SignDomainValue>(mValuesMap);
	}

	protected void setValue(String name, SignDomainValue value) {
		assert name != null;
		assert value != null;
		assert mVariablesMap.containsKey(name);
		assert mValuesMap.containsKey(name);

		mValuesMap.put(name, value);
	}

	/**
	 * Intersects {@link this} with another {@link SignDomainState} by intersecting each value of each variable.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new state which corresponds to the intersection.
	 */
	protected SignDomainState<ACTION, VARDECL> intersect(SignDomainState<ACTION, VARDECL> other) {
		assert hasSameVariables(other);

		final SignDomainState<ACTION, VARDECL> newState = (SignDomainState<ACTION, VARDECL>) this.copy();

		for (final Entry<String, VARDECL> variable : mVariablesMap.entrySet()) {
			final String key = variable.getKey();
			newState.setValue(key, mValuesMap.get(key).intersect(other.mValuesMap.get(key)));
		}

		return newState;
	}

	/**
	 * Sets all variables to &bot;.
	 */
	public void setToBottom() {
		for (final Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			entry.setValue(new SignDomainValue(Values.BOTTOM));
		}
	}

	@Override
	public SignDomainState<ACTION, VARDECL> getResult() {
		return this;
	}
}
