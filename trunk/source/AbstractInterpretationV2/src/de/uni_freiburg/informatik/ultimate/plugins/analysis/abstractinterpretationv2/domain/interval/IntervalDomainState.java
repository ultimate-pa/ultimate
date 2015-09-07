/*
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

/**
 * Implementation of an abstract state of the {@link IntervalDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <T>
 *            The type of the intervals. May be any Java-defined {@link Number}.
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class IntervalDomainState<ACTION, VARDECL> implements IAbstractState<ACTION, VARDECL>,
        IEvaluationResult<IntervalDomainState<ACTION, VARDECL>> {

	private static int sId;
	private final int mId;

	private final Map<String, VARDECL> mVariablesMap;
	private final Map<String, IntervalDomainValue> mValuesMap;

	private boolean mIsFixpoint;

	private IntervalStateConverter<ACTION, VARDECL> mStateConverter;

	protected IntervalDomainState() {
		this(null);
	}

	protected IntervalDomainState(IntervalStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>();
		mValuesMap = new HashMap<String, IntervalDomainValue>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
	}

	protected IntervalDomainState(IntervalStateConverter<ACTION, VARDECL> stateConverter,
	        Map<String, VARDECL> variablesMap, Map<String, IntervalDomainValue> valuesMap, boolean isFixpoint) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>(variablesMap);
		mValuesMap = new HashMap<String, IntervalDomainValue>(valuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
	}

	protected void setStateConverter(IntervalStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	protected Map<String, VARDECL> getVariables() {
		return new HashMap<String, VARDECL>(mVariablesMap);
	}

	protected Map<String, IntervalDomainValue> getValues() {
		return new HashMap<String, IntervalDomainValue>(mValuesMap);
	}

	protected void setValue(String name, IntervalDomainValue value) {
		assert name != null;
		assert value != null;
		assert mVariablesMap.containsKey(name);
		assert mValuesMap.containsKey(name);

		mValuesMap.put(name, value);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final VARDECL old = newVarMap.put(name, variable);

		if (old != null) {
			throw new UnsupportedOperationException("Variable names must be disjoint. Variable " + name
			        + " is already present.");
		}

		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		newValMap.put(name, new IntervalDomainValue());

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		newValMap.remove(name);

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newVarMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names must be disjoint. The variable "
				        + entry.getKey() + " is already present.");
			}
			newValMap.put(entry.getKey(), new IntervalDomainValue());
		}

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
		}

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, newVarMap, newValMap, mIsFixpoint);
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
		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			if (entry.getValue().getResult().isBottom()) {
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
		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mVariablesMap, mValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = [lb1 ; ub1]; var2 : type2 = [lb2 ; ub2]; ...", where lb is a lower
	 * bound and ub is an upper bound. Note that a value may also be "{}" if the corresponding interval is &bot;.
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final Entry<String, VARDECL> entry : mVariablesMap.entrySet()) {
			stringBuilder.append(entry.getKey()).append(':').append(entry.getValue()).append(" = ")
			        .append(mValuesMap.get(entry.getKey()).getResult().toString()).append("; ");
		}
		return stringBuilder.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public boolean isEqualTo(IAbstractState<ACTION, VARDECL> other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		final IntervalDomainState<ACTION, VARDECL> comparableOther = mStateConverter.getCheckedState(other);

		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IntervalDomainValue otherValue = comparableOther.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).getResult().equals(otherValue.getResult())) {
				return false;
			}
		}

		return true;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> copy() {
		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, new HashMap<String, VARDECL>(mVariablesMap),
		        new HashMap<String, IntervalDomainValue>(mValuesMap), mIsFixpoint);
	}

	@Override
	public IntervalDomainState<ACTION, VARDECL> getResult() {
		return this;
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
		final IntervalDomainState<ACTION, VARDECL> comparableOther = (IntervalDomainState<ACTION, VARDECL>) other;

		return isEqualTo(comparableOther);
	}

	/**
	 * Returns <code>true</code> if and only if {@link this} has the same variables as other.
	 * 
	 * @param other
	 *            The other state to check for same variables.
	 * @return <code>true</code> iff the variables are the same, <code>false</code> otherwise.
	 */
	protected boolean hasSameVariables(IAbstractState<ACTION, VARDECL> other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof IntervalDomainState)) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		final IntervalDomainState<ACTION, VARDECL> comparableOther = mStateConverter.getCheckedState(other);
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
}
