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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;

/**
 * Implementation of an abstract state of the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of the intervals. May be any Java-defined {@link Number}.
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class IntervalDomainState<ACTION, VARDECL>
        implements IAbstractState<ACTION, VARDECL>, IEvaluationResult<IntervalDomainState<ACTION, VARDECL>> {

	private static int sId;
	private final int mId;

	private final Map<String, VARDECL> mVariablesMap;
	private final Map<String, IntervalDomainValue> mValuesMap;
	private final Map<String, Boolean> mBooleanValuesMap;

	private final Logger mLogger;

	private boolean mIsFixpoint;

	private IntervalStateConverter<ACTION, VARDECL> mStateConverter;

	protected IntervalDomainState() {
		this(null, null);
	}

	protected IntervalDomainState(IntervalStateConverter<ACTION, VARDECL> stateConverter, Logger logger) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>();
		mValuesMap = new HashMap<String, IntervalDomainValue>();
		mBooleanValuesMap = new HashMap<String, Boolean>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
		mLogger = logger;
	}

	protected IntervalDomainState(IntervalStateConverter<ACTION, VARDECL> stateConverter, Logger logger,
	        Map<String, VARDECL> variablesMap, Map<String, IntervalDomainValue> valuesMap,
	        Map<String, Boolean> booleanValuesMap, boolean isFixpoint) {
		mStateConverter = stateConverter;
		mVariablesMap = new HashMap<String, VARDECL>(variablesMap);
		mValuesMap = new HashMap<String, IntervalDomainValue>(valuesMap);
		mBooleanValuesMap = new HashMap<String, Boolean>(booleanValuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
		mLogger = logger;
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

	protected Map<String, Boolean> getBooleanValues() {
		return new HashMap<String, Boolean>(mBooleanValuesMap);
	}

	protected void setValue(String name, IntervalDomainValue value) {
		assert name != null;
		assert value != null;
		final VARDECL key = mVariablesMap.get(name);
		assert key != null;
		final IntervalDomainValue valKey = mValuesMap.get(name);
		assert valKey != null;

		mValuesMap.put(name, value);
	}

	protected void setBooleanValue(String name, boolean value) {
		assert name != null;
		assert mVariablesMap.containsKey(name);
		assert mBooleanValuesMap.containsKey(name);

		mBooleanValuesMap.put(name, value);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final VARDECL old = newVarMap.put(name, variable);

		if (old != null) {
			throw new UnsupportedOperationException(
			        "Variable names must be disjoint. Variable " + name + " is already present.");
		}

		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, Boolean> newBooleanValMap = new HashMap<String, Boolean>(mBooleanValuesMap);

		if (variable instanceof IBoogieVar) {
			final IBoogieVar boogieVar = (IBoogieVar) variable;

			if (boogieVar.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) boogieVar.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					newBooleanValMap.put(name, false);
				} else {
					newValMap.put(name, new IntervalDomainValue());
				}

			} else {
				mLogger.warn("The IBoogieVar type " + boogieVar.getIType().getClass().toString()
				        + " is not implemented. Assuming top.");
				newValMap.put(name, new IntervalDomainValue());
			}
		} else {
			throw new UnsupportedOperationException(
			        "The type " + variable.getClass().toString() + " for variables is not implemented.");
		}

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger, newVarMap, newValMap,
		        newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		newValMap.remove(name);
		final Map<String, Boolean> newBooleanValMap = new HashMap<String, Boolean>(mBooleanValuesMap);
		newBooleanValMap.remove(name);

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger, newVarMap, newValMap,
		        newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, Boolean> newBooleanValMap = new HashMap<String, Boolean>(mBooleanValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newVarMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException(
				        "Variable names must be disjoint. The variable " + entry.getKey() + " is already present.");
			}
			newValMap.put(entry.getKey(), new IntervalDomainValue());

			if (entry.getValue() instanceof IBoogieVar) {
				final IBoogieVar boogieVar = (IBoogieVar) entry.getValue();

				if (boogieVar.getIType() instanceof PrimitiveType) {
					final PrimitiveType primitiveType = (PrimitiveType) boogieVar.getIType();

					if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
						newBooleanValMap.put(entry.getKey(), false);
					} else {
						newValMap.put(entry.getKey(), new IntervalDomainValue());
					}

				} else if (boogieVar.getIType() instanceof ArrayType) {
					// TODO:
					// We treat Arrays as normal variables for the time being.
					newValMap.put(entry.getKey(), new IntervalDomainValue());
				} else {
					throw new UnsupportedOperationException("The IBoogieVar type "
					        + boogieVar.getIType().getClass().toString() + " is not implemented.");
				}
			} else {
				throw new UnsupportedOperationException(
				        "The type " + entry.getValue().getClass().toString() + " for variables is not implemented.");
			}
		}

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger, newVarMap, newValMap,
		        newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, Boolean> newBooleanValMap = new HashMap<String, Boolean>(mBooleanValuesMap);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
			newBooleanValMap.remove(entry.getKey());
		}

		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger, newVarMap, newValMap,
		        newBooleanValMap, mIsFixpoint);
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
			if (entry.getValue().isBottom()) {
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
		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger, mVariablesMap, mValuesMap,
		        mBooleanValuesMap, value);
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
			        .append(mValuesMap.get(entry.getKey()).toString()).append("; ");
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
			if (!mValuesMap.get(entry.getKey()).equals(otherValue)) {
				return false;
			}
		}

		return true;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> copy() {
		return new IntervalDomainState<ACTION, VARDECL>(mStateConverter, mLogger,
		        new HashMap<String, VARDECL>(mVariablesMap), new HashMap<String, IntervalDomainValue>(mValuesMap),
		        new HashMap<String, Boolean>(mBooleanValuesMap), mIsFixpoint);
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

	/**
	 * Intersects <code>this</code> with another {@link IntervalDomainState} by piecewise intersecting all occurring
	 * variable intervals.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new {@link IAbstractState} that corresponds to the intersection of
	 */
	protected IAbstractState<ACTION, VARDECL> intersect(IntervalDomainState<ACTION, VARDECL> other) {
		assert other != null;

		assert hasSameVariables(other);

		final IntervalDomainState<ACTION, VARDECL> returnState = (IntervalDomainState<ACTION, VARDECL>) copy();

		for (Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			returnState.setValue(entry.getKey(), entry.getValue().intersect(other.mValuesMap.get(entry.getKey())));
		}

		for (Entry<String, Boolean> entry : mBooleanValuesMap.entrySet()) {
			returnState.setBooleanValue(entry.getKey(),
			        entry.getValue() && other.mBooleanValuesMap.get(entry.getKey()));
		}

		return returnState;
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		return script.term("true");
	}

	@Override
	public void setToBottom() {
		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			entry.setValue(new IntervalDomainValue(true));
		}
	}

	@Override
	public VARDECL getVariableType(String name) {
		assert name != null;
		final VARDECL var = mVariablesMap.get(name);
		assert var != null : "Unknown variable";
		return var;
	}
}
