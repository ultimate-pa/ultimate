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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of an abstract state of the {@link SignDomain}.
 * 
 * <p>
 * Such a state stores {@link SignDomainValue}s.
 * </p>
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action.
 * @param <IBoogieVar>
 *            Any variable declaration.
 */
public class SignDomainState
		implements IAbstractState<SignDomainState, CodeBlock, IBoogieVar>, IEvaluationResult<SignDomainState> {

	private static int sId;
	private final int mId;

	private final Map<String, IBoogieVar> mVariablesMap;
	private final Map<String, SignDomainValue> mValuesMap;

	private boolean mIsFixpoint;

	protected SignDomainState() {
		mVariablesMap = new HashMap<String, IBoogieVar>();
		mValuesMap = new HashMap<String, SignDomainValue>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
	}

	protected SignDomainState(Map<String, IBoogieVar> variablesMap, Map<String, SignDomainValue> valuesMap,
			boolean isFixpoint) {
		mVariablesMap = new HashMap<String, IBoogieVar>(variablesMap);
		mValuesMap = new HashMap<String, SignDomainValue>(valuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
	}

	@Override
	public SignDomainState addVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final IBoogieVar old = newVarMap.put(name, variable);
		if (old != null) {
			throw new UnsupportedOperationException("Variable names must be disjoint.");
		}

		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.put(name, new SignDomainValue(Values.TOP));

		return new SignDomainState(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public SignDomainState removeVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.remove(name);

		return new SignDomainState(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public SignDomainState addVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			final IBoogieVar old = newVarMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names must be disjoint.");
			}
			newValMap.put(entry.getKey(), new SignDomainValue(Values.TOP));
		}

		return new SignDomainState(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public SignDomainState removeVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
		}

		return new SignDomainState(newVarMap, newValMap, mIsFixpoint);
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
	public SignDomainState setFixpoint(boolean value) {
		return new SignDomainState(mVariablesMap, mValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = value1; var2 : type2 = value2; ...".
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuffer = new StringBuilder();
		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
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

		return isEqualTo((SignDomainState) other);
	}

	@Override
	public boolean isEqualTo(SignDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}
		for (final Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			final SignDomainValue otherValue = other.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).getResult().equals(otherValue.getResult())) {
				return false;
			}
		}
		return true;
	}

	protected boolean hasSameVariables(SignDomainState other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof SignDomainState)) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		if (other.mVariablesMap.size() != mVariablesMap.size()) {
			return false;
		}

		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			final IBoogieVar otherType = other.mVariablesMap.get(entry.getKey());
			if (!entry.getValue().equals(otherType)) {
				return false;
			}
		}

		return true;
	}

	public SignDomainState copy() {
		return new SignDomainState(new HashMap<String, IBoogieVar>(mVariablesMap),
				new HashMap<String, SignDomainValue>(mValuesMap), mIsFixpoint);
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mVariablesMap);
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
	protected SignDomainState intersect(SignDomainState other) {
		assert hasSameVariables(other);

		final SignDomainState newState = (SignDomainState) this.copy();

		for (final Entry<String, IBoogieVar> variable : mVariablesMap.entrySet()) {
			final String key = variable.getKey();
			newState.setValue(key, mValuesMap.get(key).intersect(other.mValuesMap.get(key)));
		}

		return newState;
	}

	public void setToBottom() {
		for (final Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			entry.setValue(new SignDomainValue(Values.BOTTOM));
		}
	}

	@Override
	public SignDomainState getResult() {
		return this;
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		return script.term("true");
	}

	@Override
	public IBoogieVar getVariableType(String name) {
		assert name != null;
		assert mVariablesMap.containsKey(name);

		return mVariablesMap.get(name);
	}

	@Override
	public SignDomainState overwrite(final SignDomainState dominator) {
		throw new UnsupportedOperationException("not yet implemented");
	}
}
