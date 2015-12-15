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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of an abstract state of the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainState
        implements IAbstractState<IntervalDomainState, CodeBlock, IBoogieVar>, IEvaluationResult<IntervalDomainState> {

	private static int sId;
	private final int mId;

	private final Map<String, IBoogieVar> mVariablesMap;
	private final Map<String, IntervalDomainValue> mValuesMap;
	private final Map<String, BooleanValue> mBooleanValuesMap;

	private final Logger mLogger;

	private boolean mIsFixpoint;

	protected IntervalDomainState() {
		this(null);
	}

	protected IntervalDomainState(Logger logger) {
		mVariablesMap = new HashMap<String, IBoogieVar>();
		mValuesMap = new HashMap<String, IntervalDomainValue>();
		mBooleanValuesMap = new HashMap<String, BooleanValue>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
		mLogger = logger;
	}

	protected IntervalDomainState(Logger logger, Map<String, IBoogieVar> variablesMap,
	        Map<String, IntervalDomainValue> valuesMap, Map<String, BooleanValue> booleanValuesMap,
	        boolean isFixpoint) {
		mVariablesMap = new HashMap<String, IBoogieVar>(variablesMap);
		mValuesMap = new HashMap<String, IntervalDomainValue>(valuesMap);
		mBooleanValuesMap = new HashMap<String, BooleanValue>(booleanValuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
		mLogger = logger;
	}

	protected Map<String, IBoogieVar> getVariables() {
		return new HashMap<String, IBoogieVar>(mVariablesMap);
	}

	protected Map<String, IntervalDomainValue> getValues() {
		return new HashMap<String, IntervalDomainValue>(mValuesMap);
	}

	protected Map<String, BooleanValue> getBooleanValues() {
		return new HashMap<String, BooleanValue>(mBooleanValuesMap);
	}

	protected void setValue(String name, IntervalDomainValue value) {
		assert name != null;
		assert value != null;
		assert mVariablesMap.get(name) != null : "Variable unknown";
		assert mValuesMap.get(name) != null : "Variable not in values map";
		mValuesMap.put(name, value);
	}

	protected void setBooleanValue(String name, boolean value) {
		assert name != null;
		assert mVariablesMap.get(name) != null : "Variable unknown";
		assert mBooleanValuesMap.get(name) != null : "Boolean variable not in values map";

		mBooleanValuesMap.put(name, new BooleanValue(value));
	}

	protected void setBooleanValue(String name, BooleanValue.Value value) {
		assert name != null;
		assert mVariablesMap.get(name) != null : "Variable unknown";
		assert mBooleanValuesMap.get(name) != null : "Boolean variable not in values map";

		mBooleanValuesMap.put(name, new BooleanValue(value));
	}

	protected void setBooleanValue(String name, BooleanValue value) {
		assert name != null;
		assert mVariablesMap.get(name) != null : "Variable unknown";
		assert mBooleanValuesMap.get(name) != null : "Boolean variable not in values map";

		mBooleanValuesMap.put(name, new BooleanValue(value));
	}

	@Override
	public IntervalDomainState addVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final IBoogieVar old = newVarMap.put(name, variable);

		if (old != null) {
			throw new UnsupportedOperationException(
			        "Variable names must be disjoint. Variable " + name + " is already present.");
		}

		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);

		if (variable.getIType() instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) variable.getIType();

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				newBooleanValMap.put(name, new BooleanValue(false));
			} else if (variable.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				newValMap.put(name, new IntervalDomainValue());
			} else {
				newValMap.put(name, new IntervalDomainValue());
			}
		} else {
			mLogger.warn("The IBoogieVar type " + variable.getIType().getClass().toString() + " of variable " + name
			        + " is not implemented. Assuming top.");
			newValMap.put(name, new IntervalDomainValue());
		}

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IntervalDomainState removeVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		newValMap.remove(name);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		newBooleanValMap.remove(name);

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IntervalDomainState addVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);

		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			final String id = entry.getKey();
			final IBoogieVar var = entry.getValue();
			final IBoogieVar old = newVarMap.put(id, var);
			if (old != null) {
				throw new UnsupportedOperationException(
				        "Variable names must be disjoint. The variable " + id + " is already present.");
			}
			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					newBooleanValMap.put(id, new BooleanValue());
				} else {
					newValMap.put(id, new IntervalDomainValue());
				}

			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				newValMap.put(id, new IntervalDomainValue());
			} else {
				mLogger.warn("The IBoogieVar type " + var.getIType().getClass().toString() + " of variable " + id
				        + " is not implemented. Assuming top.");
				newValMap.put(id, new IntervalDomainValue());
			}
		}

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public IntervalDomainState removeVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
			newBooleanValMap.remove(entry.getKey());
		}

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public boolean containsVariable(String name) {
		final IBoogieVar var = mVariablesMap.get(name);
		return var != null;
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

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			if (entry.getValue().getValue() == Value.BOTTOM) {
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
	public IntervalDomainState setFixpoint(boolean value) {
		return new IntervalDomainState(mLogger, mVariablesMap, mValuesMap, mBooleanValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = [lb1 ; ub1]; var2 : type2 = [lb2 ; ub2]; ...", where lb is a lower
	 * bound and ub is an upper bound. lb can also be -\infty or \infty. Note that a value may also be "{}" if the
	 * corresponding interval is &bot;.
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {

			stringBuilder.append(entry.getKey()).append(" = ");

			final IntervalDomainValue val = mValuesMap.get(entry.getKey());

			if (val != null) {
				stringBuilder.append(mValuesMap.get(entry.getKey()).toString());
			} else {
				stringBuilder.append(mBooleanValuesMap.get(entry.getKey()).toString());
			}

			stringBuilder.append("; ");
		}
		return stringBuilder.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public boolean isEqualTo(IntervalDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IntervalDomainValue otherValue = other.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final BooleanValue otherValue = other.mBooleanValuesMap.get(entry.getKey());
			if (!mBooleanValuesMap.get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		return true;
	}

	public IntervalDomainState copy() {
		return new IntervalDomainState(mLogger, mVariablesMap, mValuesMap, mBooleanValuesMap, mIsFixpoint);
	}

	@Override
	public IntervalDomainState getResult() {
		return this;
	}

	@Override
	public int hashCode() {
		return mId;
	}

	/**
	 * Returns <code>true</code> if and only if {@link this} has the same variables as other.
	 * 
	 * @param other
	 *            The other state to check for same variables.
	 * @return <code>true</code> iff the variables are the same, <code>false</code> otherwise.
	 */
	protected boolean hasSameVariables(IntervalDomainState other) {
		if (other == null) {
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

	/**
	 * Intersects <code>this</code> with another {@link IntervalDomainState} by piecewise intersecting all occurring
	 * variable intervals.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new {@link IAbstractState} that corresponds to the intersection of
	 */
	protected IntervalDomainState intersect(IntervalDomainState other) {
		assert other != null;
		assert hasSameVariables(other);

		final IntervalDomainState returnState = copy();

		for (Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			returnState.setValue(entry.getKey(), entry.getValue().intersect(other.mValuesMap.get(entry.getKey())));
		}

		for (Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			returnState.setBooleanValue(entry.getKey(),
			        new BooleanValue(entry.getValue().intersect(other.mBooleanValuesMap.get(entry.getKey()))));
		}

		return returnState;
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}

		Term acc = script.term("true");
		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IBoogieVar boogievar = mVariablesMap.get(entry.getKey());
			final Term var = getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				mLogger.warn("Unfinished term transformation: Unsupported sort " + sort + " for variable " + var + ": "
				        + this);
				continue;
			}
			final Term newterm = entry.getValue().getTerm(script, sort, var);
			acc = Util.and(script, acc, newterm);
		}
		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final IBoogieVar boogievar = mVariablesMap.get(entry.getKey());
			final Term var = getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			final Term newterm = entry.getValue().getTerm(script, sort, var);
			acc = Util.and(script, acc, newterm);
		}
		return acc;
	}

	private Term getTermVar(IBoogieVar var) {
		assert var != null : "Cannot get TermVariable from null";
		if (var instanceof BoogieVar) {
			final TermVariable termvar = ((BoogieVar) var).getTermVariable();
			assert termvar != null : "There seems to be no termvar for this BoogieVar";
			return termvar;
		}
		return null;
	}

	/**
	 * @return A new {@link IntervalDomainState} containing the same set of variables but with values set to &bot;.
	 */
	protected IntervalDomainState bottomState() {
		IntervalDomainState ret = copy();
		for (final Entry<String, IntervalDomainValue> entry : ret.mValuesMap.entrySet()) {
			entry.setValue(new IntervalDomainValue(true));
		}

		return ret;
	}

	@Override
	public IBoogieVar getVariableType(String name) {
		assert name != null;
		final IBoogieVar var = mVariablesMap.get(name);
		assert var != null : "Unknown variable";
		return var;
	}
}
