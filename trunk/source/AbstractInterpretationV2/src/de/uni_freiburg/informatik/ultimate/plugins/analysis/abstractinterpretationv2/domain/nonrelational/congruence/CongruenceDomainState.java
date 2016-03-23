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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of an abstract state of the {@link CongruenceDomain}.
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CongruenceDomainState implements IAbstractState<CongruenceDomainState, CodeBlock, IBoogieVar> {

	private static int sId;
	private final int mId;

	private final Map<String, IBoogieVar> mVariablesMap;
	private final Map<String, CongruenceDomainValue> mValuesMap;
	private final Map<String, BooleanValue> mBooleanValuesMap;

	private final Logger mLogger;

	private boolean mIsFixpoint;

	protected enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}

	protected CongruenceDomainState() {
		this(null);
	}

	protected CongruenceDomainState(Logger logger) {
		mVariablesMap = new HashMap<String, IBoogieVar>();
		mValuesMap = new HashMap<String, CongruenceDomainValue>();
		mBooleanValuesMap = new HashMap<String, BooleanValue>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
		mLogger = logger;
	}

	protected CongruenceDomainState(Logger logger, Map<String, IBoogieVar> variablesMap,
			Map<String, CongruenceDomainValue> valuesMap, Map<String, BooleanValue> booleanValuesMap,
			boolean isFixpoint) {
		mVariablesMap = new HashMap<String, IBoogieVar>(variablesMap);
		mValuesMap = new HashMap<String, CongruenceDomainValue>(valuesMap);
		mBooleanValuesMap = new HashMap<String, BooleanValue>(booleanValuesMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
		mLogger = logger;
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mVariablesMap);
	}

	/**
	 * Returns the {@link CongruenceDomainValue} of the given variable. If the variable does not have a value, an
	 * {@link UnsupportedOperationException} is thrown.
	 * 
	 * @param variableName
	 *            The name of the variable to get the {@link CongruenceDomainValue} for.
	 * @return A new {@link CongruenceDomainValue} containing the {@link CongruenceDomainValue} of the given variable.
	 */
	protected CongruenceDomainValue getValue(String variableName) {
		if (!mValuesMap.containsKey(variableName)) {
			throw new UnsupportedOperationException("There is no value of variable " + variableName + ".");
		}

		return mValuesMap.get(variableName).copy();
	}

	/**
	 * Returns the {@link BooleanValue} of the given variable. If the variable is not a boolean variable, an
	 * {@link UnsupportedOperationException} is thrown.
	 * 
	 * @param booleanVariableName
	 *            The name of the boolean variable to get the {@link BooleanValue} for.
	 * @return A new {@link BooleanValue} containing the {@link BooleanValue} of the given variable.
	 */
	protected BooleanValue getBooleanValue(String booleanVariableName) {
		if (!mBooleanValuesMap.containsKey(booleanVariableName)) {
			throw new UnsupportedOperationException(
					"There is no boolean variable with name " + booleanVariableName + ".");
		}

		return new BooleanValue(mBooleanValuesMap.get(booleanVariableName));
	}

	protected CongruenceDomainState setValue(String name, CongruenceDomainValue value) {
		final CongruenceDomainState returnState = copy();
		setValueInternally(returnState, name, value);
		return returnState;
	}

	protected CongruenceDomainState setValues(String[] vars, CongruenceDomainValue[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(vars, values, new String[0], new BooleanValue.Value[0], new String[0],
				new CongruenceDomainValue[0]);
	}

	protected CongruenceDomainState setBooleanValue(String name, BooleanValue.Value value) {
		assert name != null;
		assert value != null;

		final CongruenceDomainState returnState = copy();
		setValueInternally(returnState, name, new BooleanValue(value));
		return returnState;
	}

	protected CongruenceDomainState setBooleanValue(String bool, boolean value) {
		return setBooleanValue(bool, new BooleanValue(value));
	}

	protected CongruenceDomainState setBooleanValue(String bool, BooleanValue value) {
		assert bool != null;
		assert value != null;

		return setBooleanValue(bool, value.getValue());
	}

	protected CongruenceDomainState setBooleanValues(String[] vars, BooleanValue.Value[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(new String[0], new CongruenceDomainValue[0], vars, values, new String[0],
				new CongruenceDomainValue[0]);
	}

	/**
	 * Sets the value of an array variable to a given value.
	 * 
	 * TODO: Implement proper handling of arrays.
	 * 
	 * @param array
	 *            The array name.
	 * @param value
	 *            The value to set the array variable to.
	 * @return A new {@link CongruenceDomainState} which is the copy of <code>this</code> but with updated value for the
	 *         given array variable.
	 */
	protected CongruenceDomainState setArrayValue(String array, CongruenceDomainValue value) {
		assert array != null;
		assert value != null;
		final CongruenceDomainState returnState = copy();
		setValueInternally(returnState, array, value);
		return returnState;
	}

	protected CongruenceDomainState setArrayValues(String[] arrays, CongruenceDomainValue[] values) {
		assert arrays != null;
		assert values != null;
		assert arrays.length == values.length;

		return setMixedValues(new String[0], new CongruenceDomainValue[0], new String[0], new BooleanValue.Value[0],
				arrays, values);
	}

	/**
	 * Sets multiple values of multiple variable types at the same time.
	 * 
	 * TODO: Arrays are currently handled as normal variables.
	 * 
	 * @param vars
	 *            A list of variable identifiers whose values are to be changed.
	 * @param values
	 *            A list of values which corresponds to the list of variable identifiers.
	 * @param booleanVars
	 *            A list of boolean variable identifiers whose values are to be changed.
	 * @param booleanValues
	 *            A list of values which corresponds to the list of boolean variable identifiers.
	 * @return A new {@link CongruenceDomainState} which is the copy of <code>this</code> but with the updated values.
	 */
	protected CongruenceDomainState setMixedValues(String[] vars, CongruenceDomainValue[] values, String[] booleanVars,
			BooleanValue.Value[] booleanValues, String[] arrays, CongruenceDomainValue[] arrayValues) {
		assert vars != null;
		assert values != null;
		assert booleanVars != null;
		assert booleanValues != null;
		assert vars.length == values.length;
		assert booleanVars.length == booleanValues.length;

		final CongruenceDomainState returnState = copy();
		for (int i = 0; i < vars.length; i++) {
			setValueInternally(returnState, vars[i], values[i]);
		}

		for (int i = 0; i < booleanVars.length; i++) {
			setValueInternally(returnState, booleanVars[i], new BooleanValue(booleanValues[i]));
		}

		for (int i = 0; i < arrays.length; i++) {
			setValueInternally(returnState, arrays[i], arrayValues[i]);
		}

		return returnState;
	}

	private static void setValueInternally(CongruenceDomainState state, String name, CongruenceDomainValue value) {
		assert state != null;
		assert name != null;
		assert value != null;
		assert state.mVariablesMap.get(name) != null : "Variable unknown";
		assert state.mValuesMap.get(name) != null : "Variable not in values map";
		state.mValuesMap.put(name, value);
	}

	private static void setValueInternally(CongruenceDomainState state, String name, BooleanValue value) {
		assert state != null;
		assert name != null;
		assert state.mVariablesMap.get(name) != null : "Variable unknown";
		assert state.mBooleanValuesMap.get(name) != null : "Boolean variable not in boolean values map";
		state.mBooleanValuesMap.put(name, value);
	}

	@Override
	public CongruenceDomainState addVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final CongruenceDomainState returnState = copy();
		addVariableInternally(returnState, name, variable);
		return returnState;
	}

	protected VariableType getVariableType(String var) {
		if (!containsVariable(var)) {
			throw new UnsupportedOperationException("The variable " + var + " does not exist in the current state.");
		}

		if (mBooleanValuesMap.containsKey(var)) {
			return VariableType.BOOLEAN;
		}

		if (mValuesMap.containsKey(var)) {
			return VariableType.VARIABLE;
		}

		// TODO: Implement proper handling of arrays.
		throw new UnsupportedOperationException(
				"The variable " + var + " exists but was not found in the variable sets.");
	}

	/**
	 * Adds the given variable with given name and type to the appropriate data structures of <code>this</code>.
	 * 
	 * @param name
	 *            The variable to add.
	 * @param variable
	 *            The type of the variable.
	 */
	private static void addVariableInternally(CongruenceDomainState state, String name, IBoogieVar variable) {
		assert state != null;
		assert name != null;
		assert variable != null;

		final IBoogieVar old = state.mVariablesMap.put(name, variable);

		if (old != null) {
			throw new UnsupportedOperationException(
					"Variable names must be disjoint. Variable " + name + " is already present.");
		}

		if (variable.getIType() instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) variable.getIType();

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				state.mBooleanValuesMap.put(name, new BooleanValue(true));
			} else {
				state.mValuesMap.put(name, new CongruenceDomainValue());
			}
		} else if (variable.getIType() instanceof ArrayType) {
			// TODO:
			// We treat Arrays as normal variables for the time being.
			state.mValuesMap.put(name, new CongruenceDomainValue());
		} else {
			state.mLogger.warn("The IBoogieVar type " + variable.getIType().getClass().toString() + " of variable "
					+ name + " is not implemented. Assuming top.");
			state.mValuesMap.put(name, new CongruenceDomainValue());
		}
	}

	@Override
	public CongruenceDomainState removeVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, CongruenceDomainValue> newValMap = new HashMap<String, CongruenceDomainValue>(mValuesMap);
		newValMap.remove(name);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		newBooleanValMap.remove(name);

		return new CongruenceDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public CongruenceDomainState addVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return this;
		}

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, CongruenceDomainValue> newValMap = new HashMap<String, CongruenceDomainValue>(mValuesMap);
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
					newValMap.put(id, new CongruenceDomainValue());
				}

			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				newValMap.put(id, new CongruenceDomainValue());
			} else {
				mLogger.warn("The IBoogieVar type " + var.getIType().getClass().toString() + " of variable " + id
						+ " is not implemented. Assuming top.");
				newValMap.put(id, new CongruenceDomainValue());
			}
		}

		return new CongruenceDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
	}

	@Override
	public CongruenceDomainState removeVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, CongruenceDomainValue> newValMap = new HashMap<String, CongruenceDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
			newBooleanValMap.remove(entry.getKey());
		}

		return new CongruenceDomainState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsFixpoint);
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
		for (final Entry<String, CongruenceDomainValue> entry : mValuesMap.entrySet()) {
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

	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	public CongruenceDomainState setFixpoint(boolean value) {
		return new CongruenceDomainState(mLogger, mVariablesMap, mValuesMap, mBooleanValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = [lb1 ; ub1]; var2 : type2 = [lb2 ; ub2]; ...", where lb is a lower
	 * bound and ub is an upper bound. lb can also be -\infty or \infty. Note that a value may also be "{}" if the
	 * corresponding Congruence is &bot;.
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {

			stringBuilder.append(entry.getKey()).append(" = ");

			final CongruenceDomainValue val = mValuesMap.get(entry.getKey());

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
	public boolean isEqualTo(CongruenceDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		for (final Entry<String, CongruenceDomainValue> entry : mValuesMap.entrySet()) {
			final CongruenceDomainValue otherValue = other.mValuesMap.get(entry.getKey());
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

	public CongruenceDomainState copy() {
		return new CongruenceDomainState(mLogger, mVariablesMap, mValuesMap, mBooleanValuesMap, mIsFixpoint);
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
	protected boolean hasSameVariables(CongruenceDomainState other) {
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
	 * Intersects <code>this</code> with another {@link CongruenceDomainState} by piecewise intersecting all occurring
	 * variable Congruences.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new {@link IAbstractState} that corresponds to the intersection of
	 */
	protected CongruenceDomainState intersect(CongruenceDomainState other) {
		assert other != null;
		assert hasSameVariables(other);

		final CongruenceDomainState returnState = copy();

		for (Entry<String, CongruenceDomainValue> entry : mValuesMap.entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					entry.getValue().intersect(other.mValuesMap.get(entry.getKey())));
		}

		for (Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			setValueInternally(returnState, entry.getKey(),
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
		for (final Entry<String, CongruenceDomainValue> entry : mValuesMap.entrySet()) {
			final IBoogieVar boogievar = mVariablesMap.get(entry.getKey());
			final Term var = getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
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
		} else if (var instanceof BoogieConst) {
			final ApplicationTerm termvar = ((BoogieConst) var).getDefaultConstant();
			assert termvar != null : "There seems to be no termvar for this BoogieConst";
			return termvar;
		}
		return null;
	}

	/**
	 * @return A new {@link CongruenceDomainState} containing the same set of variables but with values set to &bot;.
	 */
	protected CongruenceDomainState bottomState() {
		CongruenceDomainState ret = copy();
		for (final Entry<String, CongruenceDomainValue> entry : ret.mValuesMap.entrySet()) {
			entry.setValue(new CongruenceDomainValue(true));
		}

		for (final Entry<String, BooleanValue> entry : ret.mBooleanValuesMap.entrySet()) {
			entry.setValue(new BooleanValue(Value.BOTTOM));
		}

		return ret;
	}

	/**
	 * Sets all variables, booleans, or arrays to &top;, that are specified in the corresponding parameters.
	 * 
	 * @param vars
	 *            The names of the variables to set to &top;.
	 * @param bools
	 *            The names of the booleans to set to &top;.
	 * @param arrays
	 *            The names of the arrays to set to &top;.
	 * @return A new {@link CongruenceDomainState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given in the parameters are set to &top;.
	 */
	protected CongruenceDomainState setVarsToTop(List<String> vars, List<String> bools, List<String> arrays) {
		final CongruenceDomainState returnState = copy();

		for (final String var : vars) {
			setValueInternally(returnState, var, new CongruenceDomainValue());
		}
		for (final String bool : bools) {
			setValueInternally(returnState, bool, new BooleanValue());
		}
		for (final String array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, new CongruenceDomainValue());
		}

		return returnState;
	}

	/**
	 * Sets all given variables, booleans, or arrays to &bot;.
	 * 
	 * @param vars
	 *            The names of the variables to set to &bot;.
	 * @param bools
	 *            The names of the booleans to set to &bot;.
	 * @param arrays
	 *            The names of the arrays to set to &bot;.
	 * @return A new {@link CongruenceDomainState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given as parameters are set to &bot;.
	 */
	protected CongruenceDomainState setVarsToBottom(List<String> vars, List<String> bools, List<String> arrays) {
		final CongruenceDomainState returnState = copy();

		for (final String var : vars) {
			setValueInternally(returnState, var, new CongruenceDomainValue(true));
		}
		for (final String bool : bools) {
			setValueInternally(returnState, bool, new BooleanValue(Value.BOTTOM));
		}
		for (final String array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, new CongruenceDomainValue(true));
		}

		return returnState;
	}

	@Override
	public IBoogieVar getVariableDeclarationType(String name) {
		assert name != null;
		final IBoogieVar var = mVariablesMap.get(name);
		assert var != null : "Unknown variable";
		return var;
	}

	@Override
	public CongruenceDomainState patch(final CongruenceDomainState dominator) {
		assert dominator != null;

		CongruenceDomainState returnState = copy();

		for (final Entry<String, IBoogieVar> var : dominator.mVariablesMap.entrySet()) {
			if (!returnState.containsVariable(var.getKey())) {
				addVariableInternally(returnState, var.getKey(), var.getValue());
			}

			if (var.getValue().getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getValue().getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var.getKey(), dominator.mBooleanValuesMap.get(var.getKey()));
				} else if (var.getValue().getIType() instanceof ArrayType) {
					// TODO:
					// We treat Arrays as normal variables for the time being.
					setValueInternally(returnState, var.getKey(), dominator.mValuesMap.get(var.getKey()));
				} else {
					setValueInternally(returnState, var.getKey(), dominator.mValuesMap.get(var.getKey()));
				}
			}

		}

		return returnState;
	}

	/**
	 * Merges <code>this</code> with another {@link CongruenceDomainState}. All variables that occur in
	 * <code>this</code> must also occur in the other state.
	 * 
	 * @param other
	 *            The other state to merge with.
	 * @return A new {@link CongruenceDomainState} which is the result of the merger of <code>this</code> and
	 *         <code>other</code>.
	 */
	protected CongruenceDomainState merge(CongruenceDomainState other) {
		assert other != null;

		if (!hasSameVariables(other)) {
			throw new UnsupportedOperationException(
					"Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final CongruenceDomainState returnState = copy();

		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			final String var = entry.getKey();

			if (entry.getValue().getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) entry.getValue().getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var,
							mBooleanValuesMap.get(var).merge(other.mBooleanValuesMap.get(var)));
				} else {
					setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
				}
			} else if (entry.getValue().getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
			} else {
				setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
			}
		}
		return returnState;
	}

	@Override
	public SubsetResult isSubsetOf(final CongruenceDomainState other) {
		assert hasSameVariables(other);
		
		if (mValuesMap.isEmpty() && mBooleanValuesMap.isEmpty()) {
			return SubsetResult.EQUAL;
		}
		
		SubsetResult res = SubsetResult.NONE;
		
		for (final Entry<String, CongruenceDomainValue> entry : mValuesMap.entrySet()) {
			final CongruenceDomainValue thisValue = entry.getValue();
			final CongruenceDomainValue otherValue = other.mValuesMap.get(entry.getKey());
			if (thisValue.isEqualTo(otherValue)) {
				if (res == SubsetResult.NONE) {
					res = SubsetResult.EQUAL;
				} else if (res == SubsetResult.STRICT) {
					res = SubsetResult.NON_STRICT;
				}
			} else if (thisValue.isSubsetOf(otherValue)) {
				if (res == SubsetResult.NONE) {
					res = SubsetResult.STRICT;
				} else if (res == SubsetResult.EQUAL) {
					res = SubsetResult.NON_STRICT;
				}
			} else {
				return SubsetResult.NONE;
			}
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final BooleanValue thisValue = entry.getValue();
			final BooleanValue otherValue = other.mBooleanValuesMap.get(entry.getKey());
			if (thisValue.isEqualTo(otherValue)) {
				if (res == SubsetResult.NONE) {
					res = SubsetResult.EQUAL;
				} else if (res == SubsetResult.STRICT) {
					res = SubsetResult.NON_STRICT;
				}
			} else if (thisValue.isSubsetOf(otherValue)) {
				if (res == SubsetResult.NONE) {
					res = SubsetResult.STRICT;
				} else if (res == SubsetResult.EQUAL) {
					res = SubsetResult.NON_STRICT;
				}
			} else {
				return SubsetResult.NONE;
			}
		}

		return res;
	}
}
