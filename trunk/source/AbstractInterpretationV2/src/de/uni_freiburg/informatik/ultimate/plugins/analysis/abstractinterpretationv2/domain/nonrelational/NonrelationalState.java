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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.LoggingHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TVBool;

/**
 * Abstract implementation of an abstract state for non-relational domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class NonrelationalState<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		implements IAbstractState<STATE> {

	private static final String MSG_NULL = "NULL";
	private static final String MSG_BOT = "BOT";
	private static final String MSG_TOP = "TOP";

	public enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}

	private static int sId;
	private final int mId;

	private final Set<IProgramVarOrConst> mVariables;
	private final Map<IProgramVarOrConst, V> mValueMap;
	private final Map<IProgramVarOrConst, BooleanValue> mBooleanValuesMap;
	private TVBool mIsBottom;

	private final ILogger mLogger;

	/**
	 * Default constructor of an {@link NonrelationalState}.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param isBottom
	 *            If <code>true</code>, the created state corresponds to &bot;, &top; otherwise.
	 * @param variableType
	 *            The type of the variables stored by this state.
	 */
	protected NonrelationalState(final ILogger logger, final boolean isBottom) {
		this(logger, Collections.emptySet(), Collections.emptyMap(), Collections.emptyMap(), isBottom);
	}

	/**
	 * Creates a new instance of {@link NonrelationalState} with given logger, variables map, values map and boolean
	 * values map and defines whether the state is bottom or not.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param variables
	 *            The map with all variable identifiers and their types.
	 * @param valuesMap
	 *            The values of all variables.
	 * @param booleanValuesMap
	 *            The values of all boolean variables.
	 * @param isBottom
	 *            If <code>true</code> the created state corresponds to &bot;, &top; otherwise.
	 * @param variableType
	 *            The type of the variables stored by this state.
	 */
	protected NonrelationalState(final ILogger logger, final Set<IProgramVarOrConst> variables,
			final Map<IProgramVarOrConst, V> valuesMap, final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap,
			final boolean isBottom) {
		this(logger, variables, valuesMap, booleanValuesMap, isBottom ? TVBool.FIXED : TVBool.UNCHECKED);
	}

	protected NonrelationalState(final ILogger logger, final Set<IProgramVarOrConst> variables,
			final Map<IProgramVarOrConst, V> valuesMap, final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap,
			final TVBool isBottom) {
		mVariables = new HashSet<>(variables);
		mValueMap = new HashMap<>(valuesMap);
		mBooleanValuesMap = new HashMap<>(booleanValuesMap);
		sId++;
		mId = sId;
		mLogger = logger;
		mIsBottom = isBottom;
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}

	/**
	 * Returns the {@link INonrelationalValue} of the given variable. If the variable does not have a value, an
	 * {@link AssertionError} is thrown.
	 *
	 * @param variableName
	 *            The name of the variable to get the {@link INonrelationalValue} for.
	 * @return A new {@link INonrelationalValue} containing the {@link INonrelationalValue} of the given variable.
	 */
	public V getValue(final IProgramVarOrConst variableName) {
		final V val = getVar2ValueNonrelational().get(variableName);
		if (val == null) {
			throw new AssertionError("There is no value of variable " + variableName + ".");
		}

		return val;
	}

	/**
	 * Returns the {@link BooleanValue} of the given variable. If the variable is not a boolean variable, an
	 * {@link AssertionError} is thrown.
	 *
	 * @param variableName
	 *            The name of the boolean variable to get the {@link BooleanValue} for.
	 * @return A new {@link BooleanValue} containing the {@link BooleanValue} of the given variable.
	 */
	public BooleanValue getBooleanValue(final IProgramVarOrConst variableName) {
		final BooleanValue val = getVar2ValueBoolean().get(variableName);
		if (val == null) {
			throw new AssertionError("There is no value of variable " + variableName + ".");
		}

		return val;
	}

	/**
	 * Sets the value of a variable with given name to the given value.
	 *
	 * @param name
	 *            The name of the variable.
	 * @param value
	 *            The value to set.
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	public STATE setValue(final IProgramVarOrConst name, final V value) {
		if (getValue(name).isAbstractionEqual(value)) {
			return getThis();
		}
		final STATE returnState = createCopy();
		setValueInternally(returnState, name, value);
		return returnState;
	}

	/**
	 * Sets the values of multiple given variables at once.
	 *
	 * <p>
	 * <b>Note:</b> that the values and variables arrays must have the same size.
	 * </p>
	 *
	 * @param vars
	 *            The variables to set the values for.
	 * @param values
	 *            The array of values to set.
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> where the values of the given
	 *         variables have been set to the given values.
	 */
	public STATE setValues(final IProgramVarOrConst[] vars, final V[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(vars, values, new IProgramVarOrConst[0], new BooleanValue[0], new IProgramVarOrConst[0],
				getArray(0));
	}

	/**
	 * Sets the value of a boolean variable.
	 *
	 * @param name
	 *            The boolean variable to set the value for.
	 * @param value
	 *            The value to set.
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	public STATE setBooleanValue(final IProgramVarOrConst name, final BooleanValue value) {
		assert name != null;
		assert value != null;

		if (getBooleanValue(name).isEqualTo(value)) {
			return getThis();
		}

		final STATE returnState = createCopy();
		setValueInternally(returnState, name, value);
		return returnState;
	}

	/**
	 * Sets the values of multiple given boolean variables at once.
	 *
	 * <p>
	 * <b>Note:</b> that the values and variables arrays must have the same size.
	 * </p>
	 *
	 * @param vars
	 *            The variables to set the values for.
	 * @param values
	 *            The array of values to set.
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> where the values of the given
	 *         variables have been set to the given values.
	 */
	protected NonrelationalState<STATE, V> setBooleanValues(final IProgramVarOrConst[] vars,
			final BooleanValue[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(new IProgramVarOrConst[0], getArray(0), vars, values, new IProgramVarOrConst[0],
				getArray(0));
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
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> but with updated value for the
	 *         given array variable.
	 */
	protected NonrelationalState<STATE, V> setArrayValue(final IProgramVarOrConst array, final V value) {
		assert array != null;
		assert value != null;
		final NonrelationalState<STATE, V> returnState = createCopy();
		setValueInternally(returnState, array, value);
		return returnState;
	}

	protected NonrelationalState<STATE, V> setArrayValues(final IProgramVarOrConst[] arrays, final V[] values) {
		assert arrays != null;
		assert values != null;
		assert arrays.length == values.length;

		return setMixedValues(new IProgramVarOrConst[0], getArray(0), new IProgramVarOrConst[0], new BooleanValue[0],
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
	 * @return A new {@link NonrelationalState} which is the copy of <code>this</code> but with the updated values.
	 */
	public STATE setMixedValues(final IProgramVarOrConst[] vars, final V[] values,
			final IProgramVarOrConst[] booleanVars, final BooleanValue[] booleanValues,
			final IProgramVarOrConst[] arrays, final V[] arrayValues) {
		assert vars != null;
		assert values != null;
		assert booleanVars != null;
		assert booleanValues != null;
		assert vars.length == values.length;
		assert booleanVars.length == booleanValues.length;

		final STATE returnState = createCopy();
		for (int i = 0; i < vars.length; i++) {
			setValueInternally(returnState, vars[i], values[i]);
		}

		for (int i = 0; i < booleanVars.length; i++) {
			setValueInternally(returnState, booleanVars[i], booleanValues[i]);
		}

		for (int i = 0; i < arrays.length; i++) {
			setValueInternally(returnState, arrays[i], arrayValues[i]);
		}

		return returnState;
	}

	/**
	 * Internally sets the value of a variable of a given {@link NonrelationalState}.
	 *
	 * @param state
	 *            The state to set the variable value for.
	 * @param name
	 *            The name of the variable to change the value for.
	 * @param value
	 *            The value to set.
	 */
	private void setValueInternally(final NonrelationalState<STATE, V> state, final IProgramVarOrConst var,
			final V value) {
		assert state != null;
		assert var != null;
		assert value != null;
		state.resetBottomPreserving();
		state.mVariables.add(var);
		state.getVar2ValueNonrelational().put(var, value);
		if (value.isBottom()) {
			state.mIsBottom = TVBool.FIXED;
		}
	}

	/**
	 * Internally sets the value of a boolean variable of a given {@link NonrelationalState}.
	 *
	 * @param state
	 *            The state to set the variable value for.
	 * @param variable
	 *            The variable to change the value for.
	 * @param value
	 *            The value to set.
	 */
	private void setValueInternally(final NonrelationalState<STATE, V> state, final IProgramVarOrConst variable,
			final BooleanValue value) {
		assert state != null;
		assert variable != null;
		assert state.mVariables.contains(variable) : "Variable unknown";
		assert state.getVar2ValueBoolean().get(variable) != null : "Boolean variable not in boolean values map";
		state.resetBottomPreserving();
		state.getVar2ValueBoolean().put(variable, value);
		if (value.isBottom()) {
			state.mIsBottom = TVBool.FIXED;
		}
	}

	/**
	 * Returns the type of a given variable.
	 *
	 * @param var
	 *            The variable name to obtain the type for.
	 * @return The {@link VariableType} of the variable.
	 */
	public VariableType getVariableType(final IProgramVarOrConst var) {
		if (!containsVariable(var)) {
			throw new UnsupportedOperationException("The variable " + var + " does not exist in the current state.");
		}

		if (getVar2ValueBoolean().containsKey(var)) {
			return VariableType.BOOLEAN;
		}

		if (getVar2ValueNonrelational().containsKey(var)) {
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
	private void addVariableInternally(final NonrelationalState<STATE, V> state, final IProgramVarOrConst variable) {
		assert state != null;
		assert variable != null;

		if (!state.mVariables.add(variable)) {
			throw new UnsupportedOperationException(
					"Variable names must be disjoint. Variable " + variable + " is already present.");
		}
		state.resetBottomPreserving();
		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer =
				var -> state.getVar2ValueNonrelational().put(var, createTopValue());
		final Consumer<IProgramVarOrConst> boolConsumer = var -> state.getVar2ValueBoolean().put(var, BooleanValue.TOP);

		TypeUtils.consumeVariable(varConsumer, boolConsumer, null, variable);
	}

	@Override
	public STATE patch(final STATE dominator) {
		assert dominator != null;

		final STATE returnState = createCopy();

		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer =
				var -> setValueInternally(returnState, var, dominator.getVar2ValueNonrelational().get(var));
		final Consumer<IProgramVarOrConst> boolConsumer =
				var -> setValueInternally(returnState, var, dominator.getVar2ValueBoolean().get(var));

		for (final IProgramVarOrConst var : dominator.getVariables()) {
			if (!returnState.containsVariable(var)) {
				addVariableInternally(returnState, var);
			}

			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}

		return returnState;
	}

	@Override
	public SubsetResult isSubsetOf(final STATE other) {
		if (isBottom() && other.isBottom()) {
			return SubsetResult.EQUAL;
		}
		if (isBottom()) {
			return SubsetResult.STRICT;
		}
		if (other.isBottom()) {
			return SubsetResult.NONE;
		}
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}

		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V thisValue = entry.getValue();
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (otherValue == null) {
				// if the other state has no value for this value, it means top for the other state
				continue;
			}
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}

		}

		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final BooleanValue thisValue = entry.getValue();
			final BooleanValue otherValue = other.getVar2ValueBoolean().get(entry.getKey());
			if (otherValue == null) {
				// if the other state has no value for this value, it means top for the other state
				continue;
			}
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}
		return SubsetResult.STRICT;
	}

	@Override
	public STATE removeVariable(
			final de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst variable) {
		assert variable != null;

		final Set<IProgramVarOrConst> newVarMap = new HashSet<>(mVariables);
		newVarMap.remove(variable);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		newValMap.remove(variable);
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		newBooleanValMap.remove(variable);

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE addVariable(final IProgramVarOrConst variable) {
		assert variable != null;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Adding boogievar " + LoggingHelper.getHashCodeString(variable) + " " + variable);
		}
		final STATE returnState = createCopy();
		addVariableInternally(returnState, variable);
		return returnState;
	}

	@Override
	public STATE addVariables(final Collection<IProgramVarOrConst> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return getThis();
		}

		final Set<IProgramVarOrConst> newVars = new HashSet<>(mVariables);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());

		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer = var -> newValMap.put(var, createTopValue());
		final Consumer<IProgramVarOrConst> boolConsumer = var -> newBooleanValMap.put(var, BooleanValue.TOP);

		for (final IProgramVarOrConst var : variables) {
			if (!newVars.add(var)) {
				throw new UnsupportedOperationException(
						"Variable names must be disjoint. The variable " + var + " is already present.");
			}

			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}

		return createState(mLogger, newVars, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE removeVariables(final Collection<IProgramVarOrConst> variables) {
		assert variables != null;

		if (isEmpty()) {
			return getThis();
		}

		final Set<IProgramVarOrConst> newVarMap = new HashSet<>(mVariables);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		for (final IProgramVarOrConst entry : variables) {
			newVarMap.remove(entry);
			newValMap.remove(entry);
			newBooleanValMap.remove(entry);
		}

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		if (old2newVars == null || old2newVars.isEmpty()) {
			return getThis();
		}

		final STATE newState = createCopy();

		final NonrelationalState<STATE, V> newNRState = newState;

		boolean isChanged = false;
		for (final Entry<IProgramVarOrConst, IProgramVarOrConst> entry : old2newVars.entrySet()) {
			final IProgramVarOrConst oldVar = entry.getKey();
			final IProgramVarOrConst newVar = entry.getValue();

			if (newVar == null) {
				throw new IllegalArgumentException("Cannot rename " + oldVar + " to null");
			}

			if (oldVar == newVar) {
				continue;
			}

			if (!newNRState.mVariables.remove(oldVar)) {
				// this state does not contain this variable
				continue;
			}
			addVariableInternally(newNRState, newVar);
			isChanged = true;

			if (newNRState.mValueMap.containsKey(oldVar)) {
				assert !newNRState.mBooleanValuesMap.containsKey(oldVar);
				final V oldVarValue = newNRState.mValueMap.remove(oldVar);
				newNRState.mValueMap.put(newVar, oldVarValue);
			} else if (newNRState.mBooleanValuesMap.containsKey(oldVar)) {
				final BooleanValue oldVarValue = newNRState.mBooleanValuesMap.remove(oldVar);
				newNRState.mBooleanValuesMap.put(newVar, oldVarValue);
			} else {
				throw new AssertionError(
						"If var is known in this state is has to be either a number value or a boolean value");
			}
		}

		if (isChanged) {
			return newState;
		}
		return getThis();
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst name) {
		return mVariables.contains(name);
	}

	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		switch (mIsBottom) {
		case FALSE:
			return false;
		case TRUE:
		case FIXED:
			return true;
		case UNCHECKED:
			final boolean isBottom =
					getVar2ValueNonrelational().entrySet().stream().anyMatch(a -> a.getValue().isBottom())
							|| getVar2ValueBoolean().entrySet().stream().anyMatch(a -> a.getValue().isBottom());
			mIsBottom = isBottom ? TVBool.TRUE : TVBool.FALSE;
			return isBottom();
		default:
			throw new UnsupportedOperationException("Unknown LBool " + mIsBottom);
		}
	}

	protected TVBool getBottomFlag() {
		return mIsBottom;
	}

	/**
	 * Resets the bottom state flag to unchecked if the state was not bottom before.
	 */
	protected void resetBottomPreserving() {
		if (mIsBottom == TVBool.FIXED) {
			return;
		}
		mIsBottom = TVBool.UNCHECKED;
	}

	@Override
	public boolean isEqualTo(final STATE other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!getVar2ValueNonrelational().get(entry.getKey()).isAbstractionEqual(otherValue)) {
				return false;
			}
		}

		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final BooleanValue otherValue = other.getVar2ValueBoolean().get(entry.getKey());
			if (!getVar2ValueBoolean().get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		return true;
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
		final StringBuilder sbAll = new StringBuilder();
		final StringBuilder sbTop = new StringBuilder();
		final StringBuilder sbBot = new StringBuilder();
		if (isBottom()) {
			sbAll.append("BOTTOM ");
			if (getBottomFlag() == TVBool.FIXED) {
				sbAll.append("(FIXED) ");
			}
		}
		for (final IProgramVarOrConst entry : mVariables) {
			final String varName = entry.getGloballyUniqueId();
			final String val = getValueAsString(entry);
			if (MSG_TOP.equals(val)) {
				sbTop.append(varName).append(", ");
			} else if (MSG_BOT.equals(val)) {
				sbBot.append(varName).append(", ");
			} else {
				sbAll.append(varName).append(" = ").append(val).append("; ");
			}
		}

		if (sbTop.length() > 0) {
			sbAll.append("TOP: ").append(sbTop.delete(sbTop.length() - 2, sbTop.length())).append(" ");
		}
		if (sbBot.length() > 0) {
			sbAll.append("BOT: ").append(sbBot.delete(sbBot.length() - 2, sbBot.length())).append(" ");
		}

		return sbAll.toString();
	}

	private String getValueAsString(final IProgramVarOrConst entry) {
		final V val = getVar2ValueNonrelational().get(entry);
		if (val != null) {
			if (val.isTop()) {
				return MSG_TOP;
			} else if (val.isBottom()) {
				return MSG_BOT;
			}
			return val.toString();
		}
		final BooleanValue bolVal = getVar2ValueBoolean().get(entry);
		if (bolVal != null) {
			if (bolVal == BooleanValue.TOP) {
				return MSG_TOP;
			} else if (bolVal == BooleanValue.BOTTOM) {
				return MSG_BOT;
			}
			return bolVal.toString();
		}
		return MSG_NULL;
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
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof NonrelationalState)) {
			return false;
		}
		return ((NonrelationalState<?, ?>) obj).mId == mId;
	}

	protected abstract STATE getThis();

	protected abstract STATE createCopy();

	protected abstract STATE createState(ILogger logger, Set<IProgramVarOrConst> newVarMap,
			Map<IProgramVarOrConst, V> newValMap, Map<IProgramVarOrConst, BooleanValue> newBooleanValMap,
			boolean isBottom);

	protected abstract V createBottomValue();

	protected abstract V createTopValue();

	protected abstract V[] getArray(int size);

	/**
	 * Returns <code>true</code> if and only if {@link this} has the same variables as other.
	 *
	 * @param other
	 *            The other state to check for same variables.
	 * @return <code>true</code> iff the variables are the same, <code>false</code> otherwise.
	 */
	public boolean hasSameVariables(final NonrelationalState<STATE, V> other) {
		if (other == null) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		return mVariables.equals(other.mVariables);
	}

	/**
	 * Intersects <code>this</code> with another {@link NonrelationalState} by piecewise intersecting all occurring
	 * variable intervals.
	 *
	 * @param other
	 *            The other state to intersect with.
	 * @return A new {@link IAbstractState} that corresponds to the intersection of
	 */
	@Override
	public STATE intersect(final STATE other) {
		assert other != null;
		assert hasSameVariables(other);

		// Speed optimizations
		if (other == this) {
			return getThis();
		}

		if (isBottom()) {
			return getThis();
		}

		if (other.isBottom()) {
			return other;
		}
		// End of optimizations

		final STATE returnState = createCopy();

		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					entry.getValue().intersect(other.getVar2ValueNonrelational().get(entry.getKey())));
		}

		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					entry.getValue().intersect(other.getVar2ValueBoolean().get(entry.getKey())));
		}

		return returnState;
	}

	/**
	 * Merges <code>this</code> with another {@link NonrelationalState}. All variables that occur in <code>this</code>
	 * must also occur in the other state.
	 *
	 * @param other
	 *            The other state to merge with.
	 * @return A new {@link NonrelationalState} which is the result of the merger of <code>this</code> and
	 *         <code>other</code>.
	 */
	@Override
	public STATE union(final STATE other) {
		assert other != null;
		assert hasSameVariables(other);

		// Speed optimizations
		if (other == this) {
			return getThis();
		}

		if (isBottom()) {
			return other;
		}

		if (other.isBottom()) {
			return getThis();
		}

		// End of speed optimizations

		final STATE returnState = createCopy();

		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
		final Consumer<IProgramVarOrConst> boolConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueBoolean().get(var).merge(other.getVar2ValueBoolean().get(var)));

		for (final IProgramVarOrConst var : mVariables) {
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}
		return returnState;
	}

	@Override
	public STATE compact() {
		if (isBottom()) {
			return createState(mLogger, Collections.emptySet(), Collections.emptyMap(), Collections.emptyMap(), true);
		}

		final Set<IProgramVarOrConst> toRemove = new HashSet<>();
		final Iterator<Entry<IProgramVarOrConst, V>> valueIter = getVar2ValueNonrelational().entrySet().iterator();
		while (valueIter.hasNext()) {
			final Entry<IProgramVarOrConst, V> current = valueIter.next();
			if (!current.getValue().isTop()) {
				continue;
			}
			toRemove.add(current.getKey());
		}

		final Iterator<Entry<IProgramVarOrConst, BooleanValue>> boolIter = getVar2ValueBoolean().entrySet().iterator();
		while (boolIter.hasNext()) {
			final Entry<IProgramVarOrConst, BooleanValue> current = boolIter.next();
			if (current.getValue() != BooleanValue.TOP) {
				continue;
			}
			toRemove.add(current.getKey());
		}
		if (toRemove.isEmpty()) {
			return getThis();
		}

		final STATE returnState = createCopy();
		return returnState.removeVariables(toRemove);
	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}

		final List<Term> acc = new ArrayList<>(getVar2ValueNonrelational().size() + getVar2ValueBoolean().size());

		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final IProgramVarOrConst variable = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(variable);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				// TODO: Handle boolean variables (easy)
				// TODO: what about arrays (hard -- but perhaps not necessary, c.f. Matthias' integer programs)
				continue;
			}
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final IProgramVarOrConst variable = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(variable);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			acc.add(entry.getValue().getTerm(script, sort, var));
		}

		return SmtUtils.and(script, acc.toArray(new Term[acc.size()]));
	}

	/**
	 * @return A new {@link NonrelationalState} containing the same set of variables but with values set to &bot;.
	 */
	public STATE bottomState() {
		final STATE ret = createCopy();
		ret.resetBottomPreserving();
		for (final Entry<IProgramVarOrConst, V> entry : ret.getVar2ValueNonrelational().entrySet()) {
			entry.setValue(createBottomValue());
		}

		for (final Entry<IProgramVarOrConst, BooleanValue> entry : ret.getVar2ValueBoolean().entrySet()) {
			entry.setValue(BooleanValue.BOTTOM);
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
	 * @return A new {@link NonrelationalState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given in the parameters are set to &top;.
	 */
	public STATE setVarsToTop(final List<IProgramVarOrConst> vars, final List<IProgramVarOrConst> bools,
			final List<IProgramVarOrConst> arrays) {
		final STATE returnState = createCopy();

		for (final IProgramVarOrConst var : vars) {
			setValueInternally(returnState, var, createTopValue());
		}
		for (final IProgramVarOrConst bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.TOP);
		}
		for (final IProgramVarOrConst array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, createTopValue());
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
	 * @return A new {@link NonrelationalState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given as parameters are set to &bot;.
	 */
	protected STATE setVarsToBottom(final List<IProgramVarOrConst> vars, final List<IProgramVarOrConst> bools,
			final List<IProgramVarOrConst> arrays) {
		final STATE returnState = createCopy();

		for (final IProgramVarOrConst var : vars) {
			setValueInternally(returnState, var, createBottomValue());
		}
		for (final IProgramVarOrConst bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.BOTTOM);
		}
		for (final IProgramVarOrConst array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, createBottomValue());
		}

		return returnState;
	}

	protected Map<IProgramVarOrConst, BooleanValue> getVar2ValueBoolean() {
		return mBooleanValuesMap;
	}

	protected Map<IProgramVarOrConst, V> getVar2ValueNonrelational() {
		return mValueMap;
	}

	protected ILogger getLogger() {
		return mLogger;
	}
}
