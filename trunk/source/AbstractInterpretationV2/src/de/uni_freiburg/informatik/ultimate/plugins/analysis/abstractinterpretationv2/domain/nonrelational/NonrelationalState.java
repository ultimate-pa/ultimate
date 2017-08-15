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
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.LoggingHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TVBool;

/**
 * Abstract implementation of an abstract state for non-relational domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class NonrelationalState<STATE extends NonrelationalState<STATE, V, VARDECL>, V extends INonrelationalValue<V>, VARDECL>
		implements IAbstractState<STATE, VARDECL> {

	private static final String MSG_NULL = "NULL";
	private static final String MSG_BOT = "BOT";
	private static final String MSG_TOP = "TOP";

	public enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}

	private static int sId;
	private final int mId;

	private final Set<VARDECL> mVariables;
	private final Map<VARDECL, V> mValueMap;
	private final Map<VARDECL, BooleanValue> mBooleanValuesMap;
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
	protected NonrelationalState(final ILogger logger, final Set<VARDECL> variables, final Map<VARDECL, V> valuesMap,
			final Map<VARDECL, BooleanValue> booleanValuesMap, final boolean isBottom) {
		this(logger, variables, valuesMap, booleanValuesMap, isBottom ? TVBool.FIXED : TVBool.UNCHECKED);
	}

	protected NonrelationalState(final ILogger logger, final Set<VARDECL> variables, final Map<VARDECL, V> valuesMap,
			final Map<VARDECL, BooleanValue> booleanValuesMap, final TVBool isBottom) {
		mVariables = new HashSet<>(variables);
		mValueMap = new HashMap<>(valuesMap);
		mBooleanValuesMap = new HashMap<>(booleanValuesMap);
		sId++;
		mId = sId;
		mLogger = logger;
		mIsBottom = isBottom;
	}

	@Override
	public Set<VARDECL> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}

	/**
	 * Returns the {@link IntervalDomainValue} of the given variable. If the variable does not have a value, an
	 * {@link UnsupportedOperationException} is thrown.
	 *
	 * @param variableName
	 *            The name of the variable to get the {@link IntervalDomainValue} for.
	 * @return A new {@link IntervalDomainValue} containing the {@link IntervalDomainValue} of the given variable.
	 */
	public V getValue(final VARDECL variableName) {
		final V val = getVar2ValueNonrelational().get(variableName);
		if (val == null) {
			throw new AssertionError("There is no value of variable " + variableName + ".");
		}

		return val;
	}

	/**
	 * Returns the {@link BooleanValue} of the given variable. If the variable is not a boolean variable, an
	 * {@link UnsupportedOperationException} is thrown.
	 *
	 * @param variableName
	 *            The name of the boolean variable to get the {@link BooleanValue} for.
	 * @return A new {@link BooleanValue} containing the {@link BooleanValue} of the given variable.
	 */
	public BooleanValue getBooleanValue(final VARDECL variableName) {
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
	public STATE setValue(final VARDECL name, final V value) {
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
	public STATE setValues(final VARDECL[] vars, final V[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(vars, values, getVariableTypeArray(0), new BooleanValue[0], getVariableTypeArray(0),
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
	public STATE setBooleanValue(final VARDECL name, final BooleanValue value) {
		assert name != null;
		assert value != null;

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
	protected NonrelationalState<STATE, V, VARDECL> setBooleanValues(final VARDECL[] vars,
			final BooleanValue[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(getVariableTypeArray(0), getArray(0), vars, values, getVariableTypeArray(0), getArray(0));
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
	protected NonrelationalState<STATE, V, VARDECL> setArrayValue(final VARDECL array, final V value) {
		assert array != null;
		assert value != null;
		final NonrelationalState<STATE, V, VARDECL> returnState = createCopy();
		setValueInternally(returnState, array, value);
		return returnState;
	}

	protected NonrelationalState<STATE, V, VARDECL> setArrayValues(final VARDECL[] arrays, final V[] values) {
		assert arrays != null;
		assert values != null;
		assert arrays.length == values.length;

		return setMixedValues(getVariableTypeArray(0), getArray(0), getVariableTypeArray(0), new BooleanValue[0],
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
	public STATE setMixedValues(final VARDECL[] vars, final V[] values, final VARDECL[] booleanVars,
			final BooleanValue[] booleanValues, final VARDECL[] arrays, final V[] arrayValues) {
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
	private void setValueInternally(final NonrelationalState<STATE, V, VARDECL> state, final VARDECL var,
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
	private void setValueInternally(final NonrelationalState<STATE, V, VARDECL> state, final VARDECL variable,
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
	public VariableType getVariableType(final VARDECL var) {
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
	private void addVariableInternally(final NonrelationalState<STATE, V, VARDECL> state, final VARDECL variable) {
		assert state != null;
		assert variable != null;

		if (!state.mVariables.add(variable)) {
			throw new UnsupportedOperationException(
					"Variable names must be disjoint. Variable " + variable + " is already present.");
		}
		state.resetBottomPreserving();
		// TODO: Add array support.
		final Consumer<VARDECL> varConsumer = var -> state.getVar2ValueNonrelational().put(var, createTopValue());
		final Consumer<VARDECL> boolConsumer = var -> state.getVar2ValueBoolean().put(var, BooleanValue.TOP);

		TypeUtils.consumeVariable(varConsumer, boolConsumer, null, variable);
	}

	@Override
	public STATE patch(final STATE dominator) {
		assert dominator != null;

		final STATE returnState = createCopy();

		// TODO: Add array support.
		final Consumer<VARDECL> varConsumer =
				var -> setValueInternally(returnState, var, dominator.getVar2ValueNonrelational().get(var));
		final Consumer<VARDECL> boolConsumer =
				var -> setValueInternally(returnState, var, dominator.getVar2ValueBoolean().get(var));

		for (final VARDECL var : dominator.getVariables()) {
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

		for (final Entry<VARDECL, V> entry : getVar2ValueNonrelational().entrySet()) {
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

		for (final Entry<VARDECL, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
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
		return SubsetResult.NON_STRICT;
	}

	@Override
	public STATE removeVariable(final VARDECL variable) {
		assert variable != null;

		final Set<VARDECL> newVarMap = new HashSet<>(mVariables);
		newVarMap.remove(variable);
		final Map<VARDECL, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		newValMap.remove(variable);
		final Map<VARDECL, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		newBooleanValMap.remove(variable);

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE addVariable(final VARDECL variable) {
		assert variable != null;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Adding boogievar " + LoggingHelper.getHashCodeString(variable) + " " + variable);
		}
		final STATE returnState = createCopy();
		addVariableInternally(returnState, variable);
		return returnState;
	}

	@Override
	public STATE addVariables(final Collection<VARDECL> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return getThis();
		}

		final Set<VARDECL> newVars = new HashSet<>(mVariables);
		final Map<VARDECL, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<VARDECL, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());

		// TODO: Add array support.
		final Consumer<VARDECL> varConsumer = var -> newValMap.put(var, createTopValue());
		final Consumer<VARDECL> boolConsumer = var -> newBooleanValMap.put(var, BooleanValue.TOP);

		for (final VARDECL var : variables) {
			if (!newVars.add(var)) {
				throw new UnsupportedOperationException(
						"Variable names must be disjoint. The variable " + var + " is already present.");
			}

			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}

		return createState(mLogger, newVars, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE removeVariables(final Collection<VARDECL> variables) {
		assert variables != null;

		if (isEmpty()) {
			return getThis();
		}

		final Set<VARDECL> newVarMap = new HashSet<>(mVariables);
		final Map<VARDECL, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<VARDECL, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		for (final VARDECL entry : variables) {
			newVarMap.remove(entry);
			newValMap.remove(entry);
			newBooleanValMap.remove(entry);
		}

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap, mIsBottom == TVBool.FIXED);
	}

	@Override
	public STATE renameVariables(final Map<VARDECL, VARDECL> old2newVars) {
		if (old2newVars == null || old2newVars.isEmpty()) {
			return getThis();
		}

		final STATE newState = createCopy();

		final NonrelationalState<STATE, V, VARDECL> newNRState = newState;

		boolean isChanged = false;
		for (final Entry<VARDECL, VARDECL> entry : old2newVars.entrySet()) {
			final VARDECL oldVar = entry.getKey();
			final VARDECL newVar = entry.getValue();

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
			newNRState.addVariable(newVar);
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
	public boolean containsVariable(final VARDECL name) {
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

		for (final Entry<VARDECL, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!getVar2ValueNonrelational().get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		for (final Entry<VARDECL, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
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
		for (final VARDECL entry : mVariables) {
			final String varName;
			if (entry instanceof IBoogieVar) {
				varName = ((IBoogieVar) entry).getGloballyUniqueId();
			} else if (entry instanceof IProgramVarOrConst) {
				varName = ((IProgramVarOrConst) entry).getGloballyUniqueId();
			} else {
				throw new UnsupportedOperationException(
						"Variable type not implemented: " + entry.getClass().getSimpleName());
			}

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

	private String getValueAsString(final VARDECL entry) {
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
		return obj == this;
	}

	protected abstract STATE getThis();

	protected abstract STATE createCopy();

	protected abstract STATE createState(ILogger logger, Set<VARDECL> newVarMap, Map<VARDECL, V> newValMap,
			Map<VARDECL, BooleanValue> newBooleanValMap, boolean isBottom);

	protected abstract V createBottomValue();

	protected abstract V createTopValue();

	protected abstract V[] getArray(int size);

	@SuppressWarnings("unchecked")
	public VARDECL[] getVariableTypeArray(final int size) {
		return (VARDECL[]) new Object[size];
	}

	/**
	 * Returns <code>true</code> if and only if {@link this} has the same variables as other.
	 *
	 * @param other
	 *            The other state to check for same variables.
	 * @return <code>true</code> iff the variables are the same, <code>false</code> otherwise.
	 */
	public boolean hasSameVariables(final NonrelationalState<STATE, V, VARDECL> other) {
		if (other == null) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		if (other.mVariables.size() != mVariables.size()) {
			return false;
		}

		for (final VARDECL entry : mVariables) {
			if (!other.mVariables.contains(entry)) {
				return false;
			}
		}

		return true;
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

		final STATE returnState = createCopy();

		for (final Entry<VARDECL, V> entry : getVar2ValueNonrelational().entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					entry.getValue().intersect(other.getVar2ValueNonrelational().get(entry.getKey())));
		}

		for (final Entry<VARDECL, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
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

		if (!hasSameVariables(other)) {
			throw new UnsupportedOperationException(
					"Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final STATE returnState = createCopy();

		// TODO: Add array support.
		final Consumer<VARDECL> varConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
		final Consumer<VARDECL> boolConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueBoolean().get(var).merge(other.getVar2ValueBoolean().get(var)));

		for (final VARDECL var : mVariables) {
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}
		return returnState;
	}

	@Override
	public STATE compact() {
		if (isBottom()) {
			return createState(mLogger, Collections.emptySet(), Collections.emptyMap(), Collections.emptyMap(), true);
		}

		final Set<VARDECL> toRemove = new HashSet<>();
		final Iterator<Entry<VARDECL, V>> valueIter = getVar2ValueNonrelational().entrySet().iterator();
		while (valueIter.hasNext()) {
			final Entry<VARDECL, V> current = valueIter.next();
			if (!current.getValue().isTop()) {
				continue;
			}
			toRemove.add(current.getKey());
		}

		final Iterator<Entry<VARDECL, BooleanValue>> boolIter = getVar2ValueBoolean().entrySet().iterator();
		while (boolIter.hasNext()) {
			final Entry<VARDECL, BooleanValue> current = boolIter.next();
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

		for (final Entry<VARDECL, V> entry : getVar2ValueNonrelational().entrySet()) {
			final VARDECL variable = entry.getKey();
			final Term var;
			if (variable instanceof IBoogieVar) {
				var = NonrelationalTermUtils.getTermVar((IBoogieVar) variable);
			} else if (variable instanceof IProgramVarOrConst) {
				var = NonrelationalTermUtils.getTermVar((IProgramVarOrConst) variable);
			} else {
				throw new UnsupportedOperationException(
						"Variable type " + variable.getClass().getSimpleName() + " not implemented.");
			}

			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				// TODO: Handle boolean variables (easy)
				// TODO: what about arrays (hard -- but perhaps not necessary, c.f. Matthias' integer programs)
				continue;
			}
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		for (final Entry<VARDECL, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final VARDECL variable = entry.getKey();
			final Term var;
			if (variable instanceof IBoogieVar) {
				var = NonrelationalTermUtils.getTermVar((IBoogieVar) variable);
			} else if (variable instanceof IProgramVarOrConst) {
				var = NonrelationalTermUtils.getTermVar((IProgramVarOrConst) variable);
			} else {
				throw new UnsupportedOperationException(
						"Variable type " + variable.getClass().getSimpleName() + " not implemented.");
			}

			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			acc.add(entry.getValue().getTerm(script, sort, var));
		}

		return Util.and(script, acc.toArray(new Term[acc.size()]));
	}

	/**
	 * @return A new {@link NonrelationalState} containing the same set of variables but with values set to &bot;.
	 */
	public STATE bottomState() {
		final STATE ret = createCopy();
		ret.resetBottomPreserving();
		for (final Entry<VARDECL, V> entry : ret.getVar2ValueNonrelational().entrySet()) {
			entry.setValue(createBottomValue());
		}

		for (final Entry<VARDECL, BooleanValue> entry : ret.getVar2ValueBoolean().entrySet()) {
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
	public STATE setVarsToTop(final List<VARDECL> vars, final List<VARDECL> bools, final List<VARDECL> arrays) {
		final STATE returnState = createCopy();

		for (final VARDECL var : vars) {
			setValueInternally(returnState, var, createTopValue());
		}
		for (final VARDECL bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.TOP);
		}
		for (final VARDECL array : arrays) {
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
	protected STATE setVarsToBottom(final List<VARDECL> vars, final List<VARDECL> bools, final List<VARDECL> arrays) {
		final STATE returnState = createCopy();

		for (final VARDECL var : vars) {
			setValueInternally(returnState, var, createBottomValue());
		}
		for (final VARDECL bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.BOTTOM);
		}
		for (final VARDECL array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, createBottomValue());
		}

		return returnState;
	}

	protected Map<VARDECL, BooleanValue> getVar2ValueBoolean() {
		return mBooleanValuesMap;
	}

	protected Map<VARDECL, V> getVar2ValueNonrelational() {
		return mValueMap;
	}

	protected ILogger getLogger() {
		return mLogger;
	}
}
