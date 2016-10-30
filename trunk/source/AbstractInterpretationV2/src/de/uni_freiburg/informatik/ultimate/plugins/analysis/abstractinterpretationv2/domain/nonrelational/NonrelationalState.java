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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.LoggingHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Abstract implementation of an abstract state for non-relational domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class NonrelationalState<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
        implements INonrelationalAbstractState<STATE, CodeBlock> {

	protected enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}

	private static int sId;
	private final int mId;

	private final Set<IBoogieVar> mVariables;
	private final Map<IBoogieVar, V> mValueMap;
	private final Map<IBoogieVar, BooleanValue> mBooleanValuesMap;

	private final ILogger mLogger;

	/**
	 * Default constructor of an {@link NonrelationalState}.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 */
	protected NonrelationalState(final ILogger logger) {
		this(logger, new HashSet<>(), new HashMap<>(), new HashMap<>());
	}

	/**
	 * Creates a new instance of {@link NonrelationalState} with given logger, variables map, values map and boolean
	 * values map.
	 *
	 * @param logger
	 *            The current logger object in the current context.
	 * @param variables
	 *            The map with all variable identifiers and their types.
	 * @param valuesMap
	 *            The values of all variables.
	 * @param booleanValuesMap
	 *            The values of all boolean variables.
	 */
	protected NonrelationalState(final ILogger logger, final Set<IBoogieVar> variables,
	        final Map<IBoogieVar, V> valuesMap, final Map<IBoogieVar, BooleanValue> booleanValuesMap) {
		mVariables = new HashSet<>(variables);
		mValueMap = new HashMap<>(valuesMap);
		mBooleanValuesMap = new HashMap<>(booleanValuesMap);
		sId++;
		mId = sId;
		mLogger = logger;
	}

	@Override
	public Set<IBoogieVar> getVariables() {
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
	public V getValue(final IBoogieVar variableName) {
		if (!getVar2ValueNonrelational().containsKey(variableName)) {
			throw new UnsupportedOperationException("There is no value of variable " + variableName + ".");
		}

		return getVar2ValueNonrelational().get(variableName).copy();
	}

	/**
	 * Returns the {@link BooleanValue} of the given variable. If the variable is not a boolean variable, an
	 * {@link UnsupportedOperationException} is thrown.
	 *
	 * @param booleanVariableName
	 *            The name of the boolean variable to get the {@link BooleanValue} for.
	 * @return A new {@link BooleanValue} containing the {@link BooleanValue} of the given variable.
	 */
	public BooleanValue getBooleanValue(final IBoogieVar booleanVariableName) {
		if (!getVar2ValueBoolean().containsKey(booleanVariableName)) {
			throw new UnsupportedOperationException(
			        "There is no boolean variable with name " + booleanVariableName + ".");
		}
		return getVar2ValueBoolean().get(booleanVariableName);
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
	public STATE setValue(final IBoogieVar name, final V value) {
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
	public STATE setValues(final IBoogieVar[] vars, final V[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(vars, values, new IBoogieVar[0], new BooleanValue[0], new IBoogieVar[0], getArray(0));
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
	public STATE setBooleanValue(final IBoogieVar name, final BooleanValue value) {
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
	protected NonrelationalState<STATE, V> setBooleanValues(final IBoogieVar[] vars, final BooleanValue[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(new IBoogieVar[0], getArray(0), vars, values, new IBoogieVar[0], getArray(0));
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
	protected NonrelationalState<STATE, V> setArrayValue(final IBoogieVar array, final V value) {
		assert array != null;
		assert value != null;
		final NonrelationalState<STATE, V> returnState = createCopy();
		setValueInternally(returnState, array, value);
		return returnState;
	}

	protected NonrelationalState<STATE, V> setArrayValues(final IBoogieVar[] arrays, final V[] values) {
		assert arrays != null;
		assert values != null;
		assert arrays.length == values.length;

		return setMixedValues(new IBoogieVar[0], getArray(0), new IBoogieVar[0], new BooleanValue[0], arrays, values);
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
	public STATE setMixedValues(final IBoogieVar[] vars, final V[] values, final IBoogieVar[] booleanVars,
	        final BooleanValue[] booleanValues, final IBoogieVar[] arrays, final V[] arrayValues) {
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
	private void setValueInternally(final NonrelationalState<STATE, V> state, final IBoogieVar var, final V value) {
		assert state != null;
		assert var != null;
		assert value != null;
		assert state.mVariables.contains(var) : "Variable " + var + " unknown";
		assert state.getVar2ValueNonrelational().containsKey(var) : "Variable not in values map";
		state.getVar2ValueNonrelational().put(var, value);
	}

	/**
	 * Internally sets the value of a boolean variable of a given {@link NonrelationalState}.
	 *
	 * @param state
	 *            The state to set the variable value for.
	 * @param name
	 *            The name of the variable to change the value for.
	 * @param value
	 *            The value to set.
	 */
	private void setValueInternally(final NonrelationalState<STATE, V> state, final IBoogieVar name,
	        final BooleanValue value) {
		assert state != null;
		assert name != null;
		assert state.mVariables.contains(name) : "Variable unknown";
		assert state.getVar2ValueBoolean().get(name) != null : "Boolean variable not in boolean values map";
		state.getVar2ValueBoolean().put(name, value);
	}

	/**
	 * Returns the type of a given variable.
	 *
	 * @param var
	 *            The variable name to obtain the type for.
	 * @return The {@link VariableType} of the variable.
	 */
	protected VariableType getVariableType(final IBoogieVar var) {
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
	private void addVariableInternally(final NonrelationalState<STATE, V> state, final IBoogieVar variable) {
		assert state != null;
		assert variable != null;

		if (!state.mVariables.add(variable)) {
			throw new UnsupportedOperationException(
			        "Variable names must be disjoint. Variable " + variable + " is already present.");
		}

		if (variable.getIType() instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) variable.getIType();

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				state.getVar2ValueBoolean().put(variable, BooleanValue.TRUE);
			} else {
				state.getVar2ValueNonrelational().put(variable, createTopValue());
			}
		} else if (variable.getIType() instanceof ArrayType) {
			// TODO:
			// We treat Arrays as normal variables for the time being.
			state.getVar2ValueNonrelational().put(variable, createTopValue());
		} else {
			state.mLogger.warn("The IBoogieVar type " + variable.getIType().getClass().toString() + " of variable "
			        + variable + " is not implemented. Assuming top.");
			state.getVar2ValueNonrelational().put(variable, createTopValue());
		}
	}

	@Override
	public STATE patch(final STATE dominator) {
		assert dominator != null;

		final STATE returnState = createCopy();

		for (final IBoogieVar var : dominator.getVariables()) {
			if (!returnState.containsVariable(var)) {
				addVariableInternally(returnState, var);
			}

			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var, dominator.getVar2ValueBoolean().get(var));
				} else if (var.getIType() instanceof ArrayType) {
					// TODO:
					// We treat Arrays as normal variables for the time being.
					setValueInternally(returnState, var, dominator.getVar2ValueNonrelational().get(var));
				} else {
					setValueInternally(returnState, var, dominator.getVar2ValueNonrelational().get(var));
				}
			}

		}

		return returnState;
	}

	@Override
	public SubsetResult isSubsetOf(final STATE other) {
		assert hasSameVariables(other);

		if (isBottom() && other.isBottom()) {
			return SubsetResult.EQUAL;
		}
		if (isBottom()) {
			return SubsetResult.STRICT;
		}
		if (other.isBottom()) {
			return SubsetResult.NONE;
		}

		for (final Entry<IBoogieVar, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V thisValue = entry.getValue();
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}

		for (final Entry<IBoogieVar, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final BooleanValue thisValue = entry.getValue();
			final BooleanValue otherValue = other.getVar2ValueBoolean().get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}
		return SubsetResult.NON_STRICT;
	}

	@Override
	public STATE removeVariable(final IBoogieVar variable) {
		assert variable != null;

		final Set<IBoogieVar> newVarMap = new HashSet<>(mVariables);
		newVarMap.remove(variable);
		final Map<IBoogieVar, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		newValMap.remove(variable);
		final Map<IBoogieVar, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		newBooleanValMap.remove(variable);

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	public STATE addVariable(final IBoogieVar variable) {
		assert variable != null;
		mLogger.debug("Adding boogievar " + LoggingHelper.getHashCodeString(variable) + " " + variable);
		final STATE returnState = createCopy();
		addVariableInternally(returnState, variable);
		return returnState;
	}

	@SuppressWarnings("unchecked")
	@Override
	public STATE addVariables(final Collection<IBoogieVar> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return (STATE) this;
		}

		final Set<IBoogieVar> newVars = new HashSet<>(mVariables);
		final Map<IBoogieVar, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IBoogieVar, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());

		for (final IBoogieVar var : variables) {
			if (!newVars.add(var)) {
				throw new UnsupportedOperationException(
				        "Variable names must be disjoint. The variable " + var + " is already present.");
			}
			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					newBooleanValMap.put(var, BooleanValue.TOP);
				} else {
					newValMap.put(var, createTopValue());
				}

			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				newValMap.put(var, createTopValue());
			} else {
				mLogger.warn("The IBoogieVar type " + var.getIType().getClass().toString() + " of variable " + var
				        + " is not implemented. Assuming top.");
				newValMap.put(var, createTopValue());
			}
		}

		return createState(mLogger, newVars, newValMap, newBooleanValMap);
	}

	@Override
	public STATE removeVariables(final Collection<IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Set<IBoogieVar> newVarMap = new HashSet<>(mVariables);
		final Map<IBoogieVar, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IBoogieVar, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		for (final IBoogieVar entry : variables) {
			newVarMap.remove(entry);
			newValMap.remove(entry);
			newBooleanValMap.remove(entry);
		}

		return createState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	public boolean containsVariable(final IBoogieVar name) {
		return mVariables.contains(name);
	}

	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		for (final Entry<IBoogieVar, V> entry : getVar2ValueNonrelational().entrySet()) {
			if (entry.getValue().isBottom()) {
				return true;
			}
		}

		for (final Entry<IBoogieVar, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			if (entry.getValue() == BooleanValue.BOTTOM) {
				return true;
			}
		}

		return false;
	}

	@Override
	public boolean isEqualTo(final STATE other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		for (final Entry<IBoogieVar, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!getVar2ValueNonrelational().get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		for (final Entry<IBoogieVar, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
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
		final StringBuilder stringBuilder = new StringBuilder();
		for (final IBoogieVar entry : mVariables) {

			stringBuilder.append(entry.getGloballyUniqueId()).append(" = ");

			final V val = getVar2ValueNonrelational().get(entry);

			if (val != null) {
				stringBuilder.append(getVar2ValueNonrelational().get(entry).toString());
			} else {
				stringBuilder.append(getVar2ValueBoolean().get(entry).toString());
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

	protected abstract STATE createCopy();

	protected abstract STATE createState(ILogger logger, Set<IBoogieVar> newVarMap, Map<IBoogieVar, V> newValMap,
	        Map<IBoogieVar, BooleanValue> newBooleanValMap);

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

		if (other.mVariables.size() != mVariables.size()) {
			return false;
		}

		for (final IBoogieVar entry : mVariables) {
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

		for (final Entry<IBoogieVar, V> entry : getVar2ValueNonrelational().entrySet()) {
			setValueInternally(returnState, entry.getKey(),
			        entry.getValue().intersect(other.getVar2ValueNonrelational().get(entry.getKey())));
		}

		for (final Entry<IBoogieVar, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			setValueInternally(returnState, entry.getKey(),
			        entry.getValue().intersect(other.getVar2ValueBoolean().get(entry.getKey())));
		}

		return returnState;
	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}

		final List<Term> acc = new ArrayList<>(getVar2ValueNonrelational().size() + getVar2ValueBoolean().size());

		for (final Entry<IBoogieVar, V> entry : getVar2ValueNonrelational().entrySet()) {
			final IBoogieVar boogievar = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				// TODO: Handle boolean variables (easy)
				// TODO: what about arrays (hard -- but perhaps not necessary, c.f. Matthias' integer programs)
				continue;
			}
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		for (final Entry<IBoogieVar, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final IBoogieVar boogievar = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(boogievar);
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
		for (final Entry<IBoogieVar, V> entry : ret.getVar2ValueNonrelational().entrySet()) {
			entry.setValue(createBottomValue());
		}

		for (final Entry<IBoogieVar, BooleanValue> entry : ret.getVar2ValueBoolean().entrySet()) {
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
	public STATE setVarsToTop(final List<IBoogieVar> vars, final List<IBoogieVar> bools,
	        final List<IBoogieVar> arrays) {
		final STATE returnState = createCopy();

		for (final IBoogieVar var : vars) {
			setValueInternally(returnState, var, createTopValue());
		}
		for (final IBoogieVar bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.TOP);
		}
		for (final IBoogieVar array : arrays) {
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
	protected STATE setVarsToBottom(final List<IBoogieVar> vars, final List<IBoogieVar> bools,
	        final List<IBoogieVar> arrays) {
		final STATE returnState = createCopy();

		for (final IBoogieVar var : vars) {
			setValueInternally(returnState, var, createBottomValue());
		}
		for (final IBoogieVar bool : bools) {
			setValueInternally(returnState, bool, BooleanValue.BOTTOM);
		}
		for (final IBoogieVar array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, createBottomValue());
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
	public STATE merge(final STATE other) {
		assert other != null;

		if (!hasSameVariables(other)) {
			throw new UnsupportedOperationException(
			        "Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final STATE returnState = createCopy();

		for (final IBoogieVar var : mVariables) {

			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var,
					        getVar2ValueBoolean().get(var).merge(other.getVar2ValueBoolean().get(var)));
				} else {
					setValueInternally(returnState, var,
					        getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
				}
			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				setValueInternally(returnState, var,
				        getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
			} else {
				setValueInternally(returnState, var,
				        getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
			}
		}
		return returnState;
	}

	protected Map<IBoogieVar, BooleanValue> getVar2ValueBoolean() {
		return mBooleanValuesMap;
	}

	protected Map<IBoogieVar, V> getVar2ValueNonrelational() {
		return mValueMap;
	}

	protected ILogger getLogger() {
		return mLogger;
	}
}
