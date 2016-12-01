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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.LoggingHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public abstract class NonrelationalState<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		implements INonrelationalAbstractState<STATE, CodeBlock> {
	
	protected enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}
	
	private static int sId;
	private final int mId;
	
	private final Set<IProgramVarOrConst> mVariables;
	private final Map<IProgramVarOrConst, V> mValueMap;
	private final Map<IProgramVarOrConst, BooleanValue> mBooleanValuesMap;
	
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
	protected NonrelationalState(final ILogger logger, final Set<IProgramVarOrConst> variables,
			final Map<IProgramVarOrConst, V> valuesMap, final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap) {
		mVariables = new HashSet<>(variables);
		mValueMap = new HashMap<>(valuesMap);
		mBooleanValuesMap = new HashMap<>(booleanValuesMap);
		sId++;
		mId = sId;
		mLogger = logger;
	}
	
	@Override
	public STATE addVariable(final IProgramVarOrConst variable) {
		assert variable != null;
		mLogger.debug("Adding program var " + LoggingHelper.getHashCodeString(variable) + " " + variable);
		final STATE returnState = createCopy();
		addVariableInternally(returnState, variable);
		return returnState;
	}
	
	private void addVariableInternally(final NonrelationalState<STATE, V> state, final IProgramVarOrConst variable) {
		assert state != null;
		assert variable != null;
		
		if (!state.mVariables.add(variable)) {
			throw new UnsupportedOperationException("Variable names must be disjoint. Variable "
					+ LoggingHelper.getHashCodeString(variable) + " is already present.");
		}
		
		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer =
				var -> state.getVar2ValueNonrelational().put(var, createTopValue());
		final Consumer<IProgramVarOrConst> boolConsumer = var -> state.getVar2ValueBoolean().put(var, BooleanValue.TOP);
		
		TypeUtils.consumeVariable(varConsumer, boolConsumer, null, variable);
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public STATE addVariables(final Collection<IProgramVarOrConst> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return (STATE) this;
		}
		
		final Set<IProgramVarOrConst> newVars = new HashSet<>(mVariables);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		
		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer = var -> newValMap.put(var, createTopValue());
		final Consumer<IProgramVarOrConst> boolConsumer = var -> newBooleanValMap.put(var, BooleanValue.TOP);
		
		for (final IProgramVarOrConst var : variables) {
			if (!newVars.add(var)) {
				throw new UnsupportedOperationException("Variable names must be disjoint. The variable "
						+ LoggingHelper.getHashCodeString(var) + " is already present.");
			}
			
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}
		
		return createState(mLogger, newVars, newValMap, newBooleanValMap);
	}
	
	@Override
	public boolean containsVariable(final IProgramVarOrConst name) {
		return mVariables.contains(name);
	}
	
	/**
	 * @return The bottom value.
	 */
	protected abstract V createBottomValue();
	
	/**
	 * @return A copy of <tt>this</tt>.
	 */
	protected abstract STATE createCopy();
	
	/**
	 * Creates a new abstract state of the same type as <tt>this</tt>.
	 *
	 * @param logger
	 * @param newVarMap
	 * @param newValMap
	 * @param newBooleanValMap
	 * @return
	 */
	protected abstract STATE createState(ILogger logger, Set<IProgramVarOrConst> newVarMap,
			Map<IProgramVarOrConst, V> newValMap, Map<IProgramVarOrConst, BooleanValue> newBooleanValMap);
	
	/**
	 * @return The top value.
	 */
	protected abstract V createTopValue();
	
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
	
	/**
	 * Gets an array of specified size of current abstract value types.
	 *
	 * @param size
	 *            The size of the array.
	 * @return A new array of given size for the current abstract value types.
	 */
	protected abstract V[] getArray(int size);
	
	protected ILogger getLogger() {
		return mLogger;
	}
	
	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}
		
		final List<Term> acc = new ArrayList<>(getVar2ValueNonrelational().size() + getVar2ValueBoolean().size());
		
		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final IProgramVarOrConst programVar = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(programVar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				// TODO: Handle boolean variables (easy)
				// TODO: what about arrays (hard -- but perhaps not necessary, cf. Matthias' integer programs)
				continue;
			}
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		
		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final IProgramVarOrConst programVar = entry.getKey();
			final Term var = NonrelationalTermUtils.getTermVar(programVar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		
		return Util.and(script, acc.toArray(new Term[acc.size()]));
	}
	
	public V getValue(final IProgramVarOrConst variableName) {
		if (!getVar2ValueNonrelational().containsKey(variableName)) {
			throw new UnsupportedOperationException(
					"There is no value of variable " + variableName.getGloballyUniqueId() + ".");
		}
		
		return getVar2ValueNonrelational().get(variableName).copy();
	}
	
	protected Map<IProgramVarOrConst, BooleanValue> getVar2ValueBoolean() {
		return mBooleanValuesMap;
	}
	
	protected Map<IProgramVarOrConst, V> getVar2ValueNonrelational() {
		return mValueMap;
	}
	
	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}
	
	protected VariableType getVariableType(final IProgramVarOrConst var) {
		if (!containsVariable(var)) {
			throw new UnsupportedOperationException("The variable " + var + " does not exist in the current state.");
		}
		
		if (getVar2ValueBoolean().containsKey(var)) {
			return VariableType.BOOLEAN;
		}
		
		if (getVar2ValueNonrelational().containsKey(var)) {
			return VariableType.VARIABLE;
		}
		
		// TODO: Implement proper handliny of arrays.
		throw new UnsupportedOperationException(
				"The variable " + var + " exists but was not found in the variable sets.");
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
	private boolean hasSameVariables(final NonrelationalState<STATE, V> other) {
		if (other == null) {
			return false;
		}
		
		if (!getClass().isInstance(other)) {
			return false;
		}
		
		if (other.mVariables.size() != mVariables.size()) {
			return false;
		}
		
		for (final IProgramVarOrConst entry : mVariables) {
			if (!other.mVariables.contains(entry)) {
				return false;
			}
		}
		
		return true;
	}
	
	@Override
	public STATE intersect(final STATE other) {
		assert other != null;
		assert hasSameVariables(other);
		
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
	
	@Override
	public boolean isBottom() {
		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			if (entry.getValue().isBottom()) {
				return true;
			}
		}
		
		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			if (entry.getValue().isBottom()) {
				return true;
			}
		}
		
		return false;
	}
	
	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}
	
	@Override
	public boolean isEqualTo(final STATE other) {
		if (!hasSameVariables(other)) {
			return false;
		}
		
		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!getVar2ValueNonrelational().get(entry.getKey()).isEqualTo(otherValue)) {
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
		
		for (final Entry<IProgramVarOrConst, V> entry : getVar2ValueNonrelational().entrySet()) {
			final V thisValue = entry.getValue();
			final V otherValue = other.getVar2ValueNonrelational().get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}
		
		for (final Entry<IProgramVarOrConst, BooleanValue> entry : getVar2ValueBoolean().entrySet()) {
			final BooleanValue thisValue = entry.getValue();
			final BooleanValue otherValue = other.getVar2ValueBoolean().get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}
		
		return SubsetResult.NON_STRICT;
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
					"Cannot merge the two states as their sets of variables are disjoint.");
		}
		
		final STATE returnState = createCopy();
		
		// TODO: Add array support.
		final Consumer<IProgramVarOrConst> varConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueNonrelational().get(var).merge(other.getVar2ValueNonrelational().get(var)));
		final Consumer<IProgramVarOrConst> boolConsumer = var -> setValueInternally(returnState, var,
				getVar2ValueBoolean().get(var).merge(other.getVar2ValueBoolean().get(varConsumer)));
		
		for (final IProgramVarOrConst var : mVariables) {
			TypeUtils.consumeVariable(varConsumer, boolConsumer, null, var);
		}
		
		return returnState;
	}
	
	@Override
	public STATE patch(final STATE dominator) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public STATE removeVariable(final IProgramVarOrConst variable) {
		assert variable != null;
		
		final Set<IProgramVarOrConst> newVarMap = new HashSet<>(mVariables);
		newVarMap.remove(variable);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		newValMap.remove(variable);
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		newBooleanValMap.remove(variable);
		// TODO: Add array support.
		
		return createState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}
	
	@Override
	public STATE removeVariables(final Collection<IProgramVarOrConst> variables) {
		assert variables != null;
		assert !variables.isEmpty();
		
		final Set<IProgramVarOrConst> newVarMap = new HashSet<>(mVariables);
		final Map<IProgramVarOrConst, V> newValMap = new HashMap<>(getVar2ValueNonrelational());
		final Map<IProgramVarOrConst, BooleanValue> newBooleanValMap = new HashMap<>(getVar2ValueBoolean());
		for (final IProgramVarOrConst entry : variables) {
			newVarMap.remove(entry);
			newValMap.remove(entry);
			newBooleanValMap.remove(entry);
		}
		
		return createState(mLogger, newVarMap, newValMap, newBooleanValMap);
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
	private void setValueInternally(final NonrelationalState<STATE, V> state, final IProgramVarOrConst name,
			final BooleanValue value) {
		assert state != null;
		assert name != null;
		assert state.mVariables.contains(name) : "Variable unknown";
		assert state.getVar2ValueBoolean().get(name) != null : "Boolean variable not in boolean values map";
		state.getVar2ValueBoolean().put(name, value);
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
		assert state.mVariables.contains(var) : "Variable " + var + " unknown";
		assert state.getVar2ValueNonrelational().containsKey(var) : "Variable not in values map";
		state.getVar2ValueNonrelational().put(var, value);
	}
	
	@Override
	public String toLogString() {
		final StringBuilder stringBuilder = new StringBuilder();
		
		for (final IProgramVarOrConst entry : mVariables) {
			stringBuilder.append(entry.getGloballyUniqueId()).append(" = ");
			
			final V val = getVar2ValueNonrelational().get(entry);
			
			// TODO: Implement handling of arrays.
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
}
