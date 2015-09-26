package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.*;

public class ValueState implements IAbstractState<ValueState> {
	private final ValueDomain mDomain;
	private final HashMap<TypedAbstractVariable, IAbstractValue<?>> mMapping;

	private boolean mIsBottom;

	// private boolean mIsTop;

	public ValueState(ValueDomain domain, boolean isBottom) {
		mDomain = domain;
		mMapping = new HashMap<TypedAbstractVariable, IAbstractValue<?>>();
		mIsBottom = isBottom;
		// mIsTop = isTop;
	}

	public Set<Entry<TypedAbstractVariable, IAbstractValue<?>>> getEntries() {
		return mMapping.entrySet();
	}

	@Override
	public boolean isSuperOrEqual(IAbstractState<ValueState> other) {
		if (mIsBottom) {
			return false;
		}

		ValueState otherState = (ValueState) other;
		Set<TypedAbstractVariable> otherKeys = otherState.mMapping.keySet();
		for (AbstractVariable var : otherKeys) {
			IAbstractValue thisValue = mMapping.get(var);
			if (thisValue == null) {
				return false;
			}
			IAbstractValue otherValue = otherState.mMapping.get(var);
			if (otherValue != null && !thisValue.isSuperOrEqual(otherValue)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean hasVariable(AbstractVariable variable) {
		return mMapping.containsKey(variable);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#declareVariable(de
	 * .uni_freiburg.informatik.
	 * ultimate.plugins.analysis.abstractinterpretationMk2
	 * .TypedAbstractVariable)
	 */
	@Override
	public void declareVariable(TypedAbstractVariable variable) {
		if (variable.getDeclaration() == null && variable.getType() == null) {
			throw new RuntimeException();
		}
		if (mMapping.containsKey(variable)) {
			// info: variable is already present
			return;
		}

		mMapping.put(variable,
				mDomain.getTopBottomValueForType(variable.getType(), true));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#getTypedVariable(de
	 * .uni_freiburg.informatik
	 * .ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable)
	 */
	public TypedAbstractVariable getTypedVariable(AbstractVariable variable) {
		for (TypedAbstractVariable tav : mMapping.keySet()) {
			if (tav.equals(variable)) {
				return tav;
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.plugins.analysis.
	 * abstractinterpretationMk2
	 * .abstractdomain.IAbstractState#removeVariable(de.
	 * uni_freiburg.informatik.ultimate
	 * .plugins.analysis.abstractinterpretationMk2.AbstractVariable)
	 */
	@Override
	public void removeVariable(AbstractVariable variable) {
		if (!mMapping.containsKey(variable)) {
			// info: variable is already not present in this state
			return;
		}
	}

	@Override
	public IAbstractState<ValueState> copy() {
		ValueState copy = new ValueState(mDomain, mIsBottom);

		if (isBottom()) {
			copy.mIsBottom = true;
			return copy;
		}
		for (Entry<TypedAbstractVariable, IAbstractValue<?>> entry : mMapping
				.entrySet()) {
			copy.mMapping.put(entry.getKey(), entry.getValue());
		}

		return copy;
	}

	/**
	 * Assigns the given value to this state
	 * 
	 * @param identifier
	 *            An existing identifier
	 * @param value
	 *            The new value
	 * @return True iff a layer with the given identifier exists so the value
	 *         could be written
	 */
	public void writeValue(TypedAbstractVariable variable,
			IAbstractValue<?> value) {
		// if(variable.getDeclaration() == null || variable.getType() == null)
		// {
		// //throw new RuntimeException();
		// }
		mMapping.put(variable, value);
	}

	/**
	 * Returns the value of a given variable or top, if the variable was not
	 * declared yet
	 * 
	 * @param variable
	 * @return
	 */
	public IAbstractValue<?> getValue(TypedAbstractVariable variable) {
		IAbstractValue<?> result = mMapping.get(variable);
		if (result == null) {
			// throw new RuntimeException();
			// mDomain.getLogger().warn("Acessing declared but undefined variable: "
			// + variable);
			return mDomain.getTopBottomValueForType(variable.getType(), true);
		}
		return result;
	}

	/**
	 * Returns the value of an identifier or null if no variable was declared
	 * for that identifier
	 * 
	 * @param identifier
	 * @return
	 */
	public IAbstractValue<?> getValue(String identifier) {
		return mMapping.get(new AbstractVariable(identifier));
	}

	@Override
	public boolean isBottom() {
		if (mIsBottom) {
			return true;
		}

		Iterator<Entry<TypedAbstractVariable, IAbstractValue<?>>> it = mMapping
				.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry<TypedAbstractVariable, IAbstractValue<?>> pair = (Map.Entry<TypedAbstractVariable, IAbstractValue<?>>) it
					.next();
			if (pair.getValue().isBottom()) {
				// if any variable is bottom, this state is also bottom
				mIsBottom = true;
				return true;
			}
		}
		return false;
	}

	@Override
	public ValueState getConcrete() {
		return this;
	}

	public ValueDomain getDomain() {
		return mDomain;
	}

	@Override
	public String toString()

	{
		String s = "";
		for (Entry<TypedAbstractVariable, IAbstractValue<?>> entry : mMapping
				.entrySet()) {
			if (s.length() > 0) {
				s += ", ";
			}
			s += entry.getKey().toString() + ": " + entry.getValue().toString();
		}
		return "[" + s + "]";
	}

}
