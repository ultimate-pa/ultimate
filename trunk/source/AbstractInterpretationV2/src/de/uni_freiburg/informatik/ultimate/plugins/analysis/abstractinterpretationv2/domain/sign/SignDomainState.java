package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;

/**
 * Implementation of an abstract state of the {@link SignDomain}.
 * 
 * Such a state stores the sign values for each variable, including \bot and \top.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 *            Any action.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class SignDomainState<ACTION, VARDECL> implements IAbstractState<ACTION, VARDECL> {


	private Map<String, VARDECL> mVariablesMap;
	private Map<String, SignDomainValue> mValuesMap;

	private boolean mIsFixpoint;

	protected SignDomainState() {
		mVariablesMap = new HashMap<String, VARDECL>();
		mValuesMap = new HashMap<String, SignDomainValue>();
		mIsFixpoint = false;
	}

	public SignDomainState(Map<String, VARDECL> variablesMap, Map<String, SignDomainValue> valuesMap, boolean isFixpoint) {
		mVariablesMap = variablesMap;
		mValuesMap = valuesMap;
		mIsFixpoint = isFixpoint;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final VARDECL old = newVarMap.put(name, variable);
		if (old != null) {
			throw new UnsupportedOperationException("Variable names must be disjoint.");
		}

		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.put(name, new SignDomainValue(Values.TOP));

		return new SignDomainState<ACTION, VARDECL>(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		newValMap.remove(name);

		return new SignDomainState<ACTION, VARDECL>(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newVarMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names must be disjoint.");
			}
			newValMap.put(entry.getKey(), new SignDomainValue(Values.TOP));
		}

		return new SignDomainState<ACTION, VARDECL>(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newVarMap = new HashMap<String, VARDECL>(mVariablesMap);
		final Map<String, SignDomainValue> newValMap = new HashMap<String, SignDomainValue>(mValuesMap);
		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
		}

		return new SignDomainState<ACTION, VARDECL>(newVarMap, newValMap, mIsFixpoint);
	}

	@Override
	public boolean isEmpty() {
		return mVariablesMap.isEmpty();
	}

	@Override
	public boolean isBottom() {
		for (Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			if (entry.getValue().getResult().equals(Values.BOTTOM)) {
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
		return new SignDomainState<ACTION, VARDECL>(mVariablesMap, mValuesMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = value1; var2 : type2 = value2; ...".
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		for (Entry<String, VARDECL> entry : mVariablesMap.entrySet()) {
			sb.append(entry.getKey()).append(":").append(entry.getValue()).append(" = ")
			        .append(mValuesMap.get(entry.getKey().toString()).getResult()).append("; ");
		}
		return sb.toString();
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

		final SignDomainState<ACTION, VARDECL> comparableOther = (SignDomainState<ACTION, VARDECL>) other;
		for (Entry<String, SignDomainValue> entry : mValuesMap.entrySet()) {
			final SignDomainValue otherValue = comparableOther.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).getResult().equals(otherValue.getResult())) {
				return false;
			}
		}

		return true;
	}

	protected boolean hasSameVariables(IAbstractState<ACTION, VARDECL> other) {
		if (other == null) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		final SignDomainState<ACTION, VARDECL> comparableOther = (SignDomainState<ACTION, VARDECL>) other;
		if (comparableOther.mVariablesMap.size() != mVariablesMap.size()) {
			return false;
		}

		for (Entry<String, VARDECL> entry : mVariablesMap.entrySet()) {
			final VARDECL otherType = comparableOther.mVariablesMap.get(entry.getKey());
			if (!entry.getValue().equals(otherType)) {
				return false;
			}
		}

		return true;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> copy() {
		return new SignDomainState<ACTION, VARDECL>(new HashMap<String, VARDECL>(mVariablesMap),
		        new HashMap<String, SignDomainValue>(mValuesMap), mIsFixpoint);
	}

	protected Map<String, VARDECL> getVariables() {
		return new HashMap<String, VARDECL>(mVariablesMap);
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

	@Override
	public boolean containsVariable(String name) {
		return mVariablesMap.containsKey(name);
	}

}
