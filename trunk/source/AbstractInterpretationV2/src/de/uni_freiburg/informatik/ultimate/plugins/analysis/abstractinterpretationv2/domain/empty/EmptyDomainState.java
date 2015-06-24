package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;

/**
 * 
 * This is an abstract state of the {@link EmptyDomain}. It does save variable
 * declarations, but no values or value representations. It is equal to other
 * {@link EmptyDomainState} instances with the same variable declarations.
 * 
 * This state is never bottom but always a fixpoint.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class EmptyDomainState<ACTION, VARDECL> implements IAbstractState<ACTION, VARDECL> {

	private static int sId;
	private final Map<String, VARDECL> mVarDecls;
	private final int mId;
	private boolean mIsFixpoint;

	protected EmptyDomainState() {
		mVarDecls = new HashMap<String, VARDECL>();
		mIsFixpoint = false;
		mId = sId++;
	}

	protected EmptyDomainState(Map<String, VARDECL> varDecls, boolean isFixpoint) {
		mVarDecls = varDecls;
		mIsFixpoint = isFixpoint;
		mId = sId++;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		final VARDECL old = newMap.put(name, variable);
		if (old != null) {
			throw new UnsupportedOperationException("Variable names have to be disjoint");
		}
		return new EmptyDomainState<ACTION, VARDECL>(newMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		final VARDECL oldVar = newMap.remove(name);
		assert variable.equals(oldVar);
		return new EmptyDomainState<ACTION, VARDECL>(newMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names have to be disjoint");
			}
		}
		return new EmptyDomainState<ACTION, VARDECL>(newMap, mIsFixpoint);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			newMap.remove(entry.getKey());
		}
		return new EmptyDomainState<ACTION, VARDECL>(newMap, mIsFixpoint);
	}

	@Override
	public boolean isEmpty() {
		return mVarDecls.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	@Override
	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> setFixpoint(boolean value) {
		return new EmptyDomainState<ACTION, VARDECL>(mVarDecls, value);
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder().append(mIsFixpoint)
				.append(" ");
		for (Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			sb.append(entry.getKey()).append("; ");
		}
		return sb.toString();
	}

	@Override
	public boolean isEqualTo(IAbstractState<ACTION, VARDECL> other) {
		if (other == null) {
			return false;
		}
		if (!getClass().isInstance(other)) {
			return false;
		}

		final EmptyDomainState<ACTION, VARDECL> comparableOther = (EmptyDomainState<ACTION, VARDECL>) other;
		if (comparableOther.mVarDecls.size() != mVarDecls.size()) {
			return false;
		}

		for (Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			final VARDECL otherValue = comparableOther.mVarDecls.get(entry.getKey());
			if (!entry.getValue().equals(otherValue)) {
				return false;
			}
		}
		return true;
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
	public IAbstractState<ACTION, VARDECL> copy() {
		return new EmptyDomainState<>(new HashMap<String, VARDECL>(mVarDecls), mIsFixpoint);
	}

	/**
	 * This method compares if this state contains the same variable
	 * declarations than the other state.
	 * 
	 * @param other
	 *            another state
	 * @return true iff this state has the same variables than other
	 */
	protected boolean hasSameVariables(IAbstractState<ACTION, VARDECL> other) {
		return isEqualTo(other);
	}

	protected Map<String, VARDECL> getVariables() {
		return new HashMap<>(mVarDecls);
	}

	@Override
    public boolean containsVariable(String name) {
		return mVarDecls.containsKey(name);
    }

}
