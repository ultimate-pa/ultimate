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

	private final Map<String, VARDECL> mVarDecls;

	protected EmptyDomainState() {
		mVarDecls = new HashMap<String, VARDECL>();
	}

	protected EmptyDomainState(Map<String, VARDECL> varDecls) {
		mVarDecls = varDecls;
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
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		newMap.remove(name);
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
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
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
	}

	@Override
	public IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		for (Entry<String, VARDECL> entry : variables.entrySet()) {
			newMap.remove(entry.getKey());
		}
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
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
		return true;
	}

	@Override
	public IAbstractState<ACTION, VARDECL> setFixpoint(boolean value) {
		return new EmptyDomainState<ACTION, VARDECL>(mVarDecls);
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		for (Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			sb.append(entry.getKey()).append(":").append(entry.getValue()).append("; ");
		}
		return sb.toString();
	}

	@Override
	public ComparisonResult compareTo(IAbstractState<ACTION, VARDECL> other) {
		if (other == null) {
			return ComparisonResult.NOTEQUAL;
		}
		if (!getClass().isInstance(other)) {
			return ComparisonResult.NOTEQUAL;
		}

		final EmptyDomainState<ACTION, VARDECL> comparableOther = (EmptyDomainState<ACTION, VARDECL>) other;
		if (comparableOther.mVarDecls.size() != mVarDecls.size()) {
			return ComparisonResult.NOTEQUAL;
		}

		for (Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			final VARDECL otherValue = comparableOther.mVarDecls.get(entry.getKey());
			if (!entry.getValue().equals(otherValue)) {
				return ComparisonResult.NOTEQUAL;
			}
		}
		return ComparisonResult.EQUAL;
	}
	
	@Override
	public String toString() {
		return toLogString();
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
		return compareTo(other) == ComparisonResult.EQUAL;
	}

	protected Map<String, VARDECL> getVariables() {
		return new HashMap<>(mVarDecls);
	}
}
