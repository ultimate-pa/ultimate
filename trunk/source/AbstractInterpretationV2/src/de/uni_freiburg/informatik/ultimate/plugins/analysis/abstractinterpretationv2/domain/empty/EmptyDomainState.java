/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;

/**
 * 
 * This is an abstract state of the {@link EmptyDomain}. It does save variable declarations, but no values or value
 * representations. It is equal to other {@link EmptyDomainState} instances with the same variable declarations.
 * 
 * This state is never bottom but always a fixpoint.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class EmptyDomainState<ACTION, VARDECL>
		implements IAbstractState<EmptyDomainState<ACTION, VARDECL>, ACTION, VARDECL> {

	private static int sId;
	private final Map<String, VARDECL> mVarDecls;
	private final int mId;

	protected EmptyDomainState() {
		mVarDecls = new HashMap<String, VARDECL>();
		mId = sId++;
	}

	protected EmptyDomainState(Map<String, VARDECL> varDecls) {
		mVarDecls = varDecls;
		mId = sId++;
	}

	@Override
	public EmptyDomainState<ACTION, VARDECL> addVariable(String name, VARDECL variable) {
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
	public EmptyDomainState<ACTION, VARDECL> removeVariable(String name, VARDECL variable) {
		assert name != null;
		assert variable != null;

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		final VARDECL oldVar = newMap.remove(name);
		assert variable.equals(oldVar);
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
	}

	@Override
	public EmptyDomainState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			final VARDECL old = newMap.put(entry.getKey(), entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException("Variable names have to be disjoint");
			}
		}
		return new EmptyDomainState<ACTION, VARDECL>(newMap);
	}

	@Override
	public EmptyDomainState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, VARDECL> newMap = new HashMap<>(mVarDecls);
		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
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
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			sb.append(entry.getKey()).append("; ");
		}
		return sb.toString();
	}

	@Override
	public boolean isEqualTo(final EmptyDomainState<ACTION, VARDECL> other) {
		if (other == null) {
			return false;
		}

		if (other.mVarDecls.size() != mVarDecls.size()) {
			return false;
		}

		for (final Entry<String, VARDECL> entry : mVarDecls.entrySet()) {
			final VARDECL otherValue = other.mVarDecls.get(entry.getKey());
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

	/**
	 * This method compares if this state contains the same variable declarations than the other state.
	 * 
	 * @param other
	 *            another state
	 * @return true iff this state has the same variables than other
	 */
	protected boolean hasSameVariables(EmptyDomainState<ACTION, VARDECL> other) {
		return isEqualTo(other);
	}

	@Override
	public Map<String, VARDECL> getVariables() {
		return Collections.unmodifiableMap(mVarDecls);
	}

	@Override
	public boolean containsVariable(String name) {
		return mVarDecls.containsKey(name);
	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		return script.term("true");
	}

	@Override
	public VARDECL getVariableDeclarationType(String name) {
		assert name != null;
		assert mVarDecls.containsKey(name);

		return mVarDecls.get(name);
	}

	@Override
	public EmptyDomainState<ACTION, VARDECL> patch(final EmptyDomainState<ACTION, VARDECL> dominator) {
		if (dominator.isEmpty()) {
			return this;
		} else if (isEmpty()) {
			return dominator;
		}

		final Map<String, VARDECL> newVarDecls = new HashMap<String, VARDECL>();
		newVarDecls.putAll(mVarDecls);
		newVarDecls.putAll(dominator.mVarDecls);

		if (newVarDecls.size() == mVarDecls.size()) {
			return this;
		}

		return new EmptyDomainState<ACTION, VARDECL>(newVarDecls);
	}

	@Override
	public SubsetResult isSubsetOf(EmptyDomainState<ACTION, VARDECL> other) {
		assert hasSameVariables(other);
		return isEqualTo(other) ? SubsetResult.EQUAL : SubsetResult.NONE;
	}
}
