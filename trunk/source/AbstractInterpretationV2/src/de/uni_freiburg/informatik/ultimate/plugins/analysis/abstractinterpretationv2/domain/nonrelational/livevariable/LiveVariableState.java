/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.livevariable;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LiveVariableState<ACTION extends IAction>
		implements IAbstractState<LiveVariableState<ACTION>> {

	private static int sId;
	private final int mId;

	private final Set<IProgramVarOrConst> mLive;

	LiveVariableState() {
		this(new HashSet<>());
	}

	LiveVariableState(final Set<IProgramVarOrConst> live) {
		mLive = Objects.requireNonNull(live);
		mId = getFreshId();
	}

	@Override
	public LiveVariableState<ACTION> addVariable(final IProgramVarOrConst variable) {
		// this domain does not track variables
		return this;
	}

	@Override
	public LiveVariableState<ACTION> removeVariable(final IProgramVarOrConst variable) {
		// this domain does not track variables
		return this;
	}

	@Override
	public LiveVariableState<ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		// this domain does not track variables
		return this;
	}

	@Override
	public LiveVariableState<ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		// this domain does not track variables
		return this;
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		// we contain all the variables ;)
		return true;
	}

	@Override
	public LiveVariableState<ACTION> renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		// we contain all the variables ;)
		return this;
	}

	@Override
	public LiveVariableState<ACTION> patch(final LiveVariableState<ACTION> dominator) {
		return union(dominator);
	}

	@Override
	public boolean isEmpty() {
		return false;
	}

	@Override
	public boolean isBottom() {
		// A live variable state cannot be bottom.
		return false;
	}

	@Override
	public boolean isEqualTo(final LiveVariableState<ACTION> other) {
		if (other == null) {
			return false;
		}
		return mLive.equals(other.mLive);
	}

	@Override
	public SubsetResult isSubsetOf(final LiveVariableState<ACTION> other) {
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}
		return SubsetResult.NONE;
	}

	@Override
	public LiveVariableState<ACTION> intersect(final LiveVariableState<ACTION> other) {
		final Set<IProgramVarOrConst> intersection = DataStructureUtils.intersection(mLive, other.mLive);
		if (intersection.equals(mLive)) {
			return this;
		} else if (intersection.equals(other.mLive)) {
			return other;
		}
		return new LiveVariableState<>(intersection);
	}

	@Override
	public LiveVariableState<ACTION> union(final LiveVariableState<ACTION> other) {
		final Set<IProgramVarOrConst> union = DataStructureUtils.union(mLive, other.mLive);
		if (union.equals(mLive)) {
			return this;
		} else if (union.equals(other.mLive)) {
			return other;
		}
		return new LiveVariableState<>(union);
	}

	@Override
	public Term getTerm(final Script script) {
		return script.term("true");
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('{');
		if (!mLive.isEmpty()) {
			mLive.stream().forEach(a -> sb.append(a).append(", "));
			sb.delete(sb.length() - 2, sb.length());
		}
		sb.append('}');
		return sb.toString();
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
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		@SuppressWarnings("unchecked")
		final LiveVariableState<ACTION> other = (LiveVariableState<ACTION>) obj;
		if (!isEqualTo(other)) {
			return false;
		}
		return other.mId == mId;
	}

	public Set<IProgramVarOrConst> getLiveVariables() {
		return Collections.unmodifiableSet(mLive);
	}

	public Set<IProgramVar> getLiveVariablesAsProgramVars() {
		assert mLive.stream()
				.allMatch(element -> element instanceof IProgramVar) : "Not all live variables are of type IProgramVar";
		return mLive.stream().map(element -> (IProgramVar) element).collect(Collectors.toSet());
	}

	private static int getFreshId() {
		sId++;
		return sId;
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.emptySet();
	}

	@Override
	public LiveVariableState<ACTION> compact() {
		// live variable states are always compact
		return this;
	}

}
