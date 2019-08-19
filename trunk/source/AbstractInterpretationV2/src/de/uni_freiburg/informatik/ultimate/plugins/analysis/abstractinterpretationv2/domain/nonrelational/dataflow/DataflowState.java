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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DataflowState<ACTION extends IAction> implements IAbstractState<DataflowState<ACTION>> {

	private static int sId;
	private final int mId;

	private final Set<IProgramVarOrConst> mVars;
	private final Map<IProgramVarOrConst, Set<ACTION>> mDef;
	private final Map<IProgramVarOrConst, Set<ACTION>> mUse;
	private final Map<IProgramVarOrConst, Set<ACTION>> mReachDef;
	private final Map<IProgramVarOrConst, Set<IcfgLocation>> mNoWrite;

	DataflowState() {
		this(new HashSet<>(), new HashMap<>(), new HashMap<>(), new HashMap<>(), new HashMap<>());
	}

	DataflowState(final Set<IProgramVarOrConst> vars, final Map<IProgramVarOrConst, Set<ACTION>> def,
			final Map<IProgramVarOrConst, Set<ACTION>> use, final Map<IProgramVarOrConst, Set<ACTION>> reachdef,
			final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite) {
		assert vars != null;
		assert def != null;
		assert use != null;
		assert reachdef != null;
		mVars = vars;
		mDef = def;
		mUse = use;
		mReachDef = reachdef;
		mId = getFreshId();
		mNoWrite = noWrite;
	}

	@Override
	public DataflowState<ACTION> addVariable(final IProgramVarOrConst variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars, mVars.size() + 1);
		vars.add(variable);
		return new DataflowState<>(vars, mDef, mUse, mReachDef, mNoWrite);
	}

	@Override
	public DataflowState<ACTION> removeVariable(final IProgramVarOrConst variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars);
		vars.remove(variable);
		final Map<IProgramVarOrConst, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		def.remove(variable);
		final Map<IProgramVarOrConst, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		use.remove(variable);
		final Map<IProgramVarOrConst, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		use.remove(variable);
		final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);
		use.remove(variable);
		return new DataflowState<>(vars, def, use, reachdef, noWrite);
	}

	@Override
	public DataflowState<ACTION> addVariables(final Collection<IProgramVarOrConst> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars, mVars.size() + variables.size());
		vars.addAll(variables);
		return new DataflowState<>(vars, mDef, mUse, mReachDef, mNoWrite);
	}

	@Override
	public DataflowState<ACTION> removeVariables(final Collection<IProgramVarOrConst> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars);
		final Map<IProgramVarOrConst, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		final Map<IProgramVarOrConst, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		final Map<IProgramVarOrConst, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);
		variables.stream().forEach(a -> {
			vars.remove(a);
			def.remove(a);
			use.remove(a);
			reachdef.remove(a);
			noWrite.remove(a);
		});
		return new DataflowState<>(vars, def, use, reachdef, noWrite);
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return Collections.unmodifiableSet(mVars);
	}

	@Override
	public DataflowState<ACTION> patch(final DataflowState<ACTION> dominator) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isEmpty() {
		return mVars.isEmpty();
	}

	@Override
	public boolean isBottom() {
		// A basic dataflow state is never bottom
		return false;
	}

	@Override
	public boolean isEqualTo(final DataflowState<ACTION> other) {
		if (other == null) {
			return false;
		}
		if (!other.mVars.equals(mVars)) {
			return false;
		}
		if (!other.mDef.equals(mDef)) {
			return false;
		}
		if (!other.mUse.equals(mUse)) {
			return false;
		}
		if (!other.mReachDef.equals(mReachDef)) {
			return false;
		}
		return other.mNoWrite.equals(mNoWrite);
	}

	@Override
	public SubsetResult isSubsetOf(final DataflowState<ACTION> other) {
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}
		return SubsetResult.NONE;
	}

	@Override
	public Term getTerm(final Script script) {
		return script.term("true");
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('{');
		for (final Entry<IProgramVarOrConst, Set<ACTION>> entry : mReachDef.entrySet()) {
			if (entry.getValue().isEmpty()) {
				continue;
			}
			sb.append(entry.getKey().getGloballyUniqueId());
			sb.append("->");
			if (entry.getValue().size() == 1) {
				sb.append(entry.getValue().iterator().next().hashCode());
			} else {
				sb.append('{');
				for (final ACTION value : entry.getValue()) {
					sb.append(value.hashCode());
					sb.append(", ");
				}
				sb.delete(sb.length() - 2, sb.length());
				sb.append('}');
			}
			sb.append(", ");
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
		final DataflowState<ACTION> other = (DataflowState<ACTION>) obj;
		if (!isEqualTo(other)) {
			return false;
		}
		return other.mId == mId;
	}

	Map<IProgramVarOrConst, Set<ACTION>> getDef() {
		return Collections.unmodifiableMap(mDef);
	}

	Map<IProgramVarOrConst, Set<ACTION>> getUse() {
		return Collections.unmodifiableMap(mUse);
	}

	Map<IProgramVarOrConst, Set<ACTION>> getReachingDefinitions() {
		return Collections.unmodifiableMap(mReachDef);
	}

	Map<IProgramVarOrConst, Set<IcfgLocation>> getNoWrite() {
		return Collections.unmodifiableMap(mNoWrite);
	}

	@Override
	public DataflowState<ACTION> union(final DataflowState<ACTION> other) {
		if (other == null || other == this || other.isEqualTo(this)) {
			return this;
		}

		if (!mVars.equals(other.mVars)) {
			throw new UnsupportedOperationException("Cannot create union of two incompatible dataflow states");
		}

		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars);
		final Map<IProgramVarOrConst, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		final Map<IProgramVarOrConst, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		final Map<IProgramVarOrConst, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);

		// TODO: What about def and use?

		for (final Entry<IProgramVarOrConst, Set<ACTION>> otherEntry : other.mReachDef.entrySet()) {
			final Set<ACTION> set = reachdef.get(otherEntry.getKey());
			if (set == null) {
				reachdef.put(otherEntry.getKey(), new HashSet<>(otherEntry.getValue()));
			} else {
				final Set<ACTION> newset = new HashSet<>();
				newset.addAll(otherEntry.getValue());
				newset.addAll(set);
				reachdef.put(otherEntry.getKey(), newset);
			}
		}

		for (final Entry<IProgramVarOrConst, Set<IcfgLocation>> otherEntry : other.mNoWrite.entrySet()) {
			final Set<IcfgLocation> set = noWrite.get(otherEntry.getKey());
			if (set == null) {
				noWrite.put(otherEntry.getKey(), new HashSet<>(otherEntry.getValue()));
			} else {
				final Set<IcfgLocation> newset = new HashSet<>();
				newset.addAll(otherEntry.getValue());
				newset.addAll(set);
				noWrite.put(otherEntry.getKey(), newset);
			}
		}

		return new DataflowState<>(vars, def, use, reachdef, noWrite);
	}

	@Override
	public DataflowState<ACTION> intersect(final DataflowState<ACTION> other) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	private static int getFreshId() {
		sId++;
		return sId;
	}

	public Set<IcfgLocation> getNowriteLocations(final IProgramVar iProgramVar) {
		return mNoWrite.get(iProgramVar);
	}

	public Set<ACTION> getReachingDefinitions(final IProgramVar var) {
		return mReachDef.get(var);
	}

	@Override
	public DataflowState<ACTION> compact() {
		// dataflow states are always compact
		return this;
	}

	@Override
	public DataflowState<ACTION> renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		if (old2newVars == null || old2newVars.isEmpty()) {
			return this;
		}
		final Set<IProgramVarOrConst> vars = DataStructureUtils.getFreshSet(mVars);
		final Map<IProgramVarOrConst, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		final Map<IProgramVarOrConst, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		final Map<IProgramVarOrConst, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		final Map<IProgramVarOrConst, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);

		@SuppressWarnings("unchecked")
		final Map<IProgramVarOrConst, Object>[] maps = new Map[] { def, use, reachdef, noWrite };

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

			if (!vars.remove(oldVar)) {
				continue;
			}
			isChanged = true;
			vars.add(newVar);

			for (final Map<IProgramVarOrConst, Object> map : maps) {
				if (map.containsKey(oldVar)) {
					final Object oldVal = map.remove(oldVar);
					map.put(newVar, oldVal);
				}
			}
		}
		if (isChanged) {
			return new DataflowState<>(vars, def, use, reachdef, noWrite);
		}
		return this;
	}
}
