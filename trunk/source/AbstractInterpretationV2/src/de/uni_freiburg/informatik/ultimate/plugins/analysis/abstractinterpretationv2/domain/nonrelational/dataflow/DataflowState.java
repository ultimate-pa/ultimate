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

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DataflowState<ACTION extends IAction>
		implements IAbstractState<DataflowState<ACTION>, ACTION, IProgramVar> {

	private static int sId;
	private final int mId;

	private final Set<IProgramVar> mVars;
	private final Map<IProgramVar, Set<ACTION>> mDef;
	private final Map<IProgramVar, Set<ACTION>> mUse;
	private final Map<IProgramVar, Set<ACTION>> mReachDef;
	private final Map<IProgramVar, Set<IcfgLocation>> mNoWrite;

	DataflowState() {
		this(new HashSet<>(), new HashMap<>(), new HashMap<>(), new HashMap<>(), new HashMap<>());
	}

	DataflowState(final Set<IProgramVar> vars, final Map<IProgramVar, Set<ACTION>> def,
			final Map<IProgramVar, Set<ACTION>> use, final Map<IProgramVar, Set<ACTION>> reachdef,
			final Map<IProgramVar, Set<IcfgLocation>> noWrite) {
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
	public DataflowState<ACTION> addVariable(final IProgramVar variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars, mVars.size() + 1);
		vars.add(variable);
		return new DataflowState<>(vars, mDef, mUse, mReachDef, mNoWrite);
	}

	@Override
	public DataflowState<ACTION> removeVariable(final IProgramVar variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars);
		vars.remove(variable);
		final Map<IProgramVar, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		def.remove(variable);
		final Map<IProgramVar, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		use.remove(variable);
		final Map<IProgramVar, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		use.remove(variable);
		final Map<IProgramVar, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);
		use.remove(variable);
		return new DataflowState<>(vars, def, use, reachdef, noWrite);
	}

	@Override
	public DataflowState<ACTION> addVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars, mVars.size() + variables.size());
		vars.addAll(variables);
		return new DataflowState<>(vars, mDef, mUse, mReachDef, mNoWrite);
	}

	@Override
	public DataflowState<ACTION> removeVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars);
		final Map<IProgramVar, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		final Map<IProgramVar, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		final Map<IProgramVar, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		final Map<IProgramVar, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);
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
	public boolean containsVariable(final IProgramVar var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVar> getVariables() {
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
		for (final Entry<IProgramVar, Set<ACTION>> entry : mReachDef.entrySet()) {
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

	Map<IProgramVar, Set<ACTION>> getDef() {
		return Collections.unmodifiableMap(mDef);
	}

	Map<IProgramVar, Set<ACTION>> getUse() {
		return Collections.unmodifiableMap(mUse);
	}

	Map<IProgramVar, Set<ACTION>> getReachingDefinitions() {
		return Collections.unmodifiableMap(mReachDef);
	}

	Map<IProgramVar, Set<IcfgLocation>> getNoWrite() {
		return Collections.unmodifiableMap(mNoWrite);
	}

	DataflowState<ACTION> union(final DataflowState<ACTION> other) {
		if (other == null || other == this || other.isEqualTo(this)) {
			return this;
		}

		if (!mVars.equals(other.mVars)) {
			throw new UnsupportedOperationException("Cannot create union of two incompatible dataflow states");
		}

		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars);
		final Map<IProgramVar, Set<ACTION>> def = AbsIntUtil.getFreshMap(mDef);
		final Map<IProgramVar, Set<ACTION>> use = AbsIntUtil.getFreshMap(mUse);
		final Map<IProgramVar, Set<ACTION>> reachdef = AbsIntUtil.getFreshMap(mReachDef);
		final Map<IProgramVar, Set<IcfgLocation>> noWrite = AbsIntUtil.getFreshMap(mNoWrite);

		// TODO: What about def and use?

		for (final Entry<IProgramVar, Set<ACTION>> otherEntry : other.mReachDef.entrySet()) {
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

		for (final Entry<IProgramVar, Set<IcfgLocation>> otherEntry : other.mNoWrite.entrySet()) {
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
}
