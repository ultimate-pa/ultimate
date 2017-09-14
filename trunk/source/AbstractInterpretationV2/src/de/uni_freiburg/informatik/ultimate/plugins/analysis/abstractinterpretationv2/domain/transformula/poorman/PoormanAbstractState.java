/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Abstract state type for the poorman's abstract domain that enables transformula support in abstract interpretation.
 * This state wraps common {@link IBoogieVar}-based states and exposes only a {@link IProgramVarOrConst}-based state.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class PoormanAbstractState<BACKING extends IAbstractState<BACKING, IBoogieVar>>
		implements IAbstractState<PoormanAbstractState<BACKING>, IProgramVarOrConst> {

	private static int sId;

	private final IUltimateServiceProvider mServices;
	private final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> mBoogieVarBackingDomain;
	private final int mId;

	private BACKING mBackingState;

	private Map<IProgramVarOrConst, IBoogieVar> mProgramToBoogieVar;

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> boogieVarBackingDomain) {
		this(services, boogieVarBackingDomain, Collections.emptyMap());
	}

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> boogieVarBackingDomain, final boolean isBottom) {
		this(services, boogieVarBackingDomain, Collections.emptyMap(), isBottom);
	}

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> boogieVarBackingDomain,
			final Map<IProgramVarOrConst, IBoogieVar> variablesMap) {
		this(services, boogieVarBackingDomain, variablesMap, false);
	}

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge, IBoogieVar> boogieVarBackingDomain,
			final Map<IProgramVarOrConst, IBoogieVar> variablesMap, final boolean isBottom) {
		mId = sId++;
		mServices = services;
		mBoogieVarBackingDomain = boogieVarBackingDomain;
		mProgramToBoogieVar = variablesMap;
		if (isBottom) {
			mBackingState = mBoogieVarBackingDomain.createBottomState();
		} else {
			mBackingState = mBoogieVarBackingDomain.createTopState();
		}
	}

	@Override
	public PoormanAbstractState<BACKING> addVariable(final IProgramVarOrConst variable) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		if (newState.mProgramToBoogieVar.put(variable, getBoogieVar(variable)) != null) {
			throw new UnsupportedOperationException("Variable " + variable + " already present.");
		}

		newState.mBackingState = mBackingState.addVariable(mProgramToBoogieVar.get(variable));

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> removeVariable(final IProgramVarOrConst variable) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		final IBoogieVar boogieVar = newState.mProgramToBoogieVar.remove(variable);
		if (boogieVar == null) {
			throw new UnsupportedOperationException("Variable " + variable + " not found in current abstract state.");
		}

		newState.mBackingState = mBackingState.removeVariable(boogieVar);

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> addVariables(final Collection<IProgramVarOrConst> variables) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		for (final IProgramVarOrConst var : variables) {
			if (newState.mProgramToBoogieVar.put(var, getBoogieVar(var)) != null) {
				throw new UnsupportedOperationException(
						"Variable " + var + " already present in current abstract state.");
			}
		}

		final Set<IBoogieVar> boogieVars =
				variables.stream().map(var -> newState.mProgramToBoogieVar.get(var)).collect(Collectors.toSet());
		assert boogieVars.size() == variables.size();

		newState.mBackingState = mBackingState.addVariables(boogieVars);

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> removeVariables(final Collection<IProgramVarOrConst> variables) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		final Collection<IBoogieVar> boogieVars = new HashSet<>();
		for (final IProgramVarOrConst var : variables) {
			final IBoogieVar boogieVar = newState.mProgramToBoogieVar.remove(var);
			if (boogieVar == null) {
				throw new UnsupportedOperationException("Variable " + var + " not found in current abstract state.");
			}
			boogieVars.add(boogieVar);
		}

		assert boogieVars.size() == variables.size();
		newState.mBackingState = mBackingState.removeVariables(boogieVars);

		return newState;
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		final IBoogieVar boogieVar = mProgramToBoogieVar.get(var);
		return boogieVar != null && mBackingState.containsVariable(boogieVar);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mProgramToBoogieVar.keySet();
	}

	@Override
	public PoormanAbstractState<BACKING>
			renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		if (old2newVars.values().stream().anyMatch(newName -> newState.mProgramToBoogieVar.containsKey(newName))) {
			throw new UnsupportedOperationException("Cannot rename variables, variable name already present.");
		}

		final Map<IProgramVarOrConst, Pair<IBoogieVar, IBoogieVar>> boogieVarMap = old2newVars.entrySet().stream()
				.collect(Collectors.toMap(entry -> entry.getKey(),
						entry -> new Pair<>(newState.mProgramToBoogieVar.get(entry.getKey()),
								getBoogieVar(entry.getValue()))));

		for (final Entry<IProgramVarOrConst, Pair<IBoogieVar, IBoogieVar>> entry : boogieVarMap.entrySet()) {
			newState.mProgramToBoogieVar.remove(entry.getKey());
			newState.mProgramToBoogieVar.put(old2newVars.get(entry.getKey()), entry.getValue().getSecond());
		}

		final Map<IBoogieVar, IBoogieVar> boogieVars = boogieVarMap.values().stream()
				.collect(Collectors.toMap(entry -> entry.getFirst(), entry -> entry.getSecond()));

		newState.mBackingState = mBackingState.renameVariables(boogieVars);

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> patch(final PoormanAbstractState<BACKING> dominator) {
		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		final Map<IProgramVarOrConst, IBoogieVar> varsToAdd = new HashMap<>();

		for (final IProgramVarOrConst var : dominator.mProgramToBoogieVar.keySet()) {
			if (!newState.mProgramToBoogieVar.containsKey(var)) {
				final IBoogieVar ret = varsToAdd.put(var, getBoogieVar(var));
				if (ret != null) {
					throw new UnsupportedOperationException("Variable " + var + " already added during patch.");
				}
			}
		}

		newState.mBackingState = mBackingState.patch(dominator.mBackingState);

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> intersect(final PoormanAbstractState<BACKING> other) {
		if (mProgramToBoogieVar.size() != other.mProgramToBoogieVar.size()) {
			throw new UnsupportedOperationException("Variables are not the same.");
		}

		if (!mProgramToBoogieVar.entrySet().stream().allMatch(entry -> {
			if (!other.mProgramToBoogieVar.containsKey(entry.getKey())) {
				return false;
			}
			if (!other.mProgramToBoogieVar.get(entry.getKey()).equals(entry.getValue())) {
				return false;
			}
			return true;
		})) {
			throw new UnsupportedOperationException("Variable mapping is invalid for intersection.");
		}

		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		newState.mBackingState = mBackingState.intersect(other.mBackingState);

		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> union(final PoormanAbstractState<BACKING> other) {
		if (mProgramToBoogieVar.size() != other.mProgramToBoogieVar.size()) {
			throw new UnsupportedOperationException("Variables are not the same.");
		}

		if (!mProgramToBoogieVar.entrySet().stream().allMatch(entry -> {
			if (!other.mProgramToBoogieVar.containsKey(entry.getKey())) {
				return false;
			}
			if (!other.mProgramToBoogieVar.get(entry.getKey()).equals(entry.getValue())) {
				return false;
			}
			return true;
		})) {
			throw new UnsupportedOperationException("Variable mapping is invalid for intersection.");
		}

		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		newState.mBackingState = mBackingState.union(other.mBackingState);

		return newState;
	}

	@Override
	public boolean isEmpty() {
		return mBackingState.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mBackingState.isBottom();
	}

	@Override
	public boolean isEqualTo(final PoormanAbstractState<BACKING> other) {
		return mBackingState.isEqualTo(other.mBackingState);
	}

	@Override
	public SubsetResult isSubsetOf(final PoormanAbstractState<BACKING> other) {
		return mBackingState.isSubsetOf(other.mBackingState);
	}

	@Override
	public PoormanAbstractState<BACKING> compact() {

		final PoormanAbstractState<BACKING> newState =
				new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain, new HashMap<>(mProgramToBoogieVar));

		newState.mBackingState = mBackingState.compact();

		final Set<String> newVars = newState.mBackingState.getVariables().stream().map(var -> var.getGloballyUniqueId())
				.collect(Collectors.toSet());

		newState.mProgramToBoogieVar = newState.mProgramToBoogieVar.entrySet().stream()
				.filter(entry -> newVars.contains(entry.getValue().getGloballyUniqueId()))
				.collect(Collectors.toMap(entry -> entry.getKey(), entry -> entry.getValue()));

		return newState;
	}

	@Override
	public Term getTerm(final Script script) {
		if (isBottom()) {
			return script.term("false");
		}

		return mBackingState.getTerm(script);
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(this.getClass().getSimpleName()).append(": ").append(mBackingState.toLogString());

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

	private static final IBoogieVar getBoogieVar(final IProgramVarOrConst programVar) {
		return new IBoogieVar() {

			@Override
			public Sort getSort() {
				if (programVar instanceof IProgramVar) {
					return ((IProgramVar) programVar).getTermVariable().getSort();
				} else {
					throw new UnsupportedOperationException(
							"No sort for type " + programVar.getClass().getSimpleName());
				}
			}

			@Override
			public String getGloballyUniqueId() {
				return programVar.getGloballyUniqueId();
			}

			@Override
			public ApplicationTerm getDefaultConstant() {
				if (programVar instanceof IProgramVar) {
					return ((IProgramVar) programVar).getDefaultConstant();
				} else if (programVar instanceof IProgramConst) {
					return ((IProgramConst) programVar).getDefaultConstant();
				} else {
					throw new UnsupportedOperationException(
							"Unsupported variable type: " + programVar.getClass().getSimpleName());
				}
			}

			@Override
			public String toString() {
				return getGloballyUniqueId();
			}
		};
	}

	protected BACKING getBackingState() {
		return mBackingState;
	}
}
