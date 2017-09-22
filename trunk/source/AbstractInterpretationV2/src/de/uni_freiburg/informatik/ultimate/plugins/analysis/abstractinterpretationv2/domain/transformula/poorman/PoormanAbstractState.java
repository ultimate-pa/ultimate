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
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * Abstract state type for the poorman's abstract domain that enables transformula support in abstract interpretation.
 * This state wraps common {@link IBoogieVar}-based states and exposes only a {@link IProgramVarOrConst}-based state.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class PoormanAbstractState<BACKING extends IAbstractState<BACKING>>
		implements IAbstractState<PoormanAbstractState<BACKING>> {

	private static int sId;

	private final IUltimateServiceProvider mServices;
	private final IAbstractDomain<BACKING, IcfgEdge> mBoogieVarBackingDomain;
	private final int mId;

	private BACKING mBackingState;

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge> boogieVarBackingDomain) {
		this(services, boogieVarBackingDomain, false);
	}

	public PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge> boogieVarBackingDomain, final boolean isBottom) {
		this(services, boogieVarBackingDomain,
				isBottom ? boogieVarBackingDomain.createBottomState() : boogieVarBackingDomain.createTopState());

	}

	protected PoormanAbstractState(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge> boogieVarBackingDomain, final BACKING backingState) {
		mId = sId++;
		mServices = services;
		mBoogieVarBackingDomain = boogieVarBackingDomain;
		mBackingState = backingState;
	}

	@Override
	public PoormanAbstractState<BACKING> addVariable(final IProgramVarOrConst variable) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.addVariable(variable);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> removeVariable(final IProgramVarOrConst variable) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.removeVariable(variable);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> addVariables(final Collection<IProgramVarOrConst> variables) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.addVariables(variables);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> removeVariables(final Collection<IProgramVarOrConst> variables) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.removeVariables(variables);
		return newState;
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mBackingState.containsVariable(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mBackingState.getVariables();
	}

	@Override
	public PoormanAbstractState<BACKING>
			renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.renameVariables(old2newVars);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> patch(final PoormanAbstractState<BACKING> dominator) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.patch(dominator.mBackingState);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> intersect(final PoormanAbstractState<BACKING> other) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.intersect(other.mBackingState);
		return newState;
	}

	@Override
	public PoormanAbstractState<BACKING> union(final PoormanAbstractState<BACKING> other) {
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
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
		final PoormanAbstractState<BACKING> newState = new PoormanAbstractState<>(mServices, mBoogieVarBackingDomain);
		newState.mBackingState = mBackingState.compact();
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

	/**
	 * @return The backing state for Boogie ICFGs corresponding to this poor man's abstract state.
	 */
	protected BACKING getBackingState() {
		return mBackingState;
	}
}
