/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.util.SetOperations;

/**
 * A state in the {@link CompoundDomain}.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class CompoundDomainState implements IAbstractState<CompoundDomainState, IBoogieVar> {

	private static int sId;

	private final IUltimateServiceProvider mServices;

	private final List<IAbstractState<?, IBoogieVar>> mAbstractStates;
	private final List<IAbstractDomain> mDomainList;
	private final int mId;

	/**
	 * Constructor for a new CompountDomainState from a given abstract state.
	 *
	 * @param services
	 *            The Ultimate services.
	 * @param domainList
	 *            The list of abstract domains to use.
	 * @param abstractStateList
	 *            The abstract state to create the new state from.
	 */
	public CompoundDomainState(final IUltimateServiceProvider services, final List<IAbstractDomain> domainList,
			final List<IAbstractState<?, IBoogieVar>> abstractStateList) {
		sId++;
		mId = sId;
		if (domainList.size() != abstractStateList.size()) {
			throw new UnsupportedOperationException(
					"The domain list size and the abstract state list size must be identical.");
		}
		mServices = services;
		mDomainList = domainList;
		mAbstractStates = abstractStateList;
	}

	/**
	 * Constructor for a new compound domain state which is either top or bottom.
	 *
	 * @param services
	 *            The Ultimate services.
	 * @param domainList
	 *            The list of domains.
	 * @param isBottom
	 *            If <code>true</code>, the constructed state is corresponding to &bot;, &top; otherwise.
	 */
	public CompoundDomainState(final IUltimateServiceProvider services, final List<IAbstractDomain> domainList,
			final boolean isBottom) {
		sId++;
		mId = sId;
		mServices = services;
		mDomainList = domainList;
		mAbstractStates = new ArrayList<>();
		if (isBottom) {
			mDomainList.forEach(a -> mAbstractStates.add(a.createBottomState()));
		} else {
			mDomainList.forEach(a -> mAbstractStates.add(a.createTopState()));
		}
	}

	@Override
	public CompoundDomainState addVariable(final IBoogieVar variable) {
		return performStateOperation(state -> state.addVariable(variable));
	}

	@Override
	public CompoundDomainState removeVariable(final IBoogieVar variable) {
		return performStateOperation(state -> state.removeVariable(variable));
	}

	@Override
	public CompoundDomainState addVariables(final Collection<IBoogieVar> variables) {
		return performStateOperation(state -> state.addVariables(variables));
	}

	@Override
	public CompoundDomainState removeVariables(final Collection<IBoogieVar> variables) {
		return performStateOperation(state -> state.removeVariables(variables));
	}

	@Override
	public boolean containsVariable(final IBoogieVar var) {
		return mAbstractStates.get(0).containsVariable(var);
	}

	@Override
	public Set<IBoogieVar> getVariables() {
		return mAbstractStates.get(0).getVariables();
	}

	@Override
	public CompoundDomainState renameVariable(final IBoogieVar oldVar, final IBoogieVar newVar) {
		return performStateOperation(state -> state.renameVariable(oldVar, newVar));
	}

	@Override
	public CompoundDomainState renameVariables(final Map<IBoogieVar, IBoogieVar> old2newVars) {
		return performStateOperation(state -> state.renameVariables(old2newVars));
	}

	@Override
	public CompoundDomainState patch(final CompoundDomainState dominator) {
		assert mAbstractStates.size() == dominator.mAbstractStates.size();

		final List<IAbstractState<?, IBoogieVar>> returnList = new ArrayList<>();
		for (int i = 0; i < mAbstractStates.size(); i++) {
			returnList.add(patchInternally(mAbstractStates.get(i), dominator.mAbstractStates.get(i)));
		}

		return new CompoundDomainState(mServices, mDomainList, returnList);
	}

	private static <T extends IAbstractState> T patchInternally(final T current, final T dominator) {
		return (T) current.patch(dominator);
	}

	@Override
	public boolean isEmpty() {
		return mAbstractStates.get(0).isEmpty();
	}

	@Override
	public boolean isBottom() {
		return mAbstractStates.stream().parallel().anyMatch(IAbstractState::isBottom);
	}

	@Override
	public boolean isEqualTo(final CompoundDomainState other) {
		assert mAbstractStates.size() == other.mAbstractStates.size();
		for (int i = 0; i < mAbstractStates.size(); i++) {
			if (!isEqualToInternally(mAbstractStates.get(i), other.mAbstractStates.get(i))) {
				return false;
			}
		}
		return true;
	}

	private static <T extends IAbstractState> boolean isEqualToInternally(final T current, final T other) {
		return current.isEqualTo(other);
	}

	private static <T extends IAbstractState> SubsetResult isSubsetOfInternally(final T current, final T other) {
		return current.isSubsetOf(other);
	}

	@Override
	public Term getTerm(final Script script) {
		if (mAbstractStates.isEmpty() || isBottom()) {
			return script.term("false");
		}

		if (mAbstractStates.size() == 1) {
			return mAbstractStates.iterator().next().getTerm(script);
		}

		return script.term("and",
				mAbstractStates.stream().map(state -> state.getTerm(script)).toArray(i -> new Term[i]));
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (final IAbstractState<?, IBoogieVar> state : mAbstractStates) {
			sb.append(getShortName(state.getClass())).append(": ").append(state.toLogString()).append(", ");
		}

		return sb.toString();
	}

	private static String getShortName(final Class<?> clazz) {
		final String s = clazz.getSimpleName();
		if (s.length() < 4) {
			return s;
		}
		return s.substring(0, 3);
	}

	private CompoundDomainState
			performStateOperation(final Function<IAbstractState<?, IBoogieVar>, IAbstractState<?, IBoogieVar>> state) {
		return new CompoundDomainState(mServices, mDomainList,
				mAbstractStates.stream().map(state).collect(Collectors.toList()));
	}

	protected List<IAbstractDomain> getDomainList() {
		return mDomainList;
	}

	protected List<IAbstractState<?, IBoogieVar>> getAbstractStatesList() {
		return mAbstractStates;
	}

	@Override
	public int hashCode() {
		return mId;
	}

	@Override
	public SubsetResult isSubsetOf(final CompoundDomainState other) {
		SubsetResult rtr = SubsetResult.EQUAL;
		for (int i = 0; i < mAbstractStates.size(); i++) {
			rtr = isStrictSubsetOf(rtr, mAbstractStates.get(i), other.mAbstractStates.get(i));
			if (rtr == SubsetResult.NONE) {
				return rtr;
			}
		}
		return rtr;
	}

	private static SubsetResult isStrictSubsetOf(final SubsetResult current, final IAbstractState<?, IBoogieVar> aState,
			final IAbstractState<?, IBoogieVar> bState) {
		final SubsetResult result = isSubsetOfInternally(aState, bState);
		return current.min(result);
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public CompoundDomainState intersect(final CompoundDomainState other) {
		final List<IAbstractState<?, IBoogieVar>> thisStates = getAbstractStatesList();
		final List<IAbstractState<?, IBoogieVar>> otherStates = other.getAbstractStatesList();
		final List<IAbstractDomain> domains = getDomainList();

		assert thisStates.size() == otherStates.size();
		assert domains.size() == other.getDomainList().size();
		assert domains.size() == thisStates.size();

		final List<IAbstractState<?, IBoogieVar>> returnStates = new ArrayList<>();

		for (int i = 0; i < thisStates.size(); i++) {
			final IAbstractState<?, IBoogieVar> thisState = thisStates.get(i);
			final IAbstractState<?, IBoogieVar> otherState = otherStates.get(i);
			returnStates.add(applyCasted(thisState, otherState, (a, b) -> a.intersect(b)));
		}

		return new CompoundDomainState(mServices, domains, returnStates);
	}

	@Override
	public CompoundDomainState union(final CompoundDomainState other) {
		final List<IAbstractState<?, IBoogieVar>> thisStates = getAbstractStatesList();
		final List<IAbstractState<?, IBoogieVar>> otherStates = other.getAbstractStatesList();
		final List<IAbstractDomain> domains = getDomainList();

		assert thisStates.size() == otherStates.size();
		assert domains.size() == other.getDomainList().size();
		assert domains.size() == thisStates.size();

		final List<IAbstractState<?, IBoogieVar>> returnStates = new ArrayList<>();

		for (int i = 0; i < thisStates.size(); i++) {
			final IAbstractState<?, IBoogieVar> thisState = thisStates.get(i);
			final IAbstractState<?, IBoogieVar> otherState = otherStates.get(i);
			returnStates.add(applyCasted(thisState, otherState, (a, b) -> a.union(b)));
		}

		return new CompoundDomainState(mServices, domains, returnStates);
	}

	@Override
	public CompoundDomainState compact() {

		final List<IAbstractState<?, IBoogieVar>> thisStates = getAbstractStatesList();
		final int numberOfStates = thisStates.size();
		final List<IAbstractDomain> domains = getDomainList();

		assert domains.size() == thisStates.size();

		final List<IAbstractState<?, IBoogieVar>> compactedStates = new ArrayList<>(numberOfStates);
		final Set<IBoogieVar> vars = new HashSet<>();
		for (final IAbstractState<?, IBoogieVar> thisState : thisStates) {
			final IAbstractState<?, IBoogieVar> compactedState = thisState.compact();
			vars.addAll(compactedState.getVariables());
			compactedStates.add(compactedState);
		}

		final List<IAbstractState<?, IBoogieVar>> compactedSynchronizedStates = new ArrayList<>(numberOfStates);
		for (final IAbstractState<?, IBoogieVar> compactedState : compactedStates) {
			final Set<IBoogieVar> missing = SetOperations.difference(vars, compactedState.getVariables());
			if (missing.isEmpty()) {
				compactedSynchronizedStates.add(compactedState);
			} else {
				compactedSynchronizedStates.add(compactedState.addVariables(missing));
			}
		}

		return new CompoundDomainState(mServices, domains, compactedSynchronizedStates);
	}

	private static <T extends IAbstractState<T, IBoogieVar>> T applyCasted(final IAbstractState<?, IBoogieVar> first,
			final IAbstractState<?, IBoogieVar> second, final IAbstractStateBinaryOperator<T> op) {
		final T firstT = (T) first;
		final T secondT = (T) second;
		return op.apply(firstT, secondT);
	}

}
