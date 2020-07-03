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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * A state in the {@link CompoundDomain}.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings({ "unchecked", "rawtypes" })
public class CompoundDomainState implements IAbstractState<CompoundDomainState> {

	private static int sId;

	private static final Map<Class<?>, String> mSanitizedShortNames = new HashMap<>();

	private final IUltimateServiceProvider mServices;

	private final List<IAbstractState<?>> mAbstractStates;
	private final List<IAbstractDomain> mDomainList;
	private final int mId;

	private final String[] mCachedShortNames;

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
			final List<IAbstractState<?>> abstractStateList) {
		sId++;
		mId = sId;
		if (domainList.size() != abstractStateList.size()) {
			throw new UnsupportedOperationException(
					"The domain list size and the abstract state list size must be identical.");
		}
		mServices = services;
		mDomainList = domainList;
		mAbstractStates = abstractStateList;
		mCachedShortNames = initializeShortNames();
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
		mCachedShortNames = initializeShortNames();
	}

	@Override
	public CompoundDomainState addVariable(final IProgramVarOrConst variable) {
		return performStateOperation(state -> state.addVariable(variable));
	}

	@Override
	public CompoundDomainState removeVariable(final IProgramVarOrConst variable) {
		return performStateOperation(state -> state.removeVariable(variable));
	}

	@Override
	public CompoundDomainState addVariables(final Collection<IProgramVarOrConst> variables) {
		return performStateOperation(state -> state.addVariables(variables));
	}

	@Override
	public CompoundDomainState removeVariables(final Collection<IProgramVarOrConst> variables) {
		return performStateOperation(state -> state.removeVariables(variables));
	}

	@Override
	public boolean containsVariable(final IProgramVarOrConst var) {
		return mAbstractStates.get(0).containsVariable(var);
	}

	@Override
	public Set<IProgramVarOrConst> getVariables() {
		return mAbstractStates.get(0).getVariables();
	}

	@Override
	public CompoundDomainState renameVariable(final IProgramVarOrConst oldVar, final IProgramVarOrConst newVar) {
		return performStateOperation(state -> state.renameVariable(oldVar, newVar));
	}

	@Override
	public CompoundDomainState renameVariables(final Map<IProgramVarOrConst, IProgramVarOrConst> old2newVars) {
		return performStateOperation(state -> state.renameVariables(old2newVars));
	}

	@Override
	public CompoundDomainState patch(final CompoundDomainState dominator) {
		assert mAbstractStates.size() == dominator.mAbstractStates.size();

		final List<IAbstractState<?>> returnList = new ArrayList<>();
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
		for (final IAbstractState<?> state : mAbstractStates) {
			if (state.isBottom()) {
				return true;
			}
		}
		return false;
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
		return SmtUtils.and(script,
				mAbstractStates.stream().map(state -> state.getTerm(script)).collect(Collectors.toSet()));
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (int i = 0; i < mAbstractStates.size(); i++) {
			sb.append(mCachedShortNames[i]).append(mAbstractStates.get(i).toLogString()).append(", ");
		}

		return sb.toString();
	}

	private String[] initializeShortNames() {
		final String[] shortNames = new String[mAbstractStates.size()];
		for (int i = 0; i < mAbstractStates.size(); i++) {
			shortNames[i] =
					new StringBuilder().append(getShortName(mAbstractStates.get(i).getClass())).append(": ").toString();
		}
		return shortNames;
	}

	private static String getShortName(final Class<?> clazz) {
		if (mSanitizedShortNames.containsKey(clazz)) {
			return mSanitizedShortNames.get(clazz);
		}

		String s = clazz.getSimpleName();
		if (s.length() >= 4) {
			s = s.substring(0, 3);
		}

		mSanitizedShortNames.put(clazz, s);
		return s;
	}

	private CompoundDomainState performStateOperation(final Function<IAbstractState<?>, IAbstractState<?>> state) {
		return new CompoundDomainState(mServices, mDomainList,
				mAbstractStates.stream().map(state).collect(Collectors.toList()));
	}

	protected List<IAbstractDomain> getDomainList() {
		return mDomainList;
	}

	protected List<IAbstractState<?>> getAbstractStatesList() {
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

	private static SubsetResult isStrictSubsetOf(final SubsetResult current, final IAbstractState<?> aState,
			final IAbstractState<?> bState) {
		final SubsetResult result = isSubsetOfInternally(aState, bState);
		return current.min(result);
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public CompoundDomainState intersect(final CompoundDomainState other) {
		final List<IAbstractState<?>> thisStates = getAbstractStatesList();
		final List<IAbstractState<?>> otherStates = other.getAbstractStatesList();
		final List<IAbstractDomain> domains = getDomainList();

		assert thisStates.size() == otherStates.size();
		assert domains.size() == other.getDomainList().size();
		assert domains.size() == thisStates.size();

		final List<IAbstractState<?>> returnStates = new ArrayList<>();

		for (int i = 0; i < thisStates.size(); i++) {
			final IAbstractState<?> thisState = thisStates.get(i);
			final IAbstractState<?> otherState = otherStates.get(i);
			returnStates.add(applyCasted(thisState, otherState, (a, b) -> a.intersect(b)));
		}

		return new CompoundDomainState(mServices, domains, returnStates);
	}

	@Override
	public CompoundDomainState union(final CompoundDomainState other) {
		final List<IAbstractState<?>> thisStates = getAbstractStatesList();
		final List<IAbstractState<?>> otherStates = other.getAbstractStatesList();
		final List<IAbstractDomain> domains = getDomainList();

		assert thisStates.size() == otherStates.size();
		assert domains.size() == other.getDomainList().size();
		assert domains.size() == thisStates.size();

		final List<IAbstractState<?>> returnStates = new ArrayList<>();

		for (int i = 0; i < thisStates.size(); i++) {
			final IAbstractState<?> thisState = thisStates.get(i);
			final IAbstractState<?> otherState = otherStates.get(i);
			returnStates.add(applyCasted(thisState, otherState, (a, b) -> a.union(b)));
		}

		return new CompoundDomainState(mServices, domains, returnStates);
	}

	@Override
	public CompoundDomainState compact() {

		final List<IAbstractState<?>> thisStates = getAbstractStatesList();
		final int numberOfStates = thisStates.size();
		final List<IAbstractDomain> domains = getDomainList();

		assert domains.size() == thisStates.size();

		final List<IAbstractState<?>> compactedStates = new ArrayList<>(numberOfStates);
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		for (final IAbstractState<?> thisState : thisStates) {
			final IAbstractState<?> compactedState = thisState.compact();
			vars.addAll(compactedState.getVariables());
			compactedStates.add(compactedState);
		}

		final List<IAbstractState<?>> compactedSynchronizedStates = new ArrayList<>(numberOfStates);
		for (final IAbstractState<?> compactedState : compactedStates) {
			final Set<IProgramVarOrConst> missing = DataStructureUtils.difference(vars, compactedState.getVariables());
			if (missing.isEmpty()) {
				compactedSynchronizedStates.add(compactedState);
			} else {
				compactedSynchronizedStates.add(compactedState.addVariables(missing));
			}
		}

		return new CompoundDomainState(mServices, domains, compactedSynchronizedStates);
	}

	private static <T extends IAbstractState<T>> T applyCasted(final IAbstractState<?> first,
			final IAbstractState<?> second, final IAbstractStateBinaryOperator<T> op) {
		final T firstT = (T) first;
		final T secondT = (T) second;
		return op.apply(firstT, secondT);
	}

}
