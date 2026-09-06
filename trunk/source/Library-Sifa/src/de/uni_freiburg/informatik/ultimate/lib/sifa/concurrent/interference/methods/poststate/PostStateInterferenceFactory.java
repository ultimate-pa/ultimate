/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class PostStateInterferenceFactory
		extends GroupedInterferenceFactory<Map<PostStateInterferenceFactory.GroupKey, PostStateInterferenceFactory.Group>> {

	record GroupKey(String threadId, AbstractLocationPair abstractLocations, Set<String> lockset,
			String forkedThreadId) {
	}

	static final class Group {
		private IPredicate mPostState;
		private final Set<IcfgLocation> mSources = new LinkedHashSet<>();
	}

	private final IDomain mDomain;

	public PostStateInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				preForkSourcesByThread);
		mDomain = domain;
	}

	@Override
	protected Map<GroupKey, Group> createAccumulator() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void accumulateEdgeSummary(final Map<GroupKey, Group> accumulator,
			final TranslatedInterferenceOfEdge edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate targetState = threadStates.get(edge.target());
		final IPredicate postState = targetState == null ? computeEdgeLocalPostState(edge, threadStates)
				: mTranslator.projectPreStateToSharedState(targetState);
		if (InterferenceUtils.shouldSkipTrivialPredicate(postState)) {
			return;
		}
		final GroupKey key = new GroupKey(edge.source().getProcedure(), edge.abstractLocationPair(),
				mustHeldLocksAroundEdge(edge), edge.forkedThreadId());
		final Group group = accumulator.computeIfAbsent(key, ignored -> new Group());
		group.mPostState = group.mPostState == null ? postState : mDomain.join(group.mPostState, postState);
		group.mSources.add(edge.source());
	}

	@Override
	protected IInterferenceSet buildInterferenceSet(final Map<GroupKey, Group> accumulator) {
		if (accumulator.isEmpty()) {
			return null;
		}
		final Map<InterferenceGroupKey, IPredicate> summaryByKey = new LinkedHashMap<>();
		for (final var entry : accumulator.entrySet()) {
			final GroupKey key = entry.getKey();
			summaryByKey.put(new InterferenceGroupKey(key.threadId(), key.abstractLocations(), key.lockset(),
					key.forkedThreadId(), entry.getValue().mSources), entry.getValue().mPostState);
		}
		return new PostStateInterference(summaryByKey, mPreForkSourcesByThread);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate relationalInterference = relationalInterferenceOf(edge, threadStates);
		if (relationalInterference == null) {
			return mFalsePredicate;
		}
		if (SmtUtils.isTrueLiteral(relationalInterference.getFormula())
				|| SmtUtils.isFalseLiteral(relationalInterference.getFormula())) {
			return relationalInterference;
		}
		return unconditionalPostStateOf(relationalInterference);
	}
}
