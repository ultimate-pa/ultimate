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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedEdgeInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class PostStateInterferenceFactory
		extends GroupedInterferenceFactory<Map<InterferenceContext, GroupedInterference<IPredicate>>> {

	private final IDomain mDomain;

	public PostStateInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> sourcesBeforeForkByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				sourcesBeforeForkByThread);
		mDomain = domain;
	}

	@Override
	public Map<InterferenceContext, GroupedInterference<IPredicate>> createInterferenceGroups() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void addEdgeInterference(
			final Map<InterferenceContext, GroupedInterference<IPredicate>> groupedInterferences,
			final TranslatedEdgeInterference edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate targetState = threadStates.get(edge.target());
		final IPredicate postState = targetState == null ? computeEdgeLocalPostState(edge, threadStates)
				: mTranslator.projectPreStateToSharedState(targetState);
		if (InterferenceUtils.isNullOrFalse(postState)) {
			return;
		}
		final InterferenceContext context = contextFor(edge);
		final GroupedInterference<IPredicate> previous = groupedInterferences.get(context);
		final IPredicate mergedPostState =
				previous == null ? postState : mDomain.join(previous.mergedInterference(), postState);
		final Set<IcfgLocation> sourceLocations = new LinkedHashSet<>();
		if (previous != null) {
			sourceLocations.addAll(previous.sourceLocations());
		}
		sourceLocations.add(edge.source());
		groupedInterferences.put(context, new GroupedInterference<>(context, sourceLocations, mergedPostState));
	}

	@Override
	public IInterferenceSet
			buildInterferenceSet(final Map<InterferenceContext, GroupedInterference<IPredicate>> groupedInterferences) {
		return groupedInterferences.isEmpty() ? null
				: new PostStateInterference(groupedInterferences.values(), mSourcesBeforeForkByThread);
	}

	private IPredicate computeEdgeLocalPostState(final TranslatedEdgeInterference edge,
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
