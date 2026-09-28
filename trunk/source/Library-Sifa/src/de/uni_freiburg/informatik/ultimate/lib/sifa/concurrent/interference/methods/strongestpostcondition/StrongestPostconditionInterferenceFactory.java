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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedEdgeInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterference.RelationalInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public final class StrongestPostconditionInterferenceFactory
		extends GroupedInterferenceFactory<Map<GroupedInterference.Key, GroupedInterference<RelationalInterference>>> {

	public StrongestPostconditionInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> sourcesBeforeForkByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				sourcesBeforeForkByThread);
	}

	@Override
	protected boolean requiresChangedGlobals() {
		return false;
	}

	@Override
	public Map<GroupedInterference.Key, GroupedInterference<RelationalInterference>> createInterferenceGroups() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void addEdgeInterference(
			final Map<GroupedInterference.Key, GroupedInterference<RelationalInterference>> groupedInterferences,
			final TranslatedEdgeInterference edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate relationalInterference = relationalInterferenceOf(edge, threadStates);
		if (relationalInterference == null || InterferenceUtils.isNullOrFalse(relationalInterference)) {
			return;
		}
		final RelationalInterference interference = new RelationalInterference(relationalInterference,
				mPostcondition.prepareRelation(relationalInterference),
				unconditionalPostStateOf(relationalInterference));
		final GroupedInterference<RelationalInterference> group =
				new GroupedInterference<>(contextFor(edge), Set.of(edge.source()), interference);
		groupedInterferences.merge(group.key(), group, this::mergeInterference);
	}

	@Override
	public IInterferenceSet buildInterferenceSet(
			final Map<GroupedInterference.Key, GroupedInterference<RelationalInterference>> groupedInterferences) {
		return groupedInterferences.isEmpty() ? null
				: new StrongestPostconditionInterference(groupedInterferences.values(), mSourcesBeforeForkByThread,
						mPostcondition);
	}

	private GroupedInterference<RelationalInterference> mergeInterference(
			final GroupedInterference<RelationalInterference> left,
			final GroupedInterference<RelationalInterference> right) {
		final RelationalInterference leftInterference = left.mergedInterference();
		final RelationalInterference rightInterference = right.mergedInterference();
		final IPredicate mergedRelation =
				disjoin(leftInterference.relationalInterference(), rightInterference.relationalInterference());
		final IPredicate mergedPostState =
				disjoin(leftInterference.unconditionalPostState(), rightInterference.unconditionalPostState());
		return left.withMergedInterference(new RelationalInterference(mergedRelation,
				mPostcondition.prepareRelation(mergedRelation), mergedPostState));
	}
}
