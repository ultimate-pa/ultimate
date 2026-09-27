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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class GroupedInterferenceFactory<G> {

	protected final InterferenceEdgeCollector mEdgeCollector;
	protected final TransFormulaToInterferencePredicate mTranslator;
	protected final RelationalPredicatePostcondition mPostcondition;
	protected final ManagedScript mManagedScript;
	protected final BasicPredicateFactory mPredicateFactory;
	protected final MustLocksetAnalysis mLocksetInfo;
	protected final Map<String, Set<IcfgLocation>> mSourcesBeforeForkByThread;
	protected final IPredicate mTruePredicate;
	protected final IPredicate mFalsePredicate;

	protected GroupedInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> sourcesBeforeForkByThread) {
		mEdgeCollector = edgeCollector;
		mTranslator = translator;
		mPostcondition = postcondition;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mLocksetInfo = locksetInfo;
		mSourcesBeforeForkByThread = Map.copyOf(sourcesBeforeForkByThread);
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	public final void addThreadInterferences(final G groupedInterferences, final String threadId,
			final Map<IcfgLocation, IPredicate> threadStates) {
		for (final TranslatedEdgeInterference edge : mEdgeCollector.collect(threadStates)) {
			if (!threadId.equals(edge.source().getProcedure())
					|| requiresChangedGlobals() && edge.changedGlobals().isEmpty()) {
				continue;
			}
			addEdgeInterference(groupedInterferences, edge, threadStates);
		}
	}

	protected boolean requiresChangedGlobals() {
		return true;
	}

	public abstract G createInterferenceGroups();

	protected abstract void addEdgeInterference(G groupedInterferences, TranslatedEdgeInterference edge,
			Map<IcfgLocation, IPredicate> threadStates);

	public abstract IInterferenceSet buildInterferenceSet(G groupedInterferences);

	protected final InterferenceContext contextFor(final TranslatedEdgeInterference edge) {
		return new InterferenceContext(edge.source().getProcedure(), edge.abstractLocationPair(),
				mustHeldLocksAroundEdge(edge), edge.forkedThreadId());
	}

	protected final Set<String> mustHeldLocksAroundEdge(final TranslatedEdgeInterference edge) {
		final Set<String> sourceLockset = mLocksetInfo.mustLocksetAt(edge.source());
		final Set<String> targetLockset = mLocksetInfo.mustLocksetAt(edge.target());
		if (sourceLockset.isEmpty()) {
			return targetLockset;
		}
		if (targetLockset.isEmpty()) {
			return sourceLockset;
		}
		final Set<String> union = new LinkedHashSet<>(sourceLockset);
		union.addAll(targetLockset);
		return Set.copyOf(union);
	}

	protected final IPredicate relationalInterferenceOf(final TranslatedEdgeInterference edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null) {
			return null;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		return conjoin(sharedPreState, edge.transitionPredicate());
	}

	protected final IPredicate unconditionalPostStateOf(final IPredicate relationalInterference) {
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}

	protected final IPredicate conjoin(final IPredicate left, final IPredicate right) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(), left.getFormula(),
				right.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	protected final IPredicate disjoin(final IPredicate left, final IPredicate right) {
		return mPredicateFactory
				.newPredicate(SmtUtils.or(mManagedScript.getScript(), left.getFormula(), right.getFormula()));
	}
}
