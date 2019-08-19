/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.UnknownState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Store and maintain fragments of a Hoare Annotation derived during abstraction refinement. If we would neither remove
 * dead ends nor minimize the abstraction this would not be necessary and we could extract the complete Hoare annotation
 * direcly form the final abstraction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationFragments<LETTER extends IAction> {

	private final ILogger mLogger;

	/**
	 * States for contexts were the context was already removed (because it was a dead end) from the abstraction.
	 */
	private final Map<IPredicate, HashRelation<IcfgLocation, IPredicate>> mDeadContexts2ProgPoint2Preds =
			new HashMap<>();
	/**
	 * States for contexts were the are still in the current abstraction.
	 */
	private Map<IPredicate, HashRelation<IcfgLocation, IPredicate>> mLiveContexts2ProgPoint2Preds = new HashMap<>();
	private final HashMap<IPredicate, IPredicate> mContext2Entry = new HashMap<>();

	private final HashRelation<IcfgLocation, IPredicate> mProgPoint2StatesWithEmptyContext = new HashRelation<>();

	private final Set<? extends IcfgLocation> mHoareAnnotationPositions;

	private final HoareAnnotationPositions mHoareAnnotationPos;

	Map<IPredicate, HashRelation<IcfgLocation, IPredicate>> getDeadContexts2ProgPoint2Preds() {
		return mDeadContexts2ProgPoint2Preds;
	}

	Map<IPredicate, HashRelation<IcfgLocation, IPredicate>> getLiveContexts2ProgPoint2Preds() {
		return mLiveContexts2ProgPoint2Preds;
	}

	HashRelation<IcfgLocation, IPredicate> getProgPoint2StatesWithEmptyContext() {
		return mProgPoint2StatesWithEmptyContext;
	}

	HashMap<IPredicate, IPredicate> getCallpred2Entry() {
		return mContext2Entry;
	}

	public HoareAnnotationFragments(final ILogger logger, final Set<? extends IcfgLocation> hoareAnnotationLocations,
			final HoareAnnotationPositions hoareAnnotationPos) {
		mLogger = logger;
		mHoareAnnotationPositions = hoareAnnotationLocations;
		mHoareAnnotationPos = hoareAnnotationPos;
	}

	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary because the current abstraction was
	 * updated by an intersection.
	 */
	public void updateOnIntersection(
			final Map<IPredicate, Map<IPredicate, IntersectNwa<LETTER, IPredicate>.ProductState>> fst2snd2res,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction) {
		final IUpdate update = new IntersectionUpdate(fst2snd2res);
		update(update, abstraction);
	}

	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary because the current abstraction was
	 * updated by a minimization.
	 */
	public void updateOnMinimization(final Map<IPredicate, IPredicate> old2New,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction) {
		final IUpdate update = new MinimizationUpdate(old2New);
		update(update, abstraction);
	}

	/**
	 * Perform an update the HoareAnnotationFragments that became necessary because the abstraction was updated by an
	 * automaton operation.
	 * 
	 * WARNING: At the moment we update only the contexts and the context2enry mapping, because we expect the our
	 * HoareAnnotationFragments stores double deckers that have been removed by a dead end removal.
	 */
	private void update(final IUpdate update, final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> newAbstraction) {
		final Map<IPredicate, HashRelation<IcfgLocation, IPredicate>> oldLiveContexts2ProgPoint2Preds =
				mLiveContexts2ProgPoint2Preds;
		mLiveContexts2ProgPoint2Preds = new HashMap<>();
		for (final Entry<IPredicate, HashRelation<IcfgLocation, IPredicate>> contextHrPair : oldLiveContexts2ProgPoint2Preds
				.entrySet()) {
			final IPredicate oldContext = contextHrPair.getKey();
			final List<IPredicate> newContexts = update.getNewPredicates(oldContext);
			if (newContexts == null) {
				assert !mDeadContexts2ProgPoint2Preds.containsKey(oldContext);
				mDeadContexts2ProgPoint2Preds.put(oldContext, contextHrPair.getValue());
			} else {
				final IPredicate oldEntry = mContext2Entry.get(oldContext);
				mContext2Entry.remove(oldContext);
				for (int i = 0; i < newContexts.size(); i++) {
					final HashRelation<IcfgLocation, IPredicate> hr;
					if (i == newContexts.size() - 1) {
						// last iteration, we can use the original hr instead of
						// copy
						hr = contextHrPair.getValue();
					} else {
						hr = new HashRelation<>();
						hr.addAll(contextHrPair.getValue());
					}
					mLiveContexts2ProgPoint2Preds.put(newContexts.get(i), hr);
					final IPredicate entry = getEntry(newAbstraction, newContexts.get(i));
					if (entry == null) {
						mContext2Entry.put(newContexts.get(i), oldEntry);
					} else {
						mContext2Entry.put(newContexts.get(i), entry);
					}
				}
			}
		}
	}

	/**
	 * Get the unique call successor of a state newContext. Return null if there is no call successor. Throw exception
	 * if call successor is not unique.
	 */
	private IPredicate getEntry(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final IPredicate newContext) {
		final Iterator<OutgoingCallTransition<LETTER, IPredicate>> it =
				abstraction.callSuccessors(newContext).iterator();
		if (!it.hasNext()) {
			return null;
		}
		final OutgoingCallTransition<LETTER, IPredicate> outCall = it.next();
		final IPredicate newEntry = outCall.getSucc();
		if (it.hasNext()) {
			throw new UnsupportedOperationException(
					"Unable to compute Hoare annotation if state has several outgoging calls");
		}
		return newEntry;
	}

	/**
	 * Encapsulates information for updates of the abstraction by automaton operations. Returns all predicates of the
	 * new abstraction that replace a state of the old abstraction.
	 * 
	 * WARNING: This does not provide any information about double deckers. This information is only sufficient if we
	 * store the removed double deckers.
	 */
	@FunctionalInterface
	interface IUpdate {
		List<IPredicate> getNewPredicates(IPredicate oldPredicate);
	}

	private class IntersectionUpdate implements IUpdate {

		private final Map<IPredicate, Map<IPredicate, IntersectNwa<LETTER, IPredicate>.ProductState>> mFst2snd2res;

		public IntersectionUpdate(
				final Map<IPredicate, Map<IPredicate, IntersectNwa<LETTER, IPredicate>.ProductState>> fst2snd2res) {
			mFst2snd2res = fst2snd2res;
		}

		@Override
		public List<IPredicate> getNewPredicates(final IPredicate oldPredicate) {
			final Map<IPredicate, IntersectNwa<LETTER, IPredicate>.ProductState> mapping =
					mFst2snd2res.get(oldPredicate);
			if (mapping == null) {
				return null;
			}
			final List<IPredicate> result = new ArrayList<>();
			for (final Entry<IPredicate, IntersectNwa<LETTER, IPredicate>.ProductState> entry : mapping.entrySet()) {
				result.add(entry.getValue().getRes());
			}
			return result;
		}
	}

	private static class MinimizationUpdate implements IUpdate {

		private final Map<IPredicate, IPredicate> mOld2New;

		public MinimizationUpdate(final Map<IPredicate, IPredicate> old2New) {
			super();
			mOld2New = old2New;
		}

		@Override
		public List<IPredicate> getNewPredicates(final IPredicate oldPredicate) {
			final IPredicate newPredicate = mOld2New.get(oldPredicate);
			if (newPredicate == null) {
				return null;
			}
			final List<IPredicate> result = Collections.singletonList(newPredicate);
			return result;
		}
	}

	void addDoubleDecker(final IPredicate down, final IPredicate up, final IPredicate emtpy) {
		final IcfgLocation pp = getProgramPoint(up);
		if (mHoareAnnotationPos == HoareAnnotationPositions.LoopsAndPotentialCycles
				&& !mHoareAnnotationPositions.contains(pp)) {
			// do not compute Hoare annotation for this program point
			return;
		}
		if (down == emtpy) {
			mProgPoint2StatesWithEmptyContext.addPair(pp, up);
		} else {
			HashRelation<IcfgLocation, IPredicate> pp2preds = mLiveContexts2ProgPoint2Preds.get(down);
			if (pp2preds == null) {
				pp2preds = new HashRelation<>();
				mLiveContexts2ProgPoint2Preds.put(down, pp2preds);
			}
			pp2preds.addPair(pp, up);
		}
	}

	private IcfgLocation getProgramPoint(final IPredicate pred) {
		final IcfgLocation pp;
		if (pred instanceof SPredicate) {
			pp = ((SPredicate) pred).getProgramPoint();
		} else if (pred instanceof UnknownState) {
			pp = ((UnknownState) pred).getProgramPoint();
		} else {
			throw new AssertionError("predicate does not offer program point");
		}
		return pp;
	}

	void addContextEntryPair(final IPredicate context, final IPredicate entry) {
		mContext2Entry.put(context, entry);
	}

	/**
	 * Add all DoubleDeckers dd for which holds. - dd was in the automaton directly after the automaton operation op -
	 * after dead ends where removed from op dd was no double decker of the automaton any more.
	 */
	public void addDeadEndDoubleDeckers(final IOpWithDelayedDeadEndRemoval<LETTER, IPredicate> op)
			throws AutomataOperationCanceledException {
		final IPredicate emtpyStack = op.getResult().getEmptyStackState();
		for (final UpDownEntry<IPredicate> upDownEntry : op.getRemovedUpDownEntry()) {
			addDoubleDecker(upDownEntry.getDown(), upDownEntry.getUp(), emtpyStack);
			if (upDownEntry.getEntry() != null) {
				addContextEntryPair(upDownEntry.getDown(), upDownEntry.getEntry());
			} else {
				assert upDownEntry.getDown() == emtpyStack;
			}

		}
	}

}
