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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.UnknownState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;

/**
 * Store and maintain fragments of a Hoare Annotation derived during abstraction
 * refinement. If we would neither remove dead ends nor minimize the abstraction
 * this would not be necessary and we could extract the complete Hoare
 * annotation direcly form the final abstraction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationFragments {

	private final ILogger mLogger;

	/**
	 * States for contexts were the context was already removed (because it was
	 * a dead end) from the abstraction.
	 */
	private final Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> m_DeadContexts2ProgPoint2Preds = new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
	/**
	 * States for contexts were the are still in the current abstraction.
	 */
	private Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> m_LiveContexts2ProgPoint2Preds = new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
	private final HashMap<IPredicate, IPredicate> m_Context2Entry = new HashMap<IPredicate, IPredicate>();

	private final HashRelation<ProgramPoint, IPredicate> m_ProgPoint2StatesWithEmptyContext = new HashRelation<ProgramPoint, IPredicate>();

	private final HashSet<ProgramPoint> m_HoareAnnotationPositions;

	private final HoareAnnotationPositions m_HoareAnnotationPos;

	/**
	 * What is the precondition for a context? Strongest postcondition or entry
	 * given by automaton?
	 */
	private final static boolean m_UseEntry = true;

	Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> getDeadContexts2ProgPoint2Preds() {
		return m_DeadContexts2ProgPoint2Preds;
	}

	Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> getLiveContexts2ProgPoint2Preds() {
		return m_LiveContexts2ProgPoint2Preds;
	}

	HashRelation<ProgramPoint, IPredicate> getProgPoint2StatesWithEmptyContext() {
		return m_ProgPoint2StatesWithEmptyContext;
	}

	HashMap<IPredicate, IPredicate> getContext2Entry() {
		return m_Context2Entry;
	}

	public HoareAnnotationFragments(ILogger logger, HashSet<ProgramPoint> hoareAnnotationPositions, 
			HoareAnnotationPositions hoareAnnotationPos){
		mLogger = logger;
		m_HoareAnnotationPositions = hoareAnnotationPositions;
		m_HoareAnnotationPos = hoareAnnotationPos;
	}
	
	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary
	 * because the current abstraction was updated by an intersection.
	 */
	public void updateOnIntersection(
			Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock, IPredicate>.ProductState>> fst2snd2res,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		Update update = new IntersectionUpdate(fst2snd2res);
		update(update, abstraction);
	}

	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary
	 * because the current abstraction was updated by a minimization.
	 */
	public void updateOnMinimization(Map<IPredicate, IPredicate> old2New,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		Update update = new MinimizationUpdate(old2New);
		update(update, abstraction);
	}

	/**
	 * Perform an update the HoareAnnotationFragments that became necessary
	 * because the abstraction was updated by an automaton operation.
	 * 
	 * WARNING: At the moment we update only the contexts and the context2enry
	 * mapping, because we expect the our HoareAnnotationFragments stores double
	 * deckers that have been removed by a dead end removal.
	 */
	private void update(Update update, INestedWordAutomatonSimple<CodeBlock, IPredicate> newAbstraction) {
		Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> oldLiveContexts2ProgPoint2Preds = m_LiveContexts2ProgPoint2Preds;
		m_LiveContexts2ProgPoint2Preds = new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
		for (Entry<IPredicate, HashRelation<ProgramPoint, IPredicate>> contextHrPair : oldLiveContexts2ProgPoint2Preds
				.entrySet()) {
			IPredicate oldContext = contextHrPair.getKey();
			List<IPredicate> newContexts = update.getNewPredicates(oldContext);
			if (newContexts == null) {
				assert !m_DeadContexts2ProgPoint2Preds.containsKey(oldContext);
				m_DeadContexts2ProgPoint2Preds.put(oldContext, contextHrPair.getValue());
			} else {
				IPredicate oldEntry = m_Context2Entry.get(oldContext);
				m_Context2Entry.remove(oldContext);
				for (int i = 0; i < newContexts.size(); i++) {
					final HashRelation<ProgramPoint, IPredicate> hr;
					if (i == newContexts.size() - 1) {
						// last iteration, we can use the original hr instead of
						// copy
						hr = contextHrPair.getValue();
					} else {
						hr = new HashRelation<ProgramPoint, IPredicate>();
						hr.addAll(contextHrPair.getValue());
					}
					m_LiveContexts2ProgPoint2Preds.put(newContexts.get(i), hr);
					IPredicate entry = getEntry(newAbstraction, newContexts.get(i));
					if (entry == null) {
						m_Context2Entry.put(newContexts.get(i), oldEntry);
					} else {
						m_Context2Entry.put(newContexts.get(i), entry);
					}
				}
			}
		}
	}

	/**
	 * Get the unique call successor of a state newContext. Return null if there
	 * is no call successor. Throw exception if call successor is not unique.
	 */
	private IPredicate getEntry(INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction, IPredicate newContext) {
		Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it = abstraction.callSuccessors(newContext).iterator();
		if (!it.hasNext()) {
			return null;
		} else {
			OutgoingCallTransition<CodeBlock, IPredicate> outCall = it.next();
			IPredicate newEntry = outCall.getSucc();
			if (it.hasNext()) {
				throw new UnsupportedOperationException(
						"Unable to compute Hoare annotation if state has several outgoging calls");
			}
			return newEntry;
		}
	}

	/**
	 * Encapsulates information for updates of the abstraction by automaton
	 * operations. Returns all predicates of the new abstraction that replace a
	 * state of the old abstraction.
	 * 
	 * WARNING: This does not provide any information about double deckers. This
	 * information is only sufficient if we store the removed double deckers.
	 */
	interface Update {
		List<IPredicate> getNewPredicates(IPredicate oldPredicate);
	}

	private class IntersectionUpdate implements Update {

		private final Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock, IPredicate>.ProductState>> m_Fst2snd2res;

		public IntersectionUpdate(
				Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock, IPredicate>.ProductState>> fst2snd2res) {
			m_Fst2snd2res = fst2snd2res;
		}

		@Override
		public List<IPredicate> getNewPredicates(IPredicate oldPredicate) {
			Map<IPredicate, IntersectNwa<CodeBlock, IPredicate>.ProductState> mapping = m_Fst2snd2res.get(oldPredicate);
			if (mapping == null) {
				return null;
			} else {
				List<IPredicate> result = new ArrayList<IPredicate>();
				for (Entry<IPredicate, IntersectNwa<CodeBlock, IPredicate>.ProductState> entry : mapping.entrySet()) {
					result.add(entry.getValue().getRes());
				}
				return result;
			}
		}
	}

	private class MinimizationUpdate implements Update {

		private final Map<IPredicate, IPredicate> m_Old2New;

		public MinimizationUpdate(Map<IPredicate, IPredicate> old2New) {
			super();
			m_Old2New = old2New;
		}

		@Override
		public List<IPredicate> getNewPredicates(IPredicate oldPredicate) {
			IPredicate newPredicate = m_Old2New.get(oldPredicate);
			if (newPredicate == null) {
				return null;
			} else {
				List<IPredicate> result = Collections.singletonList(newPredicate);
				return result;
			}
		}
	}

	void addDoubleDecker(IPredicate down, IPredicate up, IPredicate emtpy) {
		ProgramPoint pp = getProgramPoint(up);
		if (m_HoareAnnotationPos == HoareAnnotationPositions.LoopsAndPotentialCycles && 
				!m_HoareAnnotationPositions.contains(pp)) {
			// do not compute Hoare annotation for this program point
			return;
		}
		if (down == emtpy) {
			m_ProgPoint2StatesWithEmptyContext.addPair(pp, up);
		} else {
			HashRelation<ProgramPoint, IPredicate> pp2preds = m_LiveContexts2ProgPoint2Preds.get(down);
			if (pp2preds == null) {
				pp2preds = new HashRelation<ProgramPoint, IPredicate>();
				m_LiveContexts2ProgPoint2Preds.put(down, pp2preds);
			}
			pp2preds.addPair(pp, up);
		}
	}
	
	private ProgramPoint getProgramPoint(IPredicate pred) {
		final ProgramPoint pp;
		if (pred instanceof SPredicate) {
			pp = ((SPredicate) pred).getProgramPoint();
		} else if (pred instanceof UnknownState) {
			pp = ((UnknownState) pred).getProgramPoint();
		} else {
			throw new AssertionError("predicate does not offer program point");
		}
		return pp;
	}

	void addContextEntryPair(IPredicate context, IPredicate entry) {
		m_Context2Entry.put(context, entry);
	}

	/**
	 * Add all DoubleDeckers dd for which holds. - dd was in the automaton
	 * directly after the automaton operation op - after dead ends where removed
	 * from op dd was no double decker of the automaton any more.
	 */
	public void addDeadEndDoubleDeckers(IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> op)
			throws AutomataOperationCanceledException {
		IPredicate emtpyStack = op.getResult().getEmptyStackState();
		for (UpDownEntry<IPredicate> upDownEntry : op.getRemovedUpDownEntry()) {
			addDoubleDecker(upDownEntry.getDown(), upDownEntry.getUp(), emtpyStack);
			if (upDownEntry.getEntry() != null) {
				addContextEntryPair(upDownEntry.getDown(), upDownEntry.getEntry());
			} else {
				assert upDownEntry.getDown() == emtpyStack;
			}

		}
	}

}
