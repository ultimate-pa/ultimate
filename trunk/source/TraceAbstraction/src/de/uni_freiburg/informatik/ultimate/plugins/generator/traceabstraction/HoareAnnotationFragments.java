package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.HashRelation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

/**
 * Store and maintain fragments of a Hoare Annotation derived during abstraction
 * refinement.
 * If we would neither remove dead ends nor minimize the abstraction this would
 * not be necessary and we could extract the complete Hoare annotation direcly
 * form the final abstraction.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationFragments {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	/**
	 * States for contexts were the context was already removed (because it was
	 * a dead end) from the abstraction.
	 */
	private final Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> m_DeadContexts2ProgPoint2Preds = 
			new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
	/**
	 * States for contexts were the are still in the current abstraction.
	 */
	private Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> m_LiveContexts2ProgPoint2Preds = 
			new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
	private final HashMap<IPredicate, IPredicate> m_Context2Entry = 
			new HashMap<IPredicate, IPredicate>();
	
	private final HashRelation<ProgramPoint, IPredicate> m_ProgPoint2StatesWithEmptyContext = 
			new HashRelation<ProgramPoint, IPredicate>();
	
	/**
	 * What is the precondition for a context?
	 * Strongest postcondition or entry given by automaton?
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
	

	
	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary
	 * because the current abstraction was updated by an intersection.
	 */
	public void updateOnIntersection(
			Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> fst2snd2res, 
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
			Update update = new IntersectionUpdate(fst2snd2res);
			update(update,abstraction);
	}
	
	/**
	 * Perform an update of these HoareAnnotationFragments that became necessary
	 * because the current abstraction was updated by a minimization.
	 */
	public void updateOnMinimization(
			Map<IPredicate, IPredicate> old2New, 
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
			Update update = new MinimizationUpdate(old2New);
			update(update,abstraction);
	}
	
	
	
	/**
	 * Perform an update the HoareAnnotationFragments that became necessary 
	 * because the abstraction was updated by an automaton operation.
	 * 
	 * WARNING: At the moment we update only the contexts and the context2enry 
	 * mapping, because we expect the our HoareAnnotationFragments stores double
	 * deckers that have been removed by a dead end removal.
	 */
	private void update(
			Update update, 
			INestedWordAutomatonSimple<CodeBlock, IPredicate> newAbstraction) {
		Map<IPredicate, HashRelation<ProgramPoint, IPredicate>> oldLiveContexts2ProgPoint2Preds = 
				m_LiveContexts2ProgPoint2Preds;
		m_LiveContexts2ProgPoint2Preds = 
				new HashMap<IPredicate, HashRelation<ProgramPoint, IPredicate>>();
		for (Entry<IPredicate, HashRelation<ProgramPoint, IPredicate>> contextHrPair : oldLiveContexts2ProgPoint2Preds.entrySet()) {
			IPredicate oldContext = contextHrPair.getKey();
			List<IPredicate> newContexts = update.getNewPredicates(oldContext);
			if (newContexts == null) {
				assert !m_DeadContexts2ProgPoint2Preds.containsKey(oldContext);
				m_DeadContexts2ProgPoint2Preds.put(oldContext, contextHrPair.getValue());
			} else {
				IPredicate oldEntry = m_Context2Entry.get(oldContext);
				m_Context2Entry.remove(oldContext);
				for (int i=0; i<newContexts.size(); i++) {
					final HashRelation<ProgramPoint, IPredicate> hr;
					if (i== newContexts.size()-1) {
						// last iteration, we can use the original hr instead of copy
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
	 * Get the unique call successor of a state newContext.
	 * Return null if there is no call successor.
	 * Throw exception if call successor is not unique.
	 */
	private IPredicate getEntry(
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction,
			IPredicate newContext) {
		Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it = 
				abstraction.callSuccessors(newContext).iterator();
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
	 * operations.
	 * Returns all predicates of the new abstraction that replace a state of
	 * the old abstraction.
	 * 
	 * WARNING: This does not provide any information about double deckers.
	 * This information is only sufficient if we store the removed double 
	 * deckers. 
	 */
	interface Update {
		List<IPredicate> getNewPredicates(IPredicate oldPredicate);
	}
	
	private class IntersectionUpdate implements Update {

		private final Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> m_Fst2snd2res;
		
		public IntersectionUpdate(
				Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> fst2snd2res) {
			m_Fst2snd2res = fst2snd2res;
		}

		@Override
		public List<IPredicate> getNewPredicates(IPredicate oldPredicate) {
			Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState> mapping = m_Fst2snd2res.get(oldPredicate);
			if (mapping == null) {
				return null;
			} else {
				List<IPredicate> result = new ArrayList<IPredicate>();
				for (Entry<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState> entry  : mapping.entrySet()) {
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
		ProgramPoint pp = ((SPredicate) up).getProgramPoint();
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
	
	
	
	void addContextEntryPair(IPredicate context, IPredicate entry) {
		m_Context2Entry.put(context, entry);
	}
	
	
	/**
	 * Add all DoubleDeckers dd for which holds.
	 * - dd was in the automaton directly after the automaton operation op
	 * - after dead ends where removed from op dd was no double decker of the
	 * automaton any more.
	 */
	public void addDeadEndDoubleDeckers(
			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> op) throws OperationCanceledException {
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
