package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class HoareAnnotationFragments2 extends HoareAnnotationFragments {

	public HoareAnnotationFragments2(RootAnnot rootAnnot, SmtManager smtManager, boolean useEntry) {
		super(rootAnnot, smtManager, useEntry);
	}
	
	public void updateOnIntersection(
			Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> fst2snd2res, 
			IDoubleDeckerAutomaton<CodeBlock, IPredicate> abstraction) {
			Update update = new IntersectionUpdate(fst2snd2res);
			update(update,abstraction);
	}
	
	
	public void updateOnMinimization(
			Map<IPredicate, IPredicate> old2New, 
			IDoubleDeckerAutomaton<CodeBlock, IPredicate> abstraction) {
			Update update = new MinimizationUpdate(old2New);
			update(update,abstraction);
	}
	
	private void update(
			Update update, 
			IDoubleDeckerAutomaton<CodeBlock, IPredicate> abstraction) {
		Map<ProgramPoint, Map<IPredicate, Collection<IPredicate>>> oldProgPoint2Context2State = m_ProgPoint2Context2State;
		m_ProgPoint2Context2State = new HashMap<ProgramPoint, Map<IPredicate, Collection<IPredicate>>>();
		Map<ProgramPoint, Collection<IPredicate>> oldProgPoint2StatesWithEmptyContext = m_ProgPoint2StatesWithEmptyContext;
		m_ProgPoint2StatesWithEmptyContext = new HashMap<ProgramPoint, Collection<IPredicate>>();
//		oldContext2ProgPoint = m_Context2ProgPoint;
		m_Context2ProgPoint = new HashMap<IPredicate, Collection<ProgramPoint>>();
		Map<IPredicate, IPredicate> oldContext2Entry = m_Context2Entry;
		m_Context2Entry = new HashMap<IPredicate, IPredicate>();
		
		for (Entry<IPredicate, IPredicate> oldContextEntry : oldContext2Entry.entrySet()) {
			Collection<IPredicate> newContexts = update.getNewPredicates(oldContextEntry.getKey());
			if (newContexts == null) {
				m_Context2Entry.put(oldContextEntry.getKey(), oldContextEntry.getValue());
			} else {
				for (IPredicate newContext : newContexts) {
					Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it = 
							abstraction.callSuccessors(newContext).iterator();
					if (!it.hasNext()) {
						m_Context2Entry.put(newContext, oldContextEntry.getValue());
					} else {
						OutgoingCallTransition<CodeBlock, IPredicate> outCall = it.next();
						IPredicate newEntry = outCall.getSucc();
						m_Context2Entry.put(newContext, newEntry);
						if (it.hasNext()) {
							throw new UnsupportedOperationException(
									"Unable to compute Hoare annotation if state has several outgoging calls");
						}
					}
				}
			}
			
		}
		
		for (Entry<ProgramPoint, Collection<IPredicate>> pp2s : oldProgPoint2StatesWithEmptyContext.entrySet()) {
			for (IPredicate oldPred : pp2s.getValue()) {
				Collection<IPredicate> newPreds = update.getNewPredicates(oldPred);
				if (newPreds == null) {
					// predicate that has already been removed
					super.addDoubleDecker(null, oldPred, null);
				} else {
					for (IPredicate newPred : newPreds) {
						Set<IPredicate> contexts = abstraction.getDownStates(newPred);
						for (IPredicate context : contexts) {
							super.addDoubleDecker(context, newPred, abstraction.getEmptyStackState());
						}
					}
				}
			}
		}
		
		for (Entry<ProgramPoint, Map<IPredicate, Collection<IPredicate>>> pp2c2s : oldProgPoint2Context2State.entrySet()) {
			for (Entry<IPredicate, Collection<IPredicate>> entry : pp2c2s.getValue().entrySet()) {
				IPredicate oldContext = entry.getKey();
				Collection<IPredicate> newContexts = update.getNewPredicates(oldContext);
				for (IPredicate oldPred : entry.getValue()) {
					if (newContexts == null) {
						// double decker that has already been removed because
						// down state was removed (e.g., not on any accepting 
						// run any more.
						super.addDoubleDecker(oldContext, oldPred, null);
					}
					Collection<IPredicate> newPreds = update.getNewPredicates(oldPred);
					if (newPreds == null) {
						if (newContexts == null) {
							// do nothing, we took already care of this case
							// above
						} else {
							// double decker where only up state was removed so
							// far. We have to update down state
							for (IPredicate context : newContexts) {
								super.addDoubleDecker(context, oldPred, null);
							}
						}
					} else {
						for (IPredicate newPred : newPreds) {
							Set<IPredicate> contexts = abstraction.getDownStates(newPred);
							for (IPredicate context : contexts) {
								super.addDoubleDecker(context, newPred, abstraction.getEmptyStackState());
							}
						}
					}
				}
			}
			
		}
		
		
	}
	
	
	interface Update {
		Collection<IPredicate> getNewPredicates(IPredicate oldPredicate);
	}
	
	private class IntersectionUpdate implements Update {

		private final Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> m_Fst2snd2res;
		
		public IntersectionUpdate(
				Map<IPredicate, Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState>> fst2snd2res) {
			m_Fst2snd2res = fst2snd2res;
		}

		@Override
		public Collection<IPredicate> getNewPredicates(IPredicate oldPredicate) {
			Map<IPredicate, IntersectNwa<CodeBlock,IPredicate>.ProductState> mapping = m_Fst2snd2res.get(oldPredicate);
			if (mapping == null) {
				return null;
			} else {
				Collection<IPredicate> result = new ArrayList<IPredicate>();
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
		public Collection<IPredicate> getNewPredicates(IPredicate oldPredicate) {
			IPredicate newPredicate = m_Old2New.get(oldPredicate);
			if (newPredicate == null) {
				return null;
			} else {
				Collection<IPredicate> result = Collections.singleton(newPredicate);
				return result;
			}
		}
	}

}
