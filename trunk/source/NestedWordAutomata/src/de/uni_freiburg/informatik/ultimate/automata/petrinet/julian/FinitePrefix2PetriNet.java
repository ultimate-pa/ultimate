package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class FinitePrefix2PetriNet<L, C> implements IOperation<L, C> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	BranchingProcess<L, C> m_Input;
	PetriNetJulian<L, C> m_Net;
	private UnionFind<Condition<L, C>> representatives;

	@Override
	public String operationName() {
		return "finitePrefix2PetriNet";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + "Input " + m_Input.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Net.sizeInformation();
	}

	@Override
	public PetriNetJulian<L, C> getResult() throws OperationCanceledException {
		return m_Net;
	}
	
	
//	private Condition<L,C> getRepresentative(Condition<L,C> c) {
//		Condition<L,C> result = c;
//		while (result != representatives.get(result)) {
//			result = representatives.get(result);
//			assert result != null;
//		}
//		return result;
//	}

	public FinitePrefix2PetriNet(BranchingProcess<L, C> bp) {
		// TODO implement merging for markings?
		m_Input = bp;
		s_Logger.info(startMessage());

		Map<Condition<L, C>, Place<L, C>> placeMap = new HashMap<Condition<L, C>, Place<L, C>>();
		Map<Event<L, C>, Transition<L, C>> transitionMap = new HashMap<Event<L, C>, Transition<L, C>>();

		s_Logger.debug("CONDITIONS:");
		for (Condition<L, C> c : bp.getConditions())
			s_Logger.debug(c);
		s_Logger.debug("EVENTS:");
		for (Event<L, C> e : bp.getEvents())
			s_Logger.debug(e.getPredecessorConditions() + " || " + e + " || "
					+ e.getSuccessorConditions());

		PetriNetJulian<L, C> old_net = m_Input.getNet();
		m_Net = new PetriNetJulian<L, C>(old_net.getAlphabet(),
				old_net.getStateFactory(), false);
		
		
		
//		List<Event<L, C>> events = new ArrayList<Event<L,C>>();
//		List<Event<L, C>> worklist = new LinkedList<Event<L,C>>();
//		Set<Event<L, C>> visited = new HashSet<Event<L,C>>();
//
//		for (Event<L, C> e : bp.getMinEvents()) {
//			worklist.add(e);
//			events.add(e);
//			visited.add(e);
//		}
//		while(!worklist.isEmpty()) {
//			Event<L,C> event = worklist.remove(0);
//			for (Condition<L,C> c : event.getSuccessorConditions()) {
//				for (Event<L,C> e : c.getSuccessorEvents()) {
//					if (!visited.contains(e)) {
//						worklist.add(e);
//						events.add(e);
//						visited.add(e);
//					}
//				}
//			}
//		}
//		for (Event e : bp.getEvents()) {
//			assert e == bp.getDummyRoot() || visited.contains(e);
//		}
		TreeSet<Event<L,C>> events = new TreeSet<Event<L,C>>(bp.getOrder());
		events.addAll(bp.getEvents());
		
		representatives = new UnionFind<Condition<L, C>>();
		for (Condition c : bp.getDummyRoot().getSuccessorConditions()) {
			representatives.makeSet(c);
		}
		Iterator<Event<L, C>> it = events.iterator();
		Event<L, C> first = it.next();
		assert first == bp.getDummyRoot();
		Event<L,C> previous;
		Event<L,C> current = first;
		while (it.hasNext()) {
			previous = current;
			current = it.next();
			assert bp.getOrder().compare(previous, current) < 0;
			
			for (Condition<L,C> c : current.getConditionMark()) {
				Place p = c.getPlace();
				Condition<L, C> representative = representatives.find(c);
				if (representative == null) {
					representatives.makeSet(c);
				}
			}
			
			if (current.isCutoffEvent()) {
				Event<L,C> companion = current.getCompanion();
				ConditionMarking<L,C> companionCondMark = companion.getConditionMark();
				ConditionMarking<L,C> eCondMark = current.getConditionMark();
				mergeConditions(companionCondMark, eCondMark);
				mergeConditions(companion.getPredecessorConditions(), current.getPredecessorConditions());
			}

		}
		
		for (Condition c : bp.getConditions()) {
			assert representatives.find(c) != null;
			if (c == representatives.find(c)) {
				Place<L, C> place = m_Net.addPlace(old_net.getStateFactory()
						.finitePrefix2net(c), bp.initialConditions()
						.contains(c), bp.isAccepting(c));
				placeMap.put(c, place);
			}
		}
		TransitionSet transitionSet = new TransitionSet();
		for (Event<L,C> e : events) {
			if (e == bp.getDummyRoot()) {
				continue;
			}
			Set<Place<L, C>> preds = new HashSet<Place<L, C>>();
			Set<Place<L, C>> succs = new HashSet<Place<L, C>>();
			
			for (Condition<L, C> c : e.getPredecessorConditions()) {
				Condition<L, C> representative = representatives.find(c);
				preds.add(placeMap.get(representative));
			}
			
			for (Condition<L, C> c : e.getSuccessorConditions()) {
				Condition<L, C> representative = representatives.find(c);
				succs.add(placeMap.get(representative));
			}
			transitionSet.addTransition(e.getTransition().getSymbol(), preds, succs);
			//	m_Net.addTransition(e.getTransition().getSymbol(), preds, succs);
		}
		transitionSet.addAllTransitionsToNet(m_Net);
		
		
		
		
		
//		for (Condition<L, C> c : bp.getConditions()) {
//			if (!c.getPredecessorEvent().isCutoffEvent()) {
//				Place<L, C> place = m_Net.addPlace(old_net.getStateFactory()
//						.finitePrefix2net(c), bp.initialConditions()
//						.contains(c), bp.isAccepting(c));
//				placeMap.put(c, place);
//			}
//		}
//		s_Logger.debug("CONDITIONS TO PLACE:");
//		for (Map.Entry<Condition<L, C>, Place<L, C>> en : placeMap.entrySet())
//			s_Logger.debug(en);
//		for (Event<L, C> e : bp.getEvents()) {
//			if (e.getTransition() == null)
//				continue;
//			ArrayList<Place<L, C>> preds = new ArrayList<Place<L, C>>();
//			ArrayList<Place<L, C>> succs = new ArrayList<Place<L, C>>();
//			for (Condition<L, C> pc : e.getPredecessorConditions()) {
//				assert placeMap.containsKey(pc) : pc.toString()
//						+ " has successors, hence cannot be child of cut-off event. So it must have been added, but it cannot be found.";
//				preds.add(placeMap.get(pc));
//			}
//			Event<L, C> companionOrE = e;
//			if (e.isCutoffEvent())
//				companionOrE = e.getCompanion();
//			for (Condition<L, C> sc : companionOrE.getSuccessorConditions()) {
//				assert placeMap.containsKey(sc);
//				succs.add(placeMap.get(sc));
//			}
//			Transition<L, C> transition = m_Net.addTransition(e.getTransition()
//					.getSymbol(), preds, succs);
//			transitionMap.put(e, transition);
//		}

		s_Logger.info(exitMessage());
		try {
			assert ResultChecker.petriNetLanguageEquivalence(old_net, m_Net) : 
				"The language recognized by the FinitePrefix2PetriNet is not equal to the language of the original net.";
		} catch (OperationCanceledException e1) {
			e1.printStackTrace();
		}
	}
	
	
	private void mergeConditions(Iterable<Condition<L,C>> set1, Iterable<Condition<L,C>> set2) {
		Map<Place<L,C>, Condition<L,C>> origPlace2Condition = new HashMap<Place<L,C>, Condition<L,C>>();
		for (Condition<L,C> c1 : set1) {
			origPlace2Condition.put(c1.getPlace(), c1);
		}
		
		for (Condition<L,C> c2 : set2) {
			Place p2 = c2.getPlace();
			Condition c1 = origPlace2Condition.get(p2);
			Condition<L, C> c1representative = representatives.find(c1);
			assert c1representative != null;
			
			Condition<L, C> c2representative = representatives.find(c2);
			assert c2representative != null;
			
			representatives.union(c1representative, c2representative);
		}
	}
	
	
	
	private class UnionFind<E> {
		Map<E,Set<E>> m_Element2Set = new HashMap<E,Set<E>>();
		Map<Set<E>,E> m_CanonicalElement = new HashMap<Set<E>,E>();
		
		public E find(E element) {
			Set<E> set = m_Element2Set.get(element);
			return m_CanonicalElement.get(set);
		}
		
		public void makeSet(E element) {
			if (m_Element2Set.containsKey(element)) {
				throw new IllegalArgumentException("Already contained " + element);
			}
			Set<E> result = new HashSet<E>();
			result.add(element);
			m_Element2Set.put(element, result);
			m_CanonicalElement.put(result, element);
		}
		
		public void union(E e1, E e2) {
			Set<E> set1 = m_Element2Set.get(e1);
			Set<E> set2 = m_Element2Set.get(e2);
			E set1rep = m_CanonicalElement.get(set1);
			m_CanonicalElement.remove(set1);
			m_CanonicalElement.remove(set2);
			set1.addAll(set2);
			for (E e : set2) {
				m_Element2Set.put(e, set1);
			}
			m_CanonicalElement.put(set1, set1rep);
		}
		
		@Override
		public String toString() {
			return m_CanonicalElement.toString();
		}
	}
	
	
	class TransitionSet {
		Map<L, Map< Set<Place<L, C>>, Set<Set<Place<L, C>>>>> m_Letter2Predset2Succsets = 
				new HashMap<L, Map< Set<Place<L, C>>, Set<Set<Place<L, C>>>>>();
		
		void addTransition(L letter, Set<Place<L, C>> predset, Set<Place<L, C>> succset) {
			Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>> predsets2succsets = m_Letter2Predset2Succsets.get(letter);
			if (predsets2succsets == null) {
				predsets2succsets = new HashMap<Set<Place<L, C>>, Set<Set<Place<L, C>>>>();
				m_Letter2Predset2Succsets.put(letter, predsets2succsets);
			}
			Set<Set<Place<L, C>>> succsets = predsets2succsets.get(predset);
			if (succsets == null) {
				succsets = new HashSet<Set<Place<L, C>>>();
				predsets2succsets.put(predset, succsets);
			}
			succsets.add(succset);
		}
		
		void addAllTransitionsToNet(PetriNetJulian<L,C> net) {
			for (L letter : m_Letter2Predset2Succsets.keySet()) {
				Map<Set<Place<L, C>>, Set<Set<Place<L, C>>>> predsets2succsets = m_Letter2Predset2Succsets.get(letter);
				for (Set<Place<L,C>> predset : predsets2succsets.keySet()) {
					Set<Set<Place<L, C>>> succsets = predsets2succsets.get(predset);
					for (Set<Place<L, C>> succset : succsets) {
						List<Place<L,C>> predList = new ArrayList<Place<L,C>>(predset);
						List<Place<L,C>> succList = new ArrayList<Place<L,C>>(succset);
						net.addTransition(letter, predList, succList);
					}
				}
			}
		}
	}


	@Override
	public boolean checkResult(StateFactory<C> stateFactory)
			throws OperationCanceledException {
		return true;
	}
}
