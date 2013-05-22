package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class BranchingProcess<S, C> implements IAutomaton<S, C> {
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	
	final private Collection<Condition<S, C>> conditions;
	final private Collection<Event<S, C>> events;

	final ICoRelation<S, C> coRelation;

	final private Map<Place<S, C>, Set<Condition<S, C>>> place2cond;

	final private Event<S, C> dummyRoot;

	private PetriNetJulian<S, C> net;
	
	private final Order<S,C> m_Order;

	public BranchingProcess(PetriNetJulian<S, C> net, Order<S, C> order) {
		this.net = net;
		this.m_Order = order;
		this.place2cond = new HashMap<Place<S, C>, Set<Condition<S, C>>>();
		for (Place<S, C> p : net.getPlaces()) {
			place2cond.put(p, new HashSet<Condition<S, C>>());
		}
		this.conditions = new HashSet<Condition<S, C>>();
		this.events = new HashSet<Event<S, C>>();
		this.coRelation = new ConditionEventsCoRelation<S, C>(this);

		// add a dummy event as root. its successors are the initial conditions.
		this.dummyRoot = new Event<S, C>(net);
		addEvent(dummyRoot);
	}

	/**
	 * gets the "root" event, which is a dummy (has no transition associated)
	 * with all initial conditions as successors.
	 * 
	 * @return
	 */
	public Event<S, C> getDummyRoot() {
		return dummyRoot;
	}

	/**
	 * adds an Event to the Branching Process with all outgoing Conditions.
	 * <p>
	 * updates the Co-Relation.
	 * </p>
	 * 
	 * @return true iff some successor of e corresponds to an accepting place
	 * @param e
	 */
	boolean addEvent(Event<S, C> e) {
		events.add(e);
		for (Condition<S, C> c : e.getPredecessorConditions()) {
			c.addSuccesssor(e);
		}
		boolean someSuccessorIsAccepting = false;
		for (Condition<S, C> c : e.getSuccessorConditions()) {
			conditions.add(c);
			place2cond.get(c.getPlace()).add(c);
			if (isAccepting(c)) {
				someSuccessorIsAccepting = true;
			}
		}
		coRelation.update(e);
		assert checkOneSafety(e) : "Net is not one safe!";
		return someSuccessorIsAccepting;
	}

	private boolean checkOneSafety(Event<S, C> e) {
		for (Condition<S, C> condition : e.getSuccessorConditions()) {
			Set<Condition<S, C>> existing = place2cond
					.get(condition.getPlace());
			for (Condition<S, C> c : existing) {
				if (c != condition && isInCoRelation(c, condition)) {
					s_Logger.debug(c+" in coRelation with "+condition+" but they belong to the same place.");
					return false;
				}
			}
		}
		return true;
	}

	boolean isAccepting(Condition<S, C> c) {
		return net.getAcceptingPlaces().contains(c.getPlace());
	}

	/**
	 * checks if a new event {@code e}, with regards to {@code order} is a
	 * cut-off event. In that case, companions are computed as a side-effect.
	 * 
	 * @see Event#checkCutOffSetCompanion(Event, Comparator, boolean)
	 * @return
	 */
	public boolean isCutoffEvent(Event<S, C> e, Comparator<Event<S, C>> order,
			boolean sameTransitionCutOff) {
		// TODO possibly optimize
		for (Event<S, C> ev : getEvents()) {
			if (e.checkCutOffSetCompanion(ev, order, sameTransitionCutOff)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * return all conditions c s.t. p is the corresponding place of c.
	 */
	public Set<Condition<S, C>> place2cond(Place<S, C> p) {
		return place2cond.get(p);
	}

	public boolean isInCoRelation(Condition<S, C> c1, Condition<S, C> c2) {
		return coRelation.isInCoRelation(c1, c2);
	}

	public int getCoRelationQueries() {
		return coRelation.getCoRelationQueries();
	}

	@SuppressWarnings("unused")
	private boolean isInCoRelationChecker(Condition<S, C> c1, Condition<S, C> c2) {
		return !(isAncestorChecker(c1, c2) || isAncestorChecker(c1, c2) || inConflict(
				c1, c2));
	}

	private boolean isAncestorChecker(Condition<S, C> leaf,
			Condition<S, C> ancestor) {
		if (leaf == ancestor)
			return true;
		Event<S, C> p = leaf.getPredecessorEvent();
		if (p == null || p.getPredecessorConditions() == null)
			return false;
		for (Condition<S, C> parentOfLeaf : p.getPredecessorConditions()) {
			if (isAncestorChecker(parentOfLeaf, ancestor))
				return true;
		}
		return false;
	}

	// private boolean inConflict(Condition<S, C> c1, Condition<S, C> c2) {
	// Set<Condition<S, C>> pred =
	// c1.getPredecessorEvent().getPredecessorConditions();
	// if (pred== null) return false;
	// for (Condition<S, C> condition : pred) {
	// // TODO finish checker Method
	// }
	// return false;
	// }

	boolean isCoset(Collection<Condition<S, C>> coSet, Condition<S, C> c) {
		return coRelation.isCoset(coSet, c);
	}

	public Collection<Condition<S, C>> getConditions() {
		return conditions;
	}

	public Collection<Event<S, C>> getEvents() {
		return events;
	}

	public Collection<Condition<S, C>> initialConditions() {
		return dummyRoot.getSuccessorConditions();
	}

	/**
	 * returns all minimal events of the branching process with respect to the
	 * causal order.
	 * 
	 * @return
	 */
	public Collection<Event<S, C>> getMinEvents() {
		HashSet<Event<S, C>> h = new HashSet<Event<S, C>>();
		HashSet<Event<S, C>> min = new HashSet<Event<S, C>>();
		for (Condition<S, C> c : initialConditions()) {
			h.addAll(c.getSuccessorEvents());
		}
		for (Event<S, C> e : h) {
			if (initialConditions().containsAll(e.getPredecessorConditions())) {
				min.add(e);
			}
		}
		return min;
	}

	/**
	 * gets the net associated with the branching process.
	 * 
	 * @return
	 */
	public PetriNetJulian<S, C> getNet() {
		return net;
	}

	/**
	 * Check if the Conditions c1 and c2 are in causal relation. Conditions c1
	 * and c2 are in causal relation if
	 * <ul>
	 * <li>c1 != c2 and c1 is ancestor of c2</li>
	 * <li>or c1 != c2 and c2 is ancestor of c1</li>
	 * </ul>
	 */
	public boolean inCausalRelation(Condition<S, C> c1, Condition<S, C> c2) {
		if (c1 == c2) {
			return false;
		}
		Set<Object> c1Ancestors = ancestorNodes(c1);
		if (c1Ancestors.contains(c2)) {
			return true;
		}
		Set<Object> c2Ancestors = ancestorNodes(c2);
		if (c2Ancestors.contains(c1)) {
			return true;
		}
		return false;
	}

	/**
	 * Check if Condition c and Event e are in causal relation. Conditions c and
	 * Event e are in causal relation if
	 * <ul>
	 * <li>c is ancestor of e</li>
	 * <li>or e is ancestor of c</li>
	 * </ul>
	 */
	public boolean inCausalRelation(Condition<S, C> c, Event<S, C> e) {
		Set<Object> cAncestors = ancestorNodes(c);
		if (cAncestors.contains(e)) {
			return true;
		}
		Set<Object> eAncestors = ancestorNodes(e);
		if (eAncestors.contains(c)) {
			return true;
		}
		return false;
	}

	/**
	 * Check if the Conditions c1 and c2 are in conflict. In a branching process
	 * Conditions c1 and c2 are in conflict iff c1 != c2 and there exist two
	 * paths leading to c1 and c2 which start at the same condition and diverge
	 * immediately and never converge again.
	 */
	public boolean inConflict(Condition<S, C> c1, Condition<S, C> c2) {
		if (c1 == c2) {
			return false;
		}
		Set<Object> c2Ancestors = ancestorNodes(c2);
		return conflictPathCheck(c1, c2, c2Ancestors);
	}

	/**
	 * @return if c1 != c2 and c2 is no ancestor of c1 the result is true iff
	 *         there is a path from a condition in c2Ancestors to c1 that does
	 *         not contain other elements of c2Ancestors.
	 */
	private boolean conflictPathCheck(Condition<S, C> c1, Condition<S, C> c2,
			Set<Object> c2Ancestors) {
		if (c1 == c2) {
			throw new IllegalArgumentException(c1 + " ancestor of " + c2);
		}
		if (c2Ancestors.contains(c1)) {
			return true;
		}
		Event<S, C> pred = c1.getPredecessorEvent();
		if (c2Ancestors.contains(pred)) {
			return false;
		}
		if (pred == dummyRoot) {
			return false;
		}
		boolean result = false;
		for (Condition<S, C> cPred : pred.getPredecessorConditions()) {
			result = result || conflictPathCheck(cPred, c2, c2Ancestors);
		}
		return result;
	}

	/**
	 * @return Set containing all Conditions and Events which are (strict)
	 *         ancestors of Condition c. The dummyRoot is not considered as an
	 *         ancestor.
	 */
	private Set<Object> ancestorNodes(Condition<S, C> c) {
		Set<Object> ancestorConditionAndEvents = new HashSet<Object>();
		addAllAncestors(c, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * @return Set containing all Conditions and Events which are ancestors of
	 *         Event e. The dummyRoot is not considered as an ancestor.
	 */
	private Set<Object> ancestorNodes(Event<S, C> e) {
		Set<Object> ancestorConditionAndEvents = new HashSet<Object>();
		addAllAncestors(e, ancestorConditionAndEvents);
		return ancestorConditionAndEvents;
	}

	/**
	 * Add to a set that contains only Conditions and Events the Condition c and
	 * all (strict) ancestors of c. The dummyRoot is not considered as an
	 * ancestor.
	 */
	private void addAllAncestors(Condition<S, C> c,
			Set<Object> setOfConditionsAndEvents) {
		Event<S, C> pred = c.getPredecessorEvent();
		setOfConditionsAndEvents.add(pred);
		addAllAncestors(pred, setOfConditionsAndEvents);
	}

	/**
	 * Add to a set that contains only Conditions and Events the Event e and all
	 * (strict) ancestors of e. The dummyRoot is not considered as an ancestor.
	 */
	private void addAllAncestors(Event<S, C> e,
			Set<Object> setOfConditionsAndEvents) {
		if (e == dummyRoot) {
			return;
		} else {
			for (Condition<S, C> pred : e.getPredecessorConditions()) {
				setOfConditionsAndEvents.add(pred);
				addAllAncestors(pred, setOfConditionsAndEvents);
			}
		}
	}

	/**
	 * Given a set <i>conditions</i> returns true iff all elements are pairwise
	 * in conflict or in co-relation;
	 */
	public boolean pairwiseConflictOrCausalRelation(
			Collection<Condition<S, C>> conditions) {
		if (conditions.isEmpty()) {
			throw new IllegalArgumentException(
					"method only defined for non-empty set of conditions");
		}
		boolean result = true;
		for (Condition<S, C> c1 : conditions) {
			for (Condition<S, C> c2 : conditions) {
				if (!inCausalRelation(c1, c2) && !inConflict(c1, c2)) {
					result = false;
				}
			}
		}
		return result;
	}

	public String sizeInformation() {
		return "has " + conditions.size() + "conditions, " + events.size()
				+ " events";
	}

	public Order<S,C> getOrder() {
		return m_Order;
	}

	@Override
	public boolean accepts(Word<S> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<S> getAlphabet() {
		return net.getAlphabet();
	}

	@Override
	public StateFactory<C> getStateFactory() {
		throw new UnsupportedOperationException();
	}

}
