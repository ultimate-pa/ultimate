package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class PetriNetUnfolder<S, C> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	UltimateServices m_UltiServ = UltimateServices.getInstance();

	private final PetriNetJulian<S, C> m_Net;
	private final boolean m_StopIfAcceptingRunFound;
	private final boolean m_SameTransitionCutOff;
	private final order m_Order;
	private final IPossibleExtensions<S, C> m_PossibleExtensions;
	private final BranchingProcess<S, C> m_Unfolding;
	private PetriNetRun<S, C> m_Run;

	@Override
	public String operationName() {
		return "finitePrefix";
	}

	@Override
	public String startMessage() {
		return "Start "
				+ operationName()
				+ ". Net "
				+ m_Net.sizeInformation()
				+ (m_StopIfAcceptingRunFound ? "We stop if some accepting run was found"
						: "We compute complete finite Prefix");
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Unfolding.sizeInformation();
	}

	private final Order<S, C> MC_MILLANS_ORDER = new Order<S, C>() {
		@Override
		public int compare(Configuration<S, C> o1, Configuration<S, C> o2) {
			return o1.size() - o2.size();
		}
	};

	private final Order<S, C> ESPARZAS_ROEMER_VOGLER_ORDER = new Order<S, C>() {

		public int compare(Configuration<S, C> c1, Configuration<S, C> c2) {
			int result = c1.compareTo(c2);
			if (result != 0)
				return result;
			Configuration<S, C> min1 = c1.getMin(m_Unfolding);
			Configuration<S, C> min2 = c2.getMin(m_Unfolding);
			result = min1.compareTo(min2);
			if (result != 0)
				return result;
			Configuration<S, C> c1withoutMin1 = c1.removeMin();
			Configuration<S, C> c2withoutMin2 = c2.removeMin();

			assert (c1.equals(c2) || !c1withoutMin1.equals(c2withoutMin2)) : "\ne1\t="
					+ c1
					+ "\ne2\t="
					+ c2
					+ "\nmin1\t="
					+ min1
					+ "\nmin2\t="
					+ min2
					+ "\n-min1\t="
					+ c1withoutMin1
					+ "\n-min2\t="
					+ c2withoutMin2;

			// The Arguments are here technically no longer Configurations but
			// the lexicographical extension of the order on transitions which
			// is implemented in the compareTo method works on Sets of Events.
			// See 1996TACAS - Esparza,Römer,Vogler, page 13.
			result = compare(c1withoutMin1, c2withoutMin2);
			// result = e1withoutMin1.compareTo(e2withoutMin2);
			return result;
		}
	};

	private final Order<S, C> ERV_EQUAL_MARKING_ORDER = new Order<S, C>() {

		@Override
		public int compare(Event<S, C> o1, Event<S, C> o2) {
			int result = MC_MILLANS_ORDER.compare(o1, o2);
			if (result != 0)
				return result;
			if (!o1.getMark().equals(o2.getMark()))
				return 0;
			Configuration<S, C> c1 = o1.getLocalConfiguration();
			Configuration<S, C> c2 = o2.getLocalConfiguration();
			assert !(c1.containsAll(c2) && c2.containsAll(c1)) : "Different events with equal local configurations. equals:"
					+ c1.equals(c2);
			result = compare(c1, c2);

			return result;
		};

		@Override
		public int compare(Configuration<S, C> c1, Configuration<S, C> c2) {
			return ESPARZAS_ROEMER_VOGLER_ORDER.compare(c1, c2);
		}
	};
	
	private PetriNetUnfolder<S, C>.Statistics m_Statistics = new Statistics();

	/**
	 * 
	 * Build the finite Prefix of PetriNet net.
	 * 
	 * @param Order
	 *            the order on events and configurations respectively is used to
	 *            determine cut-off events.
	 * @param sameTransitionCutOff
	 *            if true, an additional condition for cut-off events is used:
	 *            An event and its companion must belong to the same transition
	 *            from the net.
	 * @param stopIfAcceptingRunFound
	 *            if false, the complete finite Prefix will be build.
	 * @throws OperationCanceledException
	 */
	public PetriNetUnfolder(PetriNetJulian<S, C> net, order Order,
			boolean sameTransitionCutOff, boolean stopIfAcceptingRunFound)
			throws OperationCanceledException {
		this.m_Net = net;
		this.m_StopIfAcceptingRunFound = stopIfAcceptingRunFound;
		this.m_SameTransitionCutOff = sameTransitionCutOff;
		this.m_Order = Order;
		s_Logger.info(startMessage());
		this.m_Unfolding = new BranchingProcess<S, C>(net, ESPARZAS_ROEMER_VOGLER_ORDER);
		// this.cutOffEvents = new HashSet<Event<S, C>>();
		Order<S, C> queueOrder = MC_MILLANS_ORDER;
		switch (Order) {
		case ERV_MARK:
			queueOrder = ERV_EQUAL_MARKING_ORDER;
			break;
		case ERV:
			queueOrder = ESPARZAS_ROEMER_VOGLER_ORDER;
			break;
		}
		this.m_PossibleExtensions = new PossibleExtensions<S, C>(m_Unfolding,
				queueOrder);

		computeUnfolding();
		s_Logger.info(exitMessage());
		s_Logger.info(m_Statistics.cutOffInformation());
		s_Logger.info(m_Statistics.coRelationInformation());
	}

	private void computeUnfolding() throws OperationCanceledException {
		m_PossibleExtensions.update(m_Unfolding.getDummyRoot());

		while (!m_PossibleExtensions.isEmpy()) {
			Event<S, C> e = m_PossibleExtensions.remove();

			if (!parentIsCutoffEvent(e)) {
				boolean succOfEventIsAccpting = m_Unfolding.addEvent(e);
				// assert !unfolding.pairwiseConflictOrCausalRelation(
				// e.getPredecessorConditions());
				if (succOfEventIsAccpting && m_Run == null) {
					m_Run = constructRun(e);
					if (m_StopIfAcceptingRunFound) {
						return;
					}
				}
				// TODO: switch over the order given in the constructor.
				if (!m_Unfolding.isCutoffEvent(e, ESPARZAS_ROEMER_VOGLER_ORDER,
						m_SameTransitionCutOff)) {
					m_PossibleExtensions.update(e);
					s_Logger.debug("Constructed Non-cut-off-Event: "
							+ e.toString());
				} else {
					s_Logger.debug("Constructed     Cut-off-Event: "
							+ e.toString());
				}
				s_Logger.debug("Possible Extension size: "
						+ m_PossibleExtensions.size() + ", total #Events: "
						+ m_Unfolding.getEvents().size()
						+ ", total #Conditions: "
						+ m_Unfolding.getConditions().size());
				m_Statistics.add(e);
			}
			// else {
			// assert (false);
			// }

			if (!m_UltiServ.continueProcessing()) {
				throw new OperationCanceledException();
			}
		}
	}

	/**
	 * constructs a run over the unfolding which leads to the marking
	 * corresponding with the local configuration of the specified event e.
	 * 
	 * uses the recursive helper-method {@code #constructRun(Event, Marking)}
	 * 
	 * @param e
	 * @return
	 */
	private PetriNetRun<S, C> constructRun(Event<S, C> e) {
		s_Logger.debug("Marking: " + m_Unfolding.getDummyRoot().getMark());
		return constructRun(e, m_Unfolding.getDummyRoot().getConditionMark()).Run;
	}

	/**
	 * Recursively builds a part of a run over the unfolding which leads to the
	 * marking corresponding with the local configuration of the specified event
	 * e.
	 * 
	 * The run starts with the given Marking {@code initialMarking}
	 * 
	 * @param e
	 * @param initialMarking
	 * @return
	 */
	private RunAndConditionMarking constructRun(Event<S, C> e,
			ConditionMarking<S, C> initialMarking) {
		assert (e != m_Unfolding.getDummyRoot());
		assert (e.getPredecessorConditions().size() > 0);
		assert !m_Unfolding.pairwiseConflictOrCausalRelation(e
				.getPredecessorConditions());
		PetriNetRun<S, C> run = new PetriNetRun<S, C>(
				initialMarking.getMarking());
		ConditionMarking<S, C> current = initialMarking;
		for (Condition<S, C> c : e.getPredecessorConditions()) {
			if (current.contains(c))
				continue;
			RunAndConditionMarking result = constructRun(
					c.getPredecessorEvent(), current);
			run = run.concatenate(result.Run);
			current = result.Marking;
		}
		assert (current != null);

		ConditionMarking<S, C> finalMarking = current.fireEvent(e);
		ITransition<S, C> t = e.getTransition();
		PetriNetRun<S, C> appendix = new PetriNetRun<S, C>(
				current.getMarking(), t.getSymbol(), finalMarking.getMarking());
		run = run.concatenate(appendix);

		s_Logger.debug("Event  : " + e);
		s_Logger.debug("Marking: " + run.getMarking(run.getWord().length()));
		return new RunAndConditionMarking(run, finalMarking);
	}

	class RunAndConditionMarking {
		public RunAndConditionMarking(PetriNetRun<S, C> run,
				ConditionMarking<S, C> marking) {
			Run = run;
			Marking = marking;
		}

		public PetriNetRun<S, C> Run;
		public ConditionMarking<S, C> Marking;
	}

	private boolean parentIsCutoffEvent(Event<S, C> e) {
		for (Condition<S, C> c : e.getPredecessorConditions()) {
			if (c.getPredecessorEvent().isCutoffEvent()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Return some accepting run of PetriNet net, return null if net does not
	 * have an accepting run.
	 */
	public PetriNetRun<S, C> getAcceptingRun() {
		if (!ResultChecker.isEmpty(m_Net, m_Run)) {
			throw new AssertionError();
		}
		// assert (ResultChecker.isEmpty(net, m_Run));
		return m_Run;
	}

	/**
	 * Return the occurrence net which is the finite prefix of the unfolding of
	 * net.
	 */
	public BranchingProcess<S, C> getFinitePrefix() {
		assert (ResultChecker.isEmpty(m_Net, m_Run));
		return m_Unfolding;
	}

	/**
	 * Return an PetriNet that recognizes the same language as net but has a a
	 * similar structure as the occurrence net which is the finite prefix of
	 * net.
	 */
	// TODO Julian and Matthias have to discuss what similar means.
	public PetriNetJulian<S, C> getUnfoldedPetriNet() {
		return null;
	}

	public enum order {
		ERV("Esparza Römer Vogler"), KMM("Ken McMillan"), ERV_MARK(
				"ERV with equal markings");

		String m_Description;

		private order(String name) {
			m_Description = name;
		}

		public String getDescription() {
			return m_Description;
		}
	};

	// FIXME documentation
	private class Statistics {
		Map<ITransition<S, C>, Map<Marking<S, C>, Set<Event<S, C>>>> m_Trans2Mark2Events = new HashMap<ITransition<S, C>, Map<Marking<S, C>, Set<Event<S, C>>>>();
		int m_CutOffEvents = 0;
		int m_NonCutOffEvents = 0;

		public void add(Event<S, C> e) {
			Marking<S, C> marking = e.getMark();
			ITransition<S, C> transition = e.getTransition();
			Map<Marking<S, C>, Set<Event<S, C>>> mark2Events = m_Trans2Mark2Events
					.get(transition);
			if (mark2Events == null) {
				mark2Events = new HashMap<Marking<S, C>, Set<Event<S, C>>>();
				m_Trans2Mark2Events.put(transition, mark2Events);
			}
			Set<Event<S, C>> events = mark2Events.get(marking);
			if (events == null) {
				events = new HashSet<Event<S, C>>();
				mark2Events.put(marking, events);
			}
			if (!events.isEmpty()) {
				s_Logger.info("inserting again Event for Transition "
						+ transition + " and Marking " + marking);
				s_Logger.info("new Event has " + e.getAncestors()
						+ " ancestors and is "
						+ (e.isCutoffEvent() ? "" : "not ") + "cut-off event");
				for (Event<S, C> event : events) {
					s_Logger.info("  existing Event has "
							+ event.getAncestors() + " ancestors and is "
							+ (e.isCutoffEvent() ? "" : "not ")
							+ "cut-off event");
					assert (event.getAncestors() == e.getAncestors() | e
							.isCutoffEvent());
				}
			}
			events.add(e);

			if (e.isCutoffEvent()) {
				m_CutOffEvents++;
			} else {
				m_NonCutOffEvents++;
			}

		}

		public String cutOffInformation() {
			return "has " + m_CutOffEvents + " CutOffEvents and "
					+ m_NonCutOffEvents + " nonCutOffEvents";
		}

		public String coRelationInformation() {
			return "co relation was queried "
					+ m_Unfolding.getCoRelationQueries() + " times.";
		}
	}

	@Override
	public BranchingProcess<S, C> getResult() throws OperationCanceledException {
		return m_Unfolding;
	}

}
