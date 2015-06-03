package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Computes lassos, caches computed lassos 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class AcceptingLassoProvider<LETTER, STATE> {
	/**
	 * 
	 */
	private final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	/**
	 * Use also other methods for lasso construction. This is only useful if you
	 * want to analyze if the lasso construction can be optimized.
	 */
	private final static boolean m_UseAlternativeLassoConstruction = false;
	

	private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;
	
	private final SccComputationWithAcceptingLassos<LETTER, STATE> m_SccComputation;

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private NestedLassoRun<LETTER, STATE> m_NestedLassoRun;

	/**
	 * 
	 * @param nestedWordAutomatonReachableStates
	 * @param asc
	 * @param services
	 * @param sccComputation 
	 * @param allStates states that are considered in this SCC computation
	 * @param startStates
	 */
	public AcceptingLassoProvider(NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates, 
			NestedWordAutomatonReachableStates<LETTER, STATE>.AcceptingSummariesComputation asc, 
			IUltimateServiceProvider services, SccComputationWithAcceptingLassos<LETTER, STATE> sccComputation) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.nestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		m_SccComputation = sccComputation;
		m_AcceptingSummaries = asc.getAcceptingSummaries();
	}

	public List<NestedLassoRun<LETTER, STATE>> computeNestedLassoRuns(boolean onePerScc) throws OperationCanceledException {
		if (onePerScc) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		List<NestedLassoRun<LETTER, STATE>> nestedLassoRuns = new ArrayList<NestedLassoRun<LETTER, STATE>>();
		for (SccComputationWithAcceptingLassos<LETTER, STATE>.SCComponent scc : m_SccComputation.getBalls()) {
			if (scc.isAccepting()) {
				for (StateContainer<LETTER, STATE> fin : scc.getAcceptingStatesContainers()) {
					NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(m_Services, 
							nestedWordAutomatonReachableStates, fin, scc)).getNestedLassoRun();
					if (m_UseAlternativeLassoConstruction) {
						int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
								m_Services, nestedWordAutomatonReachableStates, fin)).getNestedLassoRun();
						int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr3 = (new LassoExtractor<LETTER, STATE>(m_Services, 
								nestedWordAutomatonReachableStates, fin, scc, m_AcceptingSummaries))
								.getNestedLassoRun();
						int nlr3Size = nlr3.getStem().getLength() + nlr3.getLoop().getLength();
					}
					nestedLassoRuns.add(nlr2);
				}
				for (StateContainer<LETTER, STATE> sumPred : scc.getAcceptingSummariesOfSCC().getDomain()) {
					Set<Summary<LETTER, STATE>> summaries = scc.getAcceptingSummariesOfSCC().getImage(sumPred);
					for (Summary<LETTER, STATE> summary : summaries) {
						NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(m_Services, 
								nestedWordAutomatonReachableStates, summary, scc)).getNestedLassoRun();
						if (m_UseAlternativeLassoConstruction) {
							NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
									m_Services, nestedWordAutomatonReachableStates, sumPred)).getNestedLassoRun();
							int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
							int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
						}
						nestedLassoRuns.add(nlr2);
					}
				}
			}
		}
		return nestedLassoRuns;
	}

	public void computeShortNestedLassoRun() throws AutomataLibraryException {
		StateContainer<LETTER, STATE> lowestSerialNumber = null;
		StateContainer<LETTER, STATE> newlowestSerialNumber = null;
		SccComputationWithAcceptingLassos<LETTER, STATE>.SCComponent sccOfLowest = null;
		for (SccComputationWithAcceptingLassos<LETTER, STATE>.SCComponent scc : m_SccComputation.getBalls()) {
			if (scc.isAccepting()) {
				StateContainer<LETTER, STATE> lowestOfScc = scc.getAcceptingWithLowestSerialNumber();
				newlowestSerialNumber = StateContainer.returnLower(lowestSerialNumber, lowestOfScc);
				if (newlowestSerialNumber != lowestSerialNumber) {
					lowestSerialNumber = newlowestSerialNumber;
					sccOfLowest = scc;
				}
			}
		}
		NestedLassoRun<LETTER, STATE> method4 = (new LassoConstructor<LETTER, STATE>(m_Services, 
				nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest)).getNestedLassoRun();
		m_Logger.debug("Method4: stem" + method4.getStem().getLength() + " loop" + method4.getLoop().getLength());
		if (m_UseAlternativeLassoConstruction) {
			NestedLassoRun<LETTER, STATE> method0 = (new LassoExtractor<LETTER, STATE>(m_Services, 
					nestedWordAutomatonReachableStates, sccOfLowest.getStateWithLowestSerialNumber(),
					sccOfLowest, m_AcceptingSummaries)).getNestedLassoRun();
			m_Logger.debug("Method0: stem" + method0.getStem().getLength() + " loop"
					+ method0.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method1 = (new LassoExtractor<LETTER, STATE>(m_Services, 
					nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest, m_AcceptingSummaries))
					.getNestedLassoRun();
			m_Logger.debug("Method1: stem" + method1.getStem().getLength() + " loop"
					+ method1.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method2 = (new ShortestLassoExtractor<LETTER, STATE>(
					m_Services, nestedWordAutomatonReachableStates, lowestSerialNumber)).getNestedLassoRun();
			m_Logger.debug("Method2: stem" + method2.getStem().getLength() + " loop"
					+ method2.getLoop().getLength());
			int method0size = method0.getStem().getLength() + method0.getLoop().getLength();
			int method1size = method1.getStem().getLength() + method1.getLoop().getLength();
			int method2size = method2.getStem().getLength() + method1.getLoop().getLength();
			m_Logger.debug("Method0size" + method0size + " Method1size" + method1size + " Method2size"
					+ method2size);
		}
		m_NestedLassoRun = method4;
	}

	public List<NestedLassoRun<LETTER, STATE>> getAllNestedLassoRuns() throws OperationCanceledException {
		if (m_SccComputation.buchiIsEmpty()) {
			return Collections.emptyList();
		} else {
			if (m_NestedLassoRuns == null) {
				m_NestedLassoRuns = computeNestedLassoRuns(false);
			}
			return m_NestedLassoRuns;
		}
	}

	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataLibraryException {
		if (m_SccComputation.buchiIsEmpty()) {
			return null;
		} else {
			if (m_NestedLassoRun == null) {
				computeShortNestedLassoRun();
			}
			return m_NestedLassoRun;
		}
	}
}