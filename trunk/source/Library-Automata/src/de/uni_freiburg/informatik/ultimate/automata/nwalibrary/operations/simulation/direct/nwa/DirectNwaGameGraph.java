/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.direct.nwa;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.direct.DirectGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.EMultipleDataOption;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.ETransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.NwaGameGraphGeneration;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa.SummarizeEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Game graph that realizes <b>direct simulation</b> for NWA automata.<br/>
 * In direct simulation each time <i>Spoiler</i> visits a final state
 * <i>Duplicator</i> must also visit one at his next turn.<br/>
 * <br/>
 * 
 * If its impossible for <i>Spoiler</i> to build a word such that
 * <i>Duplicator</i> can not fulfill its condition we say <b>q1 direct simulates
 * q0</b> where q0 was the starting state of <i>Spoiler</i> and q1 of
 * <i>Duplicator</i>.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class DirectNwaGameGraph<LETTER, STATE> extends DirectGameGraph<LETTER, STATE> {
	/**
	 * Utility object for generating game graphs based on nwa automata.
	 */
	private final NwaGameGraphGeneration<LETTER, STATE> mGeneration;
	/**
	 * The underlying nwa automaton, as double decker automaton, from which the
	 * game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> mNwa;

	/**
	 * Creates a new direct nwa game graph by using the given nwa automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param nwa
	 *            The underlying nwa automaton from which the game graph gets
	 *            generated.
	 * @param stateFactory
	 *            State factory used for state creation
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	@SuppressWarnings("unchecked")
	public DirectNwaGameGraph(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final INestedWordAutomatonOldApi<LETTER, STATE> nwa,
			final StateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		super(services, progressTimer, logger, nwa, stateFactory);
		// To derive down states of automaton ensure it
		// is a double decker automaton
		final INestedWordAutomatonOldApi<LETTER, STATE> preparedNwa = getAutomaton();
		if (preparedNwa instanceof IDoubleDeckerAutomaton<?, ?>) {
			mNwa = (IDoubleDeckerAutomaton<LETTER, STATE>) preparedNwa;
		} else {
			mNwa = new RemoveUnreachable<LETTER, STATE>(services, preparedNwa).getResult();
		}
		mGeneration = new NwaGameGraphGeneration<LETTER, STATE>(services, getProgressTimer(), getLogger(), mNwa, this,
				ESimulationType.DIRECT);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.direct.DirectGameGraph#generateAutomatonFromGraph()
	 */
	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> generateAutomatonFromGraph() throws AutomataOperationCanceledException {
		final SimulationPerformance performance = getSimulationPerformance();
		if (performance != null) {
			performance.startTimeMeasure(ETimeMeasure.BUILD_RESULT);
		}

//		final INestedWordAutomatonOldApi<LETTER, STATE> result = mGeneration.generateAutomatonFromGraph();
		// TODO Enable the correct simulation again when DD problems are resolved
		@SuppressWarnings("unchecked")
		final INestedWordAutomatonOldApi<LETTER, STATE> result = (INestedWordAutomatonOldApi<LETTER, STATE>) mNwa;

		// Log performance
		if (performance != null) {
			performance.stopTimeMeasure(ETimeMeasure.BUILD_RESULT);
			performance.addAllMeasures(mGeneration.getSimulationPerformance());
		}

		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.AGameGraph#generateGameGraphFromBuechi()
	 */
	@Override
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		mGeneration.generateGameGraphFromAutomaton();

		// Set values for compatibility with non nwa graph
		final SimulationPerformance performance = mGeneration.getSimulationPerformance();
		setGraphBuildTime(performance.getTimeMeasureResult(ETimeMeasure.BUILD_GRAPH, EMultipleDataOption.ADDITIVE));
		setBuechiAmountOfStates(performance.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES));
		setBuechiAmountOfTransitions(performance.getCountingMeasureResult(ECountingMeasure.BUCHI_TRANSITIONS));
		setGraphAmountOfEdges(performance.getCountingMeasureResult(ECountingMeasure.GAMEGRAPH_EDGES));
	}

	/**
	 * Unsupported operation. Use
	 * {@link #getDuplicatorVertex(Object, Object, Object, boolean, ETransitionType, SummarizeEdge, Sink)}
	 * instead.
	 * 
	 * @throws UnsupportedOperationException
	 *             Operation is not supported.
	 */
	@Override
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit) {
		throw new UnsupportedOperationException(
				"Use getDuplicatorVertex(q0, q1, a, bit, transType, summarizeEdge, sink) instead.");
		// TODO Can later be removed but for now
		// it should throw an Exception for problem detection.
	}

	/**
	 * Unsupported operation. Use
	 * {@link #getSpoilerVertex(Object, Object, boolean, SummarizeEdge, Sink)}
	 * instead.
	 * 
	 * @throws UnsupportedOperationException
	 *             Operation is not supported.
	 */
	@Override
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit) {
		throw new UnsupportedOperationException("Use getSpoilerVertex(q0, q1, a, bit, summarizeEdge, sink) instead.");
		// TODO Can later be removed but for now
		// it should throw an Exception for problem detection.
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.AGameGraph#verifyAutomatonValidity(de.uni_freiburg.informatik.
	 * ultimate.automata.nwalibrary.INestedWordAutomatonOldApi)
	 */
	@Override
	public void verifyAutomatonValidity(final INestedWordAutomatonOldApi<LETTER, STATE> automaton) {
		// Do nothing to accept nwa automata
	}

}
