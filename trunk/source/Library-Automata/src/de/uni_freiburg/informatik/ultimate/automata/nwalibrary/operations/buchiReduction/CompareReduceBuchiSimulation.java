package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.delayed.DelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Operation that compares the different types of simulation methods for buechi
 * reduction.<br/>
 * The resulting automaton is the input automaton.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class CompareReduceBuchiSimulation<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	/**
	 * Factor that, if multiplied with, converts seconds to milliseconds.
	 */
	private final static int SECONDS_TO_MILLIS = 1000;
	/**
	 * Decimal places to round duration of a method to.
	 */
	private final static int DECIMAL_PLACES = 2;

	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * The inputed buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	/**
	 * The resulting possible reduced buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final IUltimateServiceProvider m_Services;
	/**
	 * Starting time-stamp of the current active time measure.
	 */
	private long m_StartTime;
	/**
	 * Internal buffer for logged lines, can be flushed by using
	 * {@link #flushLogs()}.
	 */
	private final List<String> m_LoggedLines;

	/**
	 * Compares the different types of simulation methods for buechi reduction.
	 * Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public CompareReduceBuchiSimulation(final IUltimateServiceProvider services, final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		m_LoggedLines = new LinkedList<String>();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Result = operand;

		m_Logger.info(startMessage());
		try {
			logLine("Name\tDuration\tEliminated states");

			// Direct simulation without SCC
			startTimeMeasure();
			measureMethodEffectiveness("Direct w/o SCC",
					new DirectSimulation<>(services, operand, false, stateFactory));
			// Direct simulation with SCC
			startTimeMeasure();
			measureMethodEffectiveness("Direct w/ SCC", new DirectSimulation<>(services, operand, true, stateFactory));

			// Delayed simulation without SCC
			startTimeMeasure();
			measureMethodEffectiveness("Delayed w/o SCC",
					new DelayedSimulation<>(services, operand, false, stateFactory));
			// Delayed simulation with SCC
			startTimeMeasure();
			measureMethodEffectiveness("Delayed w/ SCC",
					new DelayedSimulation<>(services, operand, true, stateFactory));

			// Fair simulation without SCC
			startTimeMeasure();
			measureMethodEffectiveness("Fair w/o SCC", new FairSimulation<>(services, operand, false, stateFactory));
			// Fair simulation with SCC
			startTimeMeasure();
			measureMethodEffectiveness("Fair w/ SCC", new FairSimulation<>(services, operand, true, stateFactory));

			// Fair direct simulation without SCC
			startTimeMeasure();
			measureMethodEffectiveness("FairDirect w/o SCC",
					new FairDirectSimulation<>(services, operand, false, stateFactory));
			// Fair direct simulation with SCC
			startTimeMeasure();
			measureMethodEffectiveness("FairDirect w/ SCC",
					new FairDirectSimulation<>(services, operand, true, stateFactory));

			// Other minimization methods
			// TODO Fix problem with not possible cast to IDoubleDecker
//			startTimeMeasure();
//			measureMethodEffectiveness("MinimizeSevpa", new MinimizeSevpa<>(services, operand));
//			startTimeMeasure();
//			measureMethodEffectiveness("ShrinkNwa", new ShrinkNwa<>(services, stateFactory, operand));
		} catch (AutomataLibraryException e) {

		} finally {
			flushLogs();
		}
		m_Logger.info(exitMessage());
	}

	/**
	 * Logs a given message as single line. Uses a internal buffer that needs to
	 * be flushed in order to actually print the logs. Flushing is done by using
	 * {@link #flushLogs()}.
	 * 
	 * @param message
	 *            Message to log
	 */
	private void logLine(final String message) {
		m_LoggedLines.add(message);
	}

	/**
	 * Flushes the internal buffered log messages.
	 */
	private void flushLogs() {
		for (String message : m_LoggedLines) {
			m_Logger.info(message);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ".";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Object getResult() throws AutomataLibraryException {
		return m_Result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "compareReduceBuchiSimulation";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#startMessage()
	 */
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand has " + m_Operand.sizeInformation();
	}

	/**
	 * Measures the effectiveness of a given method for buechi reduction and
	 * logs it.<br/>
	 * The format of the log is: <tt>NAME\tDURATION\tELIMINATED_STATES<tt> where
	 * duration is in seconds.
	 * 
	 * @param methodName
	 *            Name of the used method
	 * @param method
	 *            Used method
	 * @throws AutomataLibraryException
	 *             If a automata library exception occurred.
	 */
	@SuppressWarnings("unchecked")
	private void measureMethodEffectiveness(final String methodName, final Object method)
			throws AutomataLibraryException {
		// Duration
		long durationInMillis = stopTimeMeasure();
		BigDecimal durationAsBigDecimal = new BigDecimal((durationInMillis + 0.0) / SECONDS_TO_MILLIS);
		durationAsBigDecimal = durationAsBigDecimal.setScale(DECIMAL_PLACES, RoundingMode.HALF_UP);
		float duration = durationAsBigDecimal.floatValue();

		INestedWordAutomatonOldApi<LETTER, STATE> methodResult = null;
		if (method instanceof ASimulation) {
			ASimulation<LETTER, STATE> simulation = (ASimulation<LETTER, STATE>) method;
			methodResult = simulation.getResult();
		} else if (method instanceof MinimizeSevpa) {
			MinimizeSevpa<LETTER, STATE> minimizeSevpa = (MinimizeSevpa<LETTER, STATE>) method;
			methodResult = minimizeSevpa.getResult();
		} else if (method instanceof ShrinkNwa) {
			ShrinkNwa<LETTER, STATE> shrinkNwa = (ShrinkNwa<LETTER, STATE>) method;
			methodResult = (INestedWordAutomatonOldApi<LETTER, STATE>) shrinkNwa.getResult();
		}

		// Eliminated states
		int eliminatedStates = -1;
		if (methodResult != null) {
			eliminatedStates = m_Operand.size() - methodResult.size();
		}

		logLine(methodName + "\t" + duration + "\t" + eliminatedStates);
	}

	/**
	 * Remembers the current time-stamp for a time measure. Time measure can be
	 * stopped by using {@link #stopTimeMeasure()}.
	 */
	private void startTimeMeasure() {
		m_StartTime = System.currentTimeMillis();
	}

	/**
	 * Calculates the time difference between now and of the last time called
	 * {@link CompareReduceBuchiSimulation#startTimeMeasure()}.
	 * 
	 * @return Duration between now and the last time called
	 *         {@link CompareReduceBuchiSimulation#startTimeMeasure()} in
	 *         milliseconds.
	 */
	private long stopTimeMeasure() {
		return System.currentTimeMillis() - m_StartTime;
	}

}
