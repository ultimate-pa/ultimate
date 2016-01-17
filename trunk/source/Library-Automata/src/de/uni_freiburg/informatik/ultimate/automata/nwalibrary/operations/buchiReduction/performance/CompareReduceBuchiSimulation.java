/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
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
	 * Decimal places to round duration of a method to.
	 */
	private final static int DECIMAL_PLACES = 2;
	/**
	 * Factor that, if multiplied with, converts seconds to milliseconds.
	 */
	private final static int SECONDS_TO_MILLIS = 1000;

	/**
	 * Internal buffer for logged lines, can be flushed by using
	 * {@link #flushLogToLogger()}.
	 */
	private final List<String> m_LoggedLines;
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
			appendPerformanceHeadToLog();

			// Direct simulation without SCC
			appendMethodPerformanceToLog(new DirectSimulation<>(services, operand, false, stateFactory));
			// Direct simulation with SCC
			appendMethodPerformanceToLog(new DirectSimulation<>(services, operand, true, stateFactory));

			// Delayed simulation without SCC
			appendMethodPerformanceToLog(new DelayedSimulation<>(services, operand, false, stateFactory));
			// Delayed simulation with SCC
			appendMethodPerformanceToLog(new DelayedSimulation<>(services, operand, true, stateFactory));

			// Fair simulation without SCC
			appendMethodPerformanceToLog(new FairSimulation<>(services, operand, false, stateFactory));
			// Fair simulation with SCC
			appendMethodPerformanceToLog(new FairSimulation<>(services, operand, true, stateFactory));

			// Fair direct simulation without SCC
			appendMethodPerformanceToLog(new FairDirectSimulation<>(services, operand, false, stateFactory));
			// Fair direct simulation with SCC
			appendMethodPerformanceToLog(new FairDirectSimulation<>(services, operand, true, stateFactory));

			// Other minimization methods
			// TODO Fix problem with not possible cast to IDoubleDecker
			// startTimeMeasure();
			// measureMethodEffectiveness("MinimizeSevpa", new
			// MinimizeSevpa<>(services, operand));
			// startTimeMeasure();
			// measureMethodEffectiveness("ShrinkNwa", new ShrinkNwa<>(services,
			// stateFactory, operand));
		} catch (AutomataLibraryException e) {
			e.printStackTrace();
		} finally {
			// flushLogToLogger();
			flushLogToFile();
		}
		m_Logger.info(exitMessage());
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
	 * The format of the log is:
	 * <tt>NAME\tSCCS\tDURATION\tREMOVED_STATES\tREMOVED_TRANSITIONS\
	 * tSIMULATION_STEPS\tFAILED_MERGE_ATTEMPTS\tFAILED_TRANSREMOVE_ATTEMPTS<tt>
	 * where duration is in seconds.
	 * 
	 * @param method
	 *            Used method
	 * @throws AutomataLibraryException
	 *             If a automata library exception occurred.
	 */
	@SuppressWarnings("unchecked")
	private void appendMethodPerformanceToLog(final Object method) throws AutomataLibraryException {
		float duration = -1;
		int removedStates = -1;
		int removedTransitions = -1;
		int simulationSteps = -1;
		int failedMergeAttempts = -1;
		int failedTransRemoveAttempts = -1;
		String methodName = "";
		boolean usesSCCs = false;

		INestedWordAutomatonOldApi<LETTER, STATE> methodResult = null;
		if (method instanceof ASimulation) {
			ASimulation<LETTER, STATE> simulation = (ASimulation<LETTER, STATE>) method;
			SimulationPerformance performance = simulation.getSimulationPerformance();

			// Duration
			long durationInMillis = performance.getTimeMeasureResult(TimeMeasure.OVERALL_TIME,
					MultipleDataOption.ADDITIVE);
			BigDecimal durationAsBigDecimal = new BigDecimal((durationInMillis + 0.0) / SECONDS_TO_MILLIS);
			durationAsBigDecimal = durationAsBigDecimal.setScale(DECIMAL_PLACES, RoundingMode.HALF_UP);
			duration = durationAsBigDecimal.floatValue();

			// Removed states
			removedStates = performance.getCountingMeasureResult(CountingMeasure.REMOVED_STATES);
			// Removed transitions
			removedTransitions = performance.getCountingMeasureResult(CountingMeasure.REMOVED_TRANSITIONS);
			// Simulation steps
			simulationSteps = performance.getCountingMeasureResult(CountingMeasure.SIMULATION_STEPS);
			// Uses SCCs
			usesSCCs = performance.isUsingSCCs();
			// Method name
			methodName = performance.getSimType().toString();
			// Failed merge attempts
			failedMergeAttempts = performance.getCountingMeasureResult(CountingMeasure.FAILED_MERGE_ATTEMPTS);
			// Failed transition removal attempts
			failedTransRemoveAttempts = performance
					.getCountingMeasureResult(CountingMeasure.FAILED_TRANSREMOVE_ATTEMPTS);

		} else if (method instanceof MinimizeSevpa) {
			MinimizeSevpa<LETTER, STATE> minimizeSevpa = (MinimizeSevpa<LETTER, STATE>) method;
			methodResult = minimizeSevpa.getResult();
			// Removed states
			if (methodResult != null) {
				removedStates = m_Operand.size() - methodResult.size();
			}
			// Method name
			methodName = "MinimizeSevpa";
		} else if (method instanceof ShrinkNwa) {
			ShrinkNwa<LETTER, STATE> shrinkNwa = (ShrinkNwa<LETTER, STATE>) method;
			methodResult = (INestedWordAutomatonOldApi<LETTER, STATE>) shrinkNwa.getResult();
			// Removed states
			if (methodResult != null) {
				removedStates = m_Operand.size() - methodResult.size();
			}
			// Method name
			methodName = "ShrinkNwa";
		}

		logLine(methodName + "\t" + usesSCCs + "\t" + duration + "\t" + removedStates + "\t" + removedTransitions + "\t"
				+ simulationSteps + "\t" + failedMergeAttempts + "\t" + failedTransRemoveAttempts);
	}

	/**
	 * Appends the head of the performance format to the log.
	 */
	private void appendPerformanceHeadToLog() {
		logLine("<!--Name\tSCCs\tDuration\tRemoved states\tRemoved transitions\t"
				+ "Simulation steps\tFailed merge attempts\tFailed transremove attempts-->");
	}

	/**
	 * Flushes the internal buffered log messages to a file on the desktop.
	 */
	private void flushLogToFile() {
		File dumpfile = new File(new File(System.getProperty("user.home"), "Desktop"), "simulationPerformanceTest.tsv");
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(dumpfile, true)));
			for (String message : m_LoggedLines) {
				writer.println(message);
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
		m_Logger.info("Logged data to file (" + dumpfile.getAbsolutePath() + ").");
	}

	/**
	 * Flushes the internal buffered log messages to the used logger.
	 */
	@SuppressWarnings("unused")
	private void flushLogToLogger() {
		for (String message : m_LoggedLines) {
			m_Logger.info(message);
		}
	}

	/**
	 * Logs a given message as single line. Uses a internal buffer that needs to
	 * be flushed in order to actually print the logs. Flushing is done by using
	 * {@link #flushLogToLogger()}.
	 * 
	 * @param message
	 *            Message to log
	 */
	private void logLine(final String message) {
		m_LoggedLines.add(message);
	}
}
