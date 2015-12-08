/*
 * Copyright (C) 2015 Layla Franke
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.concurrent.Callable;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * This class manages the parallel computation of minimization by Hopcroft's and
 * Incremental Amr algorithm.
 * 
 * @author Layla Franke
 */
public class MinimizeDfaParallel<LETTER, STATE> extends
		AMinimizeNwa<LETTER, STATE> implements IOperation<LETTER, STATE> {
	/**
	 * Result automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> m_result;
	/**
	 * Getter for result.
	 */
	private Callable<INestedWordAutomaton<LETTER, STATE>> m_resultGetter;
	/**
	 * Input automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_operand;
	/**
	 * Array of threads processing helper tasks.
	 */
	private final ArrayList<WorkingThread> m_threads;
	/**
	 * Blocking queue for Tasks.
	 */
	private final LinkedBlockingQueue<Runnable> m_taskQueue;
	/**
	 * Thread running Hopcroft's Algorithm.
	 */
	private final Thread m_hopcroftThread;
	/**
	 * Thread running the Incremental Algorithm.
	 */
	private final Thread m_incrementalThread;
	/**
	 * Instance of Hopcroft's Algorithm.
	 */
	private MinimizeDfaHopcroftParallel<LETTER, STATE> m_hopcroftAlgorithm;
	/**
	 * Instance of the Incremental Algorithm.
	 */
	private MinimizeDfaAmrParallel<LETTER, STATE> m_incrementalAlgorithm;

	/**
	 * Object for interrupting the incremental algorithm.
	 */
	private final Interrupt m_interrupt;

	
	private boolean m_hopcroftAlgorithmInitialized = false;
	private boolean m_incrementalAlgorithmInitialized = false;

	/**
	 * Sum of run time of all threads in nanoseconds.
	 */
	private double[] m_cpuTime;

	/**
	 * Getter for run time.
	 */
	public double[] getCpuTime() {
		return m_cpuTime;
	}

	/**
	 * String Builder holding the run time of all threads.
	 */
	private StringBuilder m_sb;

	/**
	 * Getter of runtime string builder for testing.
	 */
	public String getRunTime() {
		return m_sb.toString();
	}

	/**
	 * Getter for instance of Hopcroft's algorithm.
	 * 
	 * @return
	 */
	public MinimizeDfaHopcroftParallel<LETTER, STATE> getHopcroft() {
		return m_hopcroftAlgorithm;
	}

	/**
	 * Getter for instance of incremental algorithm.
	 * 
	 * @return
	 */
	public MinimizeDfaAmrParallel<LETTER, STATE> getIncremental() {
		return m_incrementalAlgorithm;
	}

	/**
	 * Preprocessed mappings.
	 */
	private ArrayList<STATE> m_int2state;
	private HashMap<STATE, Integer> m_state2int;

	/**
	 * Switches for setting priority. Setting both to true will have the same
	 * effect as setting both to false. Then they will just all run with the
	 * same priority as the main thread.
	 */
	public static boolean PreferHelperThreads = false;
	public static boolean PreferAlgorithmThreads = false;

	/**
	 * GUI Constructor
	 * 
	 * @param services
	 * @param stateFactory	 
	 * @param operand
	 * 				input automaton (DFA)
	 * @throws AutomataLibraryException
	 * 				thrown when execution is cancelled
	 * @throws AutomataLibraryException
	 * 				thrown by DFA check
	 */
	public MinimizeDfaParallel(final IUltimateServiceProvider services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataLibraryException, AutomataLibraryException {
		this(services, operand);
	}
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 * @param operand
	 * 			input automaton
	 */
	public MinimizeDfaParallel(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "MinimizeDfaParallel",
				operand);
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0) ||
				(operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		
		this.m_operand = operand;
		this.m_interrupt = new Interrupt();

		MinimizeDfaHopcroftParallel.setParallelFlag(true);
		MinimizeDfaAmrParallel.setParallelFlag(true);

		m_hopcroftThread = new AlgorithmTask(this, Algorithm.Hopcroft);
		m_incrementalThread = new AlgorithmTask(this, Algorithm.Incremental);

		// Initialize Data.
		initialize();

		// Create queue
		m_taskQueue = new LinkedBlockingQueue<Runnable>();
		
		//final int processors = Runtime.getRuntime().availableProcessors();
		final int processors = 6;
		m_threads = new ArrayList<WorkingThread>();
		for (int i = 0; i < Math.max(1, processors - 2); i++) {
			m_threads.add(new WorkingThread("HelperThread" + i));
			m_threads.get(i).start();
		}
		s_logger.info("MAIN: Start execution of Incremental algorithm.");
		m_incrementalThread.start();
		s_logger.info("MAIN: Start execution of Hopcroft algorithm.");
		m_hopcroftThread.start();

		synchronized (this) {
			if (m_result == null) {
				try {
					this.wait();
				} catch (InterruptedException e) {
					//e.printStackTrace();
				}
			}
		}

		// Interrupt all threads
		s_logger.info("MAIN: Result available. Start interrupting working threads.");
		measureTime();

		for (Thread thread : m_threads) {
			thread.interrupt();
		}
		synchronized (m_incrementalThread) {
			m_incrementalThread.notify();
		}
		synchronized (m_hopcroftThread) {
			m_hopcroftThread.notify();
		}
		// End execution of both algorithms.
		m_incrementalThread.interrupt();
		m_hopcroftThread.interrupt();
		m_interrupt.setStatus();
		s_logger.info("MAIN: Interrupting working threads finished.");

		s_logger.info("MAIN: Start postprocessing result.");
		try {
			m_result = m_resultGetter.call();
		} catch (Exception e) {
			//e.printStackTrace();
		}

		m_sb = createConsoleOutput();
		s_logger.info(m_sb);

		// Set parallel flags of both algorithms to false again.
		MinimizeDfaHopcroftParallel.setParallelFlag(false);
		MinimizeDfaAmrParallel.setParallelFlag(false);
		s_logger.info("MAIN: " + exitMessage());
	}

	/**
	 * Measure CPU Time of all Threads.
	 * 
	 * @return Array that holds the cpu times of all threads except for the main
	 *         thread.
	 */
	private void measureTime() {
		m_cpuTime = new double[m_threads.size() + 2];
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		for (int i = 0; i < m_threads.size(); i++) {
			m_cpuTime[i] = bean.getThreadCpuTime(m_threads.get(i).getId());
		}
		m_cpuTime[m_threads.size()] = bean.getThreadCpuTime(m_incrementalThread
				.getId());
		m_cpuTime[m_threads.size() + 1] = bean
				.getThreadCpuTime(m_hopcroftThread.getId());
	}

	/**
	 * Create formatted output of CPU times.
	 * 
	 * @return Formatted output.
	 */
	private StringBuilder createConsoleOutput() {
		StringBuilder sb = new StringBuilder();
		sb.append("CPU TIME needed for computation:\n");

		for (int j = 0; j < m_threads.size(); j++) {

			sb.append("Thread " + (j + 1) + ": " + m_cpuTime[j] + "ns\n");

		}
		sb.append("Incremental Thread: " + m_cpuTime[m_threads.size()] + "ns\n");
		sb.append("Hopcroft Thread: " + m_cpuTime[m_threads.size() + 1]
				+ "ns\n");

		long sum = 0;
		for (double i : m_cpuTime) {
			sum += i;
		}

		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		long cpuTime = bean.getThreadCpuTime(Thread.currentThread().getId());
		sum += cpuTime;
		sb.append("Main Thread: " + cpuTime + "ns\n" + "TOTAL: " + sum + "ns"
				+ " = " + sum / Math.pow(10, 9) + "sec");

		return sb;
	}

	/**
	 * Initialize mappings from state to int.
	 */
	private void initialize() {
		int nOfStates = m_operand.getStates().size();
		// Allocate the finite space in ArrayList and HashMap.
		m_int2state = new ArrayList<STATE>(nOfStates);
		m_state2int = new HashMap<STATE, Integer>(nOfStates);
		int index = -1;
		for (final STATE state : m_operand.getStates()) {
			m_int2state.add(state);
			m_state2int.put(state, ++index);
		}
	}

	// ------------------- WorkingThread --------------------//
	/**
	 * This class defines the worker threads that make up the thread pool. A
	 * WorkerThread runs in a loop in which it retrieves a task from the
	 * taskQueue and calls the run() method in that task. Note that if the queue
	 * is empty, the thread blocks until a task becomes available in the queue.
	 * The constructor starts the thread, so there is no need for the main
	 * program to do so. The thread will run at a priority that is one less than
	 * the priority of the thread that calls the constructor.
	 * 
	 * A WorkerThread is designed to run in an infinite loop. It will end only
	 * when the Java virtual machine exits. (This assumes that the tasks that
	 * are executed don't throw exceptions, which is true in this program.) The
	 * constructor sets the thread to run as a daemon thread; the Java virtual
	 * machine will exit when the only threads are daemon threads. (In this
	 * program, this is not necessary since the virtual machine is set to exit
	 * when the window is closed. In a multi-window program, however, that would
	 * not be the case and it would be important for the threads to be daemon
	 * threads.)
	 */
	private class WorkingThread extends Thread {

		/**
		 * Creating the thread.
		 * 
		 * @param name
		 */
		WorkingThread(final String name) {
			super(name);
			try {
				if (PreferHelperThreads && !PreferAlgorithmThreads) {
					setPriority(Thread.MAX_PRIORITY);
				} else if (!PreferHelperThreads && PreferAlgorithmThreads) {
					setPriority(Thread.MIN_PRIORITY);
				}
			} catch (Exception e) {
				//e.printStackTrace();
			}
			try {
				setDaemon(true);
			} catch (Exception e) {
				//e.printStackTrace();
			}
		}

		@Override
		public void run() {
			while (!this.isInterrupted()) {
				try {
					assert (!this.isInterrupted());
					Runnable task = m_taskQueue.take();
					if (!this.isInterrupted()) {
						task.run();
					}
					s_logger.info("MAIN: Size of task queue: "
							+ m_taskQueue.size());
				} catch (InterruptedException e) {
					this.interrupt();
				}
			}
		}
	}

	// -------------- Algorithm Tasks -------------//
	/**
	 * The algorithm task is a thread that performs a given algorithm for
	 * minimizing DFA.
	 * 
	 * @author layla
	 */
	private class AlgorithmTask extends Thread implements
			IOperation<LETTER, STATE> {
		/**
		 * Reference to main thread for setting result.
		 */
		private final MinimizeDfaParallel<LETTER, STATE> m_mainThread;
		/**
		 * Parameter for deciding on which algorithm to run.
		 */
		private final Algorithm m_chooseAlgorithm;
		/**
		 * Instance of running algorithm.
		 */
		private IMinimize m_algorithm;

		/**
		 * Constructor for a thread processing a minimization algorithm.
		 * 
		 * @param mainThread
		 *            The calling instance.
		 * @param algorithm
		 *            The algorithm to run.
		 */
		AlgorithmTask(final MinimizeDfaParallel<LETTER, STATE> mainThread,
				final Algorithm algorithm) {
			super(algorithm.toString());
			m_chooseAlgorithm = algorithm;
			m_mainThread = mainThread;

			try {
				if (!PreferAlgorithmThreads && PreferHelperThreads) {
					setPriority(Thread.MIN_PRIORITY);
				} else if (PreferAlgorithmThreads && !PreferHelperThreads) {
					setPriority(Thread.MAX_PRIORITY);
				}
			} catch (Exception e) {
				assert (false);
			}
			try {
				setDaemon(true);
			} catch (Exception e) {
				//e.printStackTrace();
			}
		}

		@Override
		public void run() {
			try {
				if (m_chooseAlgorithm.equals(Algorithm.Hopcroft)) {

					s_logger.info("moep1");
					m_algorithm = new MinimizeDfaHopcroftParallel<LETTER, STATE>(
							m_Services, m_operand.getStateFactory(),
							(INestedWordAutomaton<LETTER, STATE>) m_operand,
							m_interrupt, m_int2state, m_state2int);

					if (isInterrupted()) {
						return;
					}
					s_logger.info("moep2");
					m_hopcroftAlgorithm = (MinimizeDfaHopcroftParallel) m_algorithm;
					m_hopcroftAlgorithmInitialized = true;

					synchronized (m_interrupt) {
						if (m_incrementalAlgorithmInitialized) {
							s_logger.info("moep3a");
							synchronized (m_incrementalAlgorithm) {
								m_interrupt.notify();
							}
						} else {
							s_logger.info("moep3b");
							m_interrupt.wait();
						}
					}
					s_logger.info("moep4");
					m_hopcroftAlgorithm.minimizeParallel(m_taskQueue,
							m_incrementalAlgorithm);
					s_logger.info("moep5");

				} else {
					s_logger.info("miep1");
					m_algorithm = new MinimizeDfaAmrParallel<LETTER, STATE>(
							m_Services, m_operand.getStateFactory(), m_operand,
							m_interrupt, m_int2state, m_state2int);

					if (isInterrupted()) {
						return;
					}
					s_logger.info("miep2");
					m_incrementalAlgorithm = (MinimizeDfaAmrParallel) m_algorithm;
					m_incrementalAlgorithmInitialized = true;
					synchronized (m_interrupt) {
						if (m_hopcroftAlgorithmInitialized) {
							s_logger.info("miep3a");
							m_interrupt.notify();
						} else {
							s_logger.info("miep3b");

							m_interrupt.wait();
						}
					}
					s_logger.info("miep4");
					m_incrementalAlgorithm.minimizeParallel(m_taskQueue,
							m_hopcroftAlgorithm);
					s_logger.info("miep5");
				}

				if (isInterrupted()) {
					return;
				}
				
				synchronized (m_mainThread) {
					if (m_resultGetter == null) {
						m_resultGetter = new Callable<INestedWordAutomaton<LETTER, STATE>>() {
							public INestedWordAutomaton<LETTER, STATE> call() {
								return (INestedWordAutomaton<LETTER, STATE>) m_algorithm
										.getResult();
							}
						};
						m_mainThread.notify();
					}
				}
				synchronized (this) {
					this.wait();
				}

			} catch (AutomataLibraryException e) {
				throw new AssertionError("unhandeled AutomataLibraryException");
			} catch (InterruptedException e) {
				//e.printStackTrace();
			}
		}

		@Override
		public String operationName() {
			return m_algorithm.operationName();
		}

		@Override
		public String startMessage() {
			return m_algorithm.startMessage();
		}

		@Override
		public String exitMessage() {
			return m_algorithm.exitMessage();
		}

		@Override
		public Object getResult() throws AutomataLibraryException {
			return m_algorithm.getResult();
		}

		@Override
		public boolean checkResult(StateFactory<STATE> stateFactory)
				throws AutomataLibraryException {
			// TODO Implement method.
			return true;
		}
	}

	// ------------ Enum ------------ //

	/**
	 * Enum for choosing the algorithm to run in AlgorithmTasks.
	 * 
	 * @author layla
	 *
	 */
	private enum Algorithm {
		Hopcroft, Incremental
	}

	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_result;
	}
}
