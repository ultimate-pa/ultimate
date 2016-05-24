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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.parallel;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.concurrent.Callable;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.AMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.Interrupt;

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
	private INestedWordAutomaton<LETTER, STATE> mresult;
	/**
	 * Getter for result.
	 */
	private Callable<INestedWordAutomaton<LETTER, STATE>> mresultGetter;
	/**
	 * Input automaton.
	 */
	private final INestedWordAutomaton<LETTER, STATE> moperand;
	/**
	 * Array of threads processing helper tasks.
	 */
	private final ArrayList<WorkingThread> mthreads;
	/**
	 * Blocking queue for Tasks.
	 */
	private final LinkedBlockingQueue<Runnable> mtaskQueue;
	/**
	 * Thread running Hopcroft's Algorithm.
	 */
	private final Thread mhopcroftThread;
	/**
	 * Thread running the Incremental Algorithm.
	 */
	private final Thread mincrementalThread;
	/**
	 * Instance of Hopcroft's Algorithm.
	 */
	private MinimizeDfaHopcroftParallel<LETTER, STATE> mhopcroftAlgorithm;
	/**
	 * Instance of the Incremental Algorithm.
	 */
	private MinimizeDfaAmrParallel<LETTER, STATE> mincrementalAlgorithm;

	/**
	 * Object for interrupting the incremental algorithm.
	 */
	private final Interrupt minterrupt;

	
	private boolean mhopcroftAlgorithmInitialized = false;
	private boolean mincrementalAlgorithmInitialized = false;

	/**
	 * Sum of run time of all threads in nanoseconds.
	 */
	private double[] mcpuTime;

	/**
	 * Getter for run time.
	 */
	public double[] getCpuTime() {
		return mcpuTime;
	}

	/**
	 * String Builder holding the run time of all threads.
	 */
	private StringBuilder msb;

	/**
	 * Getter of runtime string builder for testing.
	 */
	public String getRunTime() {
		return msb.toString();
	}

	/**
	 * Getter for instance of Hopcroft's algorithm.
	 * 
	 * @return
	 */
	public MinimizeDfaHopcroftParallel<LETTER, STATE> getHopcroft() {
		return mhopcroftAlgorithm;
	}

	/**
	 * Getter for instance of incremental algorithm.
	 * 
	 * @return
	 */
	public MinimizeDfaAmrParallel<LETTER, STATE> getIncremental() {
		return mincrementalAlgorithm;
	}

	/**
	 * Preprocessed mappings.
	 */
	private ArrayList<STATE> mint2state;
	private HashMap<STATE, Integer> mstate2int;

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
	public MinimizeDfaParallel(final AutomataLibraryServices services,
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
	public MinimizeDfaParallel(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "MinimizeDfaParallel",
				operand);
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0) ||
				(operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		
		this.moperand = operand;
		this.minterrupt = new Interrupt();

		MinimizeDfaHopcroftParallel.setParallelFlag(true);
		MinimizeDfaAmrParallel.setParallelFlag(true);

		mhopcroftThread = new AlgorithmTask(this, Algorithm.Hopcroft);
		mincrementalThread = new AlgorithmTask(this, Algorithm.Incremental);

		// Initialize Data.
		initialize();

		// Create queue
		mtaskQueue = new LinkedBlockingQueue<Runnable>();
		
		//final int processors = Runtime.getRuntime().availableProcessors();
		final int processors = 6;
		mthreads = new ArrayList<WorkingThread>();
		for (int i = 0; i < Math.max(1, processors - 2); i++) {
			mthreads.add(new WorkingThread("HelperThread" + i));
			mthreads.get(i).start();
		}
		s_logger.info("MAIN: Start execution of Incremental algorithm.");
		mincrementalThread.start();
		s_logger.info("MAIN: Start execution of Hopcroft algorithm.");
		mhopcroftThread.start();

		synchronized (this) {
			if (mresult == null) {
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

		for (Thread thread : mthreads) {
			thread.interrupt();
		}
		synchronized (mincrementalThread) {
			mincrementalThread.notify();
		}
		synchronized (mhopcroftThread) {
			mhopcroftThread.notify();
		}
		// End execution of both algorithms.
		mincrementalThread.interrupt();
		mhopcroftThread.interrupt();
		minterrupt.setStatus();
		s_logger.info("MAIN: Interrupting working threads finished.");

		s_logger.info("MAIN: Start postprocessing result.");
		try {
			mresult = mresultGetter.call();
		} catch (Exception e) {
			//e.printStackTrace();
		}

		msb = createConsoleOutput();
		s_logger.info(msb);

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
		mcpuTime = new double[mthreads.size() + 2];
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		for (int i = 0; i < mthreads.size(); i++) {
			mcpuTime[i] = bean.getThreadCpuTime(mthreads.get(i).getId());
		}
		mcpuTime[mthreads.size()] = bean.getThreadCpuTime(mincrementalThread
				.getId());
		mcpuTime[mthreads.size() + 1] = bean
				.getThreadCpuTime(mhopcroftThread.getId());
	}

	/**
	 * Create formatted output of CPU times.
	 * 
	 * @return Formatted output.
	 */
	private StringBuilder createConsoleOutput() {
		StringBuilder sb = new StringBuilder();
		sb.append("CPU TIME needed for computation:\n");

		for (int j = 0; j < mthreads.size(); j++) {

			sb.append("Thread " + (j + 1) + ": " + mcpuTime[j] + "ns\n");

		}
		sb.append("Incremental Thread: " + mcpuTime[mthreads.size()] + "ns\n");
		sb.append("Hopcroft Thread: " + mcpuTime[mthreads.size() + 1]
				+ "ns\n");

		long sum = 0;
		for (double i : mcpuTime) {
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
		int nOfStates = moperand.getStates().size();
		// Allocate the finite space in ArrayList and HashMap.
		mint2state = new ArrayList<STATE>(nOfStates);
		mstate2int = new HashMap<STATE, Integer>(nOfStates);
		int index = -1;
		for (final STATE state : moperand.getStates()) {
			mint2state.add(state);
			mstate2int.put(state, ++index);
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
					Runnable task = mtaskQueue.take();
					if (!this.isInterrupted()) {
						task.run();
					}
					s_logger.info("MAIN: Size of task queue: "
							+ mtaskQueue.size());
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
		private final MinimizeDfaParallel<LETTER, STATE> mmainThread;
		/**
		 * Parameter for deciding on which algorithm to run.
		 */
		private final Algorithm mchooseAlgorithm;
		/**
		 * Instance of running algorithm.
		 */
		private IMinimize malgorithm;

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
			mchooseAlgorithm = algorithm;
			mmainThread = mainThread;

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
				if (mchooseAlgorithm.equals(Algorithm.Hopcroft)) {

					s_logger.info("moep1");
					malgorithm = new MinimizeDfaHopcroftParallel<LETTER, STATE>(
							mServices, moperand.getStateFactory(),
							(INestedWordAutomaton<LETTER, STATE>) moperand,
							minterrupt, mint2state, mstate2int);

					if (isInterrupted()) {
						return;
					}
					s_logger.info("moep2");
					mhopcroftAlgorithm = (MinimizeDfaHopcroftParallel) malgorithm;
					mhopcroftAlgorithmInitialized = true;

					synchronized (minterrupt) {
						if (mincrementalAlgorithmInitialized) {
							s_logger.info("moep3a");
							synchronized (mincrementalAlgorithm) {
								minterrupt.notify();
							}
						} else {
							s_logger.info("moep3b");
							minterrupt.wait();
						}
					}
					s_logger.info("moep4");
					mhopcroftAlgorithm.minimizeParallel(mtaskQueue,
							mincrementalAlgorithm);
					s_logger.info("moep5");

				} else {
					s_logger.info("miep1");
					malgorithm = new MinimizeDfaAmrParallel<LETTER, STATE>(
							mServices, moperand.getStateFactory(), moperand,
							minterrupt, mint2state, mstate2int);

					if (isInterrupted()) {
						return;
					}
					s_logger.info("miep2");
					mincrementalAlgorithm = (MinimizeDfaAmrParallel) malgorithm;
					mincrementalAlgorithmInitialized = true;
					synchronized (minterrupt) {
						if (mhopcroftAlgorithmInitialized) {
							s_logger.info("miep3a");
							minterrupt.notify();
						} else {
							s_logger.info("miep3b");

							minterrupt.wait();
						}
					}
					s_logger.info("miep4");
					mincrementalAlgorithm.minimizeParallel(mtaskQueue,
							mhopcroftAlgorithm);
					s_logger.info("miep5");
				}

				if (isInterrupted()) {
					return;
				}
				
				synchronized (mmainThread) {
					if (mresultGetter == null) {
						mresultGetter = new Callable<INestedWordAutomaton<LETTER, STATE>>() {
							public INestedWordAutomaton<LETTER, STATE> call() {
								return (INestedWordAutomaton<LETTER, STATE>) malgorithm
										.getResult();
							}
						};
						mmainThread.notify();
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
			return malgorithm.operationName();
		}

		@Override
		public String startMessage() {
			return malgorithm.startMessage();
		}

		@Override
		public String exitMessage() {
			return malgorithm.exitMessage();
		}

		@Override
		public Object getResult() throws AutomataLibraryException {
			return malgorithm.getResult();
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
		return mresult;
	}
}
