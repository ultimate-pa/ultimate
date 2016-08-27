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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.parallel;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.concurrent.Callable;
import java.util.concurrent.LinkedBlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.AbstractMinimizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.Interrupt;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * This class manages the parallel computation of minimization by Hopcroft's and
 * Incremental AMR algorithm.
 * 
 * @author Layla Franke
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public final class MinimizeDfaParallel<LETTER, STATE>
		extends AbstractMinimizeNwa<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * Whether the result is constructed yet.
	 */
	private boolean mResultConstructed = false;
	/**
	 * Getter for result.
	 */
	private Callable<INestedWordAutomaton<LETTER, STATE>> mResultGetter;
	/**
	 * Array of threads processing helper tasks.
	 */
	private final ArrayList<WorkingThread> mThreads;
	/**
	 * Blocking queue for Tasks.
	 */
	private final LinkedBlockingQueue<Runnable> mTaskQueue;
	/**
	 * Thread running Hopcroft's Algorithm.
	 */
	private final Thread mHopcroftThread;
	/**
	 * Thread running the Incremental Algorithm.
	 */
	private final Thread mIncrementalThread;
	/**
	 * Instance of Hopcroft's Algorithm.
	 */
	private MinimizeDfaHopcroftParallel<LETTER, STATE> mHopcroftAlgorithm;
	/**
	 * Instance of the Incremental Algorithm.
	 */
	private MinimizeDfaIncrementalParallel<LETTER, STATE> mIncrementalAlgorithm;

	/**
	 * Object for interrupting the incremental algorithm.
	 */
	private final Interrupt mInterrupt;

	
	private boolean mHopcroftAlgorithmInitialized = false;
	private boolean mIncrementalAlgorithmInitialized = false;

	/**
	 * Sum of run time of all threads in nanoseconds.
	 */
	private double[] mCpuTime;

	/**
	 * String Builder holding the run time of all threads.
	 */
	private final StringBuilder mSb;

	/**
	 * Preprocessed mappings.
	 */
	private ArrayList<STATE> mInt2state;
	private HashMap<STATE, Integer> mState2int;

	/**
	 * Switches for setting priority. Setting both to true will have the same
	 * effect as setting both to false. Then they will just all run with the
	 * same priority as the main thread.
	 */
	public static final boolean PREFER_HELPER_THREADS = false;
	public static final boolean PREFER_ALGORITHM_THREADS = false;

	
	/**
	 * Constructor.
	 * 
	 * @param services Ultimave services
	 * @param stateFactory state factory
	 * @param operand
	 * 			input automaton
	 */
	public MinimizeDfaParallel(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, stateFactory, "MinimizeDfaParallel", operand);
		
		// added by Christian
		if ((operand.getCallAlphabet().size() > 0)
				|| (operand.getReturnAlphabet().size() > 0)) {
			throw new UnsupportedOperationException(
				"This class only supports minimization of finite automata.");
		}
		
		this.mInterrupt = new Interrupt();

		MinimizeDfaHopcroftParallel.setParallelFlag(true);
		MinimizeDfaIncrementalParallel.setParallelFlag(true);

		mHopcroftThread = new AlgorithmTask(this, Algorithm.HOPCROFT);
		mIncrementalThread = new AlgorithmTask(this, Algorithm.INCREMENTAL);

		// Initialize Data.
		initialize();

		// Create queue
		mTaskQueue = new LinkedBlockingQueue<Runnable>();
		
		//final int processors = Runtime.getRuntime().availableProcessors();
		final int processors = 6;
		mThreads = new ArrayList<WorkingThread>();
		for (int i = 0; i < Math.max(1, processors - 2); i++) {
			mThreads.add(new WorkingThread("HelperThread" + i));
			mThreads.get(i).start();
		}
		mLogger.info("MAIN: Start execution of Incremental algorithm.");
		mIncrementalThread.start();
		mLogger.info("MAIN: Start execution of Hopcroft algorithm.");
		mHopcroftThread.start();

		synchronized (this) {
			if (! mResultConstructed) {
				try {
					this.wait();
				} catch (final InterruptedException e) {
					//e.printStackTrace();
				}
			}
		}

		// Interrupt all threads
		mLogger.info("MAIN: Result available. Start interrupting working threads.");
		measureTime();

		for (final Thread thread : mThreads) {
			thread.interrupt();
		}
		synchronized (mIncrementalThread) {
			mIncrementalThread.notify();
		}
		synchronized (mHopcroftThread) {
			mHopcroftThread.notify();
		}
		// End execution of both algorithms.
		mIncrementalThread.interrupt();
		mHopcroftThread.interrupt();
		mInterrupt.setStatus();
		mLogger.info("MAIN: Interrupting working threads finished.");

		mLogger.info("MAIN: Start postprocessing result.");
		try {
			directResultConstruction(mResultGetter.call());
			mResultConstructed = true;
		} catch (final Exception e) {
			//e.printStackTrace();
		}

		mSb = createConsoleOutput();
		mLogger.info(mSb);

		// Set parallel flags of both algorithms to false again.
		MinimizeDfaHopcroftParallel.setParallelFlag(false);
		MinimizeDfaIncrementalParallel.setParallelFlag(false);
		mLogger.info("MAIN: " + exitMessage());
	}

	/**
	 * Getter for run time.
	 */
	public double[] getCpuTime() {
		return mCpuTime;
	}

	/**
	 * Getter of runtime string builder for testing.
	 */
	public String getRunTime() {
		return mSb.toString();
	}

	/**
	 * Getter for instance of Hopcroft's algorithm.
	 */
	public MinimizeDfaHopcroftParallel<LETTER, STATE> getHopcroft() {
		return mHopcroftAlgorithm;
	}

	/**
	 * Getter for instance of incremental algorithm.
	 */
	public MinimizeDfaIncrementalParallel<LETTER, STATE> getIncremental() {
		return mIncrementalAlgorithm;
	}

	/**
	 * Measure CPU Time of all Threads.
	 * 
	 * @return Array that holds the cpu times of all threads except for the main
	 *         thread.
	 */
	private void measureTime() {
		mCpuTime = new double[mThreads.size() + 2];
		final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		for (int i = 0; i < mThreads.size(); i++) {
			mCpuTime[i] = bean.getThreadCpuTime(mThreads.get(i).getId());
		}
		mCpuTime[mThreads.size()] = bean.getThreadCpuTime(mIncrementalThread
				.getId());
		mCpuTime[mThreads.size() + 1] = bean
				.getThreadCpuTime(mHopcroftThread.getId());
	}

	/**
	 * Create formatted output of CPU times.
	 * 
	 * @return Formatted output.
	 */
	private StringBuilder createConsoleOutput() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CPU TIME needed for computation:\n");

		for (int j = 0; j < mThreads.size(); j++) {

			sb.append("Thread " + (j + 1) + ": " + mCpuTime[j] + "ns\n");

		}
		sb.append("Incremental Thread: " + mCpuTime[mThreads.size()] + "ns\n");
		sb.append("Hopcroft Thread: " + mCpuTime[mThreads.size() + 1]
				+ "ns\n");

		long sum = 0;
		for (final double i : mCpuTime) {
			sum += i;
		}

		final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		final long cpuTime = bean.getThreadCpuTime(Thread.currentThread().getId());
		sum += cpuTime;
		sb.append("Main Thread: " + cpuTime + "ns\n" + "TOTAL: " + sum + "ns"
				+ " = " + sum / Math.pow(10, 9) + "sec");

		return sb;
	}

	/**
	 * Initialize mappings from state to int.
	 */
	private void initialize() {
		final int nOfStates = mOperand.size();
		// Allocate the finite space in ArrayList and HashMap.
		mInt2state = new ArrayList<STATE>(nOfStates);
		mState2int = new HashMap<STATE, Integer>(nOfStates);
		int index = -1;
		for (final STATE state : mOperand.getStates()) {
			mInt2state.add(state);
			mState2int.put(state, ++index);
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
	 * <p>A WorkerThread is designed to run in an infinite loop. It will end only
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
		 * @param name name
		 */
		WorkingThread(final String name) {
			super(name);
			try {
				if (PREFER_HELPER_THREADS && !PREFER_ALGORITHM_THREADS) {
					setPriority(Thread.MAX_PRIORITY);
				} else if (!PREFER_HELPER_THREADS && PREFER_ALGORITHM_THREADS) {
					setPriority(Thread.MIN_PRIORITY);
				}
			} catch (final Exception e) {
				//e.printStackTrace();
			}
			try {
				setDaemon(true);
			} catch (final Exception e) {
				//e.printStackTrace();
			}
		}

		@Override
		public void run() {
			while (!isInterrupted()) {
				try {
					assert (!isInterrupted());
					final Runnable task = mTaskQueue.take();
					if (!isInterrupted()) {
						task.run();
					}
					mLogger.info("MAIN: Size of task queue: "
							+ mTaskQueue.size());
				} catch (final InterruptedException e) {
					interrupt();
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
	private class AlgorithmTask extends Thread {
		/**
		 * Reference to main thread for setting result.
		 */
		private final MinimizeDfaParallel<LETTER, STATE> mMainThread;
		/**
		 * Parameter for deciding on which algorithm to run.
		 */
		private final Algorithm mChooseAlgorithm;
		/**
		 * Instance of running algorithm.
		 */
		private IMinimize mAlgorithm;

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
			mChooseAlgorithm = algorithm;
			mMainThread = mainThread;

			try {
				if (!PREFER_ALGORITHM_THREADS && PREFER_HELPER_THREADS) {
					setPriority(Thread.MIN_PRIORITY);
				} else if (PREFER_ALGORITHM_THREADS && !PREFER_HELPER_THREADS) {
					setPriority(Thread.MAX_PRIORITY);
				}
			} catch (final Exception e) {
				assert (false);
			}
			try {
				setDaemon(true);
			} catch (final Exception e) {
				//e.printStackTrace();
			}
		}

		@SuppressWarnings("unchecked")
		@Override
		public void run() {
			try {
				if (mChooseAlgorithm.equals(Algorithm.HOPCROFT)) {

					mLogger.debug("moep1");
					mAlgorithm = new MinimizeDfaHopcroftParallel<LETTER, STATE>(
							mServices, mOperand.getStateFactory(),
							mOperand,
							mInterrupt, mInt2state, mState2int);

					if (isInterrupted()) {
						return;
					}
					mLogger.debug("moep2");
					mHopcroftAlgorithm = (MinimizeDfaHopcroftParallel<LETTER, STATE>) mAlgorithm;
					mHopcroftAlgorithmInitialized = true;

					synchronized (mInterrupt) {
						if (mIncrementalAlgorithmInitialized) {
							mLogger.debug("moep3a");
							synchronized (mIncrementalAlgorithm) {
								mInterrupt.notify();
							}
						} else {
							mLogger.debug("moep3b");
							mInterrupt.wait();
						}
					}
					mLogger.debug("moep4");
					mHopcroftAlgorithm.minimizeParallel(mTaskQueue,
							mIncrementalAlgorithm);
					mLogger.debug("moep5");

				} else {
					mLogger.debug("miep1");
					mAlgorithm = new MinimizeDfaIncrementalParallel<LETTER, STATE>(
							mServices, mOperand.getStateFactory(), mOperand,
							mInterrupt, mInt2state, mState2int);

					if (isInterrupted()) {
						return;
					}
					mLogger.debug("miep2");
					mIncrementalAlgorithm = (MinimizeDfaIncrementalParallel<LETTER, STATE>) mAlgorithm;
					mIncrementalAlgorithmInitialized = true;
					synchronized (mInterrupt) {
						if (mHopcroftAlgorithmInitialized) {
							mLogger.debug("miep3a");
							mInterrupt.notify();
						} else {
							mLogger.debug("miep3b");

							mInterrupt.wait();
						}
					}
					mLogger.debug("miep4");
					mIncrementalAlgorithm.minimizeParallel(mTaskQueue,
							mHopcroftAlgorithm);
					mLogger.debug("miep5");
				}

				if (isInterrupted()) {
					return;
				}
				
				synchronized (mMainThread) {
					if (mResultGetter == null) {
						mResultGetter = new Callable<INestedWordAutomaton<LETTER, STATE>>() {
							@Override
							public INestedWordAutomaton<LETTER, STATE> call() {
								return (INestedWordAutomaton<LETTER, STATE>) mAlgorithm
										.getResult();
							}
						};
						mMainThread.notify();
					}
				}
				synchronized (this) {
					this.wait();
				}

			} catch (final AutomataLibraryException e) {
				throw new AssertionError("unhandeled AutomataLibraryException");
			} catch (final InterruptedException e) {
				//e.printStackTrace();
			}
		}
	}

	// ------------ Enum ------------ //

	/**
	 * Enum for choosing the algorithm to run in AlgorithmTasks.
	 */
	private enum Algorithm {
		HOPCROFT, INCREMENTAL
	}
}
