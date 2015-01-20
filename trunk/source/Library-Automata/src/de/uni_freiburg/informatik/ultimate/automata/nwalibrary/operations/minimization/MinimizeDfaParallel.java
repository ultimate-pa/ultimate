package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.concurrent.LinkedBlockingQueue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

// TODO STATE->int, int->STATE only once -> optimize?
// TODO Generic constructor for Inc and Hopcroft?

// TODO Test with big input
// TODO What about the state factory for the constructors? Does it work like that?

/**
 * This class manages the parallel computation of minimization by Hopcroft's and
 * Incremental Amr algorithm.
 * 
 * @author Layla Franke
 */
public class MinimizeDfaParallel<LETTER, STATE> extends
		AMinimizeNwa<LETTER, STATE> implements IOperation<LETTER, STATE> {
	/**
	 * The logger.
	 */
	protected static final Logger s_logger = NestedWordAutomata.getLogger();
	/**
	 * Service Provider.
	 */
	private final IUltimateServiceProvider m_services;
	/**
	 * Result automaton.
	 */
	private INestedWordAutomaton<LETTER, STATE> m_result;
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
	 * Holds cpu time of finishing thread.
	 */
	private long m_cpuTime;

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            the input automaton
	 */
	public MinimizeDfaParallel(final IUltimateServiceProvider services, final INestedWordAutomaton<LETTER, STATE> operand) {
		super(services, operand.getStateFactory(), "MinimizeDfaParallel", operand);
		this.m_services=services;
		this.m_operand = operand;
		this.m_interrupt = new Interrupt();
		m_hopcroftThread = new AlgorithmTask(this, Algorithm.Hopcroft);
		m_incrementalThread = new AlgorithmTask(this, Algorithm.Incremental);
		// Create queue
		m_taskQueue = new LinkedBlockingQueue<Runnable>();
		final int processors = Runtime.getRuntime().availableProcessors();
		m_threads = new ArrayList<WorkingThread>();
		for (int i = 0; i < Math.max(1, processors - 2); i++) {
			m_threads.add(new WorkingThread("HelperThread" + i));
			m_threads.get(i).start();
		}
		m_hopcroftThread.start();
		s_logger.info("MAIN: Started execution of Hopcroft algorithm.");
		m_incrementalThread.start();
		s_logger.info("MAIN: Started execution of Incremental algorithm.");
		StringBuilder sb = new StringBuilder();
		long sum;
		synchronized (this) {
			if (m_result == null) {
				try {
					this.wait();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
			// Interrupt all threads - This should happen after the result was
			// written by some thread and before any other thread can lock the
			// result.
			s_logger.info("MAIN: Result available. Start interrupting working threads.");
			// TODO Maybe do this in own thread for higher accuracy
			sum = measureTime(sb);
			for (Thread thread : m_threads) {
				thread.interrupt();
			}
			s_logger.info("MAIN: Interrupting working threads finished.");

		}
		// End execution of incremental algorithm.
		m_incrementalThread.interrupt();
		// End execution of both algorithms.
		m_hopcroftThread.interrupt();
		m_interrupt.setStatus();
		// Try to join each of the threads.
		try {
			m_incrementalThread.join();
		} catch (InterruptedException e) {
			// e.printStackTrace();
		}
		try {
			m_hopcroftThread.join();
		} catch (InterruptedException e) {
			// e.printStackTrace();
		}

		// Set parallel flags of both algorithms to false again.
		MinimizeDfaHopcroftParallel.setParallelFlag(false);
		MinimizeDfaAmrParallel.setParallelFlag(false);
		/*
		 * ThreadMXBean.getThreadCPUTime() can help you find out how much CPU
		 * time a given thread has used. Use ManagementFactory.getThreadMXBean()
		 * to get a ThreadMXBean and Thread.getId() to find the id of the thread
		 * you're interested in.
		 */
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		long cpuTime = bean.getThreadCpuTime(Thread.currentThread().getId());
		sum += cpuTime;
		sb.append("Main Thread: " + cpuTime + "ns\n" + "TOTAL: " + sum + "ns"
				+ " = " + sum / Math.pow(10, 9) + "sec");
		s_logger.info(sb);
		s_logger.info("MAIN: " + exitMessage());
	}

	/**
	 * Measure CPU Time of all Threads.
	 * 
	 * @return Formatted output.
	 */
	private long measureTime(StringBuilder sb) {
		long[] ids = new long[m_threads.size() + 2];
		ThreadMXBean bean = ManagementFactory.getThreadMXBean();
		Thread thread;
		for (int i = 0; i < m_threads.size(); i++) {
			thread = m_threads.get(i);
			ids[i] = thread.getId();
		}
		ids[ids.length - 1] = m_hopcroftThread.getId();
		ids[ids.length - 2] = m_incrementalThread.getId();
		sb.append("CPU TIME needed for computation:\n");
		long sum = 0;
		for (int j = 0; j < ids.length; j++) {
			long cpuTime = bean.getThreadCpuTime(ids[j]);
			if (ids[j] == m_hopcroftThread.getId()) {
				sb.append("Hopcroft Thread: ");
			} else if (ids[j] == m_incrementalThread.getId()) {
				sb.append("Incremental Thread: ");
				// } else if (ids[j] == Thread.currentThread().getId()) {
				// sb.append("Main Thread: ");
			} else {
				sb.append("Thread " + (j + 1) + ": ");
			}
			if (cpuTime == -1) {
				cpuTime = m_cpuTime;
			}
			sb.append(cpuTime + "ns\n");
			sum += cpuTime;
		}
		// sb.append("TOTAL: " + sum + "ns");
		// sb.append(" = " + sum/Math.pow(10, 9) + "sec");
		return sum;
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
				// TODO Evaluation of priorities.
				setPriority(Thread.currentThread().getPriority() - 1);
			} catch (Exception e) {
			}
			try {
				setDaemon(true);
			} catch (Exception e) {
			}
		}

		@Override
		public void run() {
			while (!this.isInterrupted()) {
				try {
					Runnable task = m_taskQueue.take();
					task.run();
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
				// TODO Evaluation of priorities
				if (m_chooseAlgorithm.equals(Algorithm.Hopcroft)) {
					setPriority(Thread.MAX_PRIORITY);
				} else {
					setPriority(Thread.MIN_PRIORITY);
				}
			} catch (Exception e) {
				assert (false);
			}
			try {
				setDaemon(true);
			} catch (Exception e) {
			}
		}

		@Override
		public void run() {
			try {
				if (m_chooseAlgorithm.equals(Algorithm.Hopcroft)) {
					MinimizeDfaHopcroftParallel.setParallelFlag(true);
					m_algorithm = new MinimizeDfaHopcroftParallel<LETTER, STATE>(m_services,
							m_operand.getStateFactory(),
							(INestedWordAutomaton<LETTER, STATE>) m_operand,
							m_interrupt);
					synchronized (m_algorithm) {
						m_hopcroftAlgorithm = (MinimizeDfaHopcroftParallel) m_algorithm;
						m_algorithm.notifyAll();
					}
					synchronized (m_algorithm) {
						while (m_incrementalAlgorithm == null) {
							try {
								m_algorithm.wait();
							} catch (InterruptedException e) {
								e.printStackTrace();
							}
						}
					}
					assert (m_incrementalAlgorithm.getParallel()) : "Parallel Flag for Hopcroft is false";
					if (isInterrupted()) {
						return;
					}
					m_hopcroftAlgorithm.minimizeParallel(m_taskQueue,
							m_incrementalAlgorithm);

				} else {
					MinimizeDfaAmrParallel.setParallelFlag(true);
					m_algorithm = new MinimizeDfaAmrParallel<LETTER, STATE>(m_services,
							m_operand.getStateFactory(), m_operand, m_interrupt);
					synchronized (m_algorithm) {
						m_incrementalAlgorithm = (MinimizeDfaAmrParallel) m_algorithm;
						m_algorithm.notifyAll();
					}
					synchronized (m_algorithm) {
						while (m_hopcroftAlgorithm == null) {
							try {
								m_algorithm.wait();
							} catch (InterruptedException e) {
								e.printStackTrace();
							}
						}
					}
					assert (m_incrementalAlgorithm.getParallel()) : "Parallel Flag for Incremental is false";
					if (isInterrupted()) {
						return;
					}
					m_incrementalAlgorithm.minimizeParallel(m_taskQueue,
							m_hopcroftAlgorithm);
				}
				if (isInterrupted()) {
					return;
				}
				synchronized (m_mainThread) {
					if (m_result == null) {
						m_result = (INestedWordAutomaton<LETTER, STATE>) getResult();
						m_cpuTime = Thread.currentThread().getId();
						m_mainThread.notify();
					}

				}
			} catch (OperationCanceledException e) {
				e.printStackTrace();
			} catch (AutomataLibraryException e) {
				e.printStackTrace();
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
		public Object getResult() throws OperationCanceledException {
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
