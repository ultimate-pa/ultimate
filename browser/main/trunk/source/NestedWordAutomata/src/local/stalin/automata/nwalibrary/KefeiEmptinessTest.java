package local.stalin.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

import org.apache.log4j.Logger;

/**
 * DESCRIPTION: test emptiness through computing reachability with baseline
 * algorism. baseline-reachability algorism have been introduced by Swarat
 * Chaudhuri in [1] Subcubic Algorithms for Recursive State Machines. page
 * 162-164
 * 
 * @author: kefei
 * 
 */

public class KefeiEmptinessTest<Symbol, Content> {

	private NestedRun<Symbol, Content>[][] m_reachablityTable;
	private Collection<IState<Symbol, Content>> m_stateSet;
	private Map<IState<Symbol, Content>, Integer> m_stateIndexMap;
	private Map<Integer, IState<Symbol, Content>> m_indexStateMap;
	private Collection<IState<Symbol, Content>> m_initialStateSet;
	private Map<Pair<IState<Symbol, Content>, IState<Symbol, Content>>, Symbol> m_callingSymbolMap;

	private LinkedList<IState<Symbol, Content>[]> m_workList;
	private LinkedList<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> m_callRelationList;

	private static final boolean mb_compute_min_run = true;

	private static final Boolean m_debugMessages = false;
	private static Logger s_Logger = Logger.getRootLogger();

	public KefeiEmptinessTest(INestedWordAutomaton<Symbol, Content> nwa) {

		if (nwa != null) {

			m_workList = new LinkedList<IState<Symbol, Content>[]>();
			m_stateSet = nwa.getAllStates();

			int size = nwa.getAllStates().size();
			int i = 0;
			m_stateIndexMap = new HashMap<IState<Symbol, Content>, Integer>();
			m_indexStateMap = new HashMap<Integer, IState<Symbol, Content>>();
			// m_callRelationMap = new HashMap<IState<Symbol, Content>,
			// ArrayList<IState<Symbol, Content>>>();
			m_callingSymbolMap = new HashMap<Pair<IState<Symbol, Content>, IState<Symbol, Content>>, Symbol>();
			m_callRelationList = new LinkedList<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();
			m_initialStateSet = nwa.getInitialStates();

			for (IState<Symbol, Content> state : m_stateSet) {

				m_stateIndexMap.put(state, i);
				m_indexStateMap.put(i, state);
				i++;
			}

			m_reachablityTable = new NestedRun[size][size];
			for (i = 0; i < size; i++)
				for (int j = 0; j < size; j++) {

					m_reachablityTable[i][j] = null;
				}
		} else {
			throw new IllegalArgumentException(
					"This NWA has not been yet instantiated!");
		}
	}

	/**
	 * Description : computing reachability for every states of a NWA with
	 * baseline-reachability algorism in [1] page 163.
	 */
	public void computerReachability() {

		/* look for a relation between calling states and called states */
		for (IState<Symbol, Content> callingState : m_stateSet) {

			for (Symbol sy : callingState.getSymbolsCall()) {

				Collection<IState<Symbol, Content>> calledStates = callingState
						.getCallSucc(sy);
				for (IState<Symbol, Content> calledState : calledStates) {

					if (calledState == null)
						throw new IllegalStateException(
								"The called state must not be nullpointer!");
					if (callingState == null)
						throw new IllegalStateException(
								"The calling state must not be nullpointer!");
					putCallRelation(calledState, callingState, sy);

					/*
					 * if direct succedent state of a called state is a return
					 * state add the reachablity from calling state to return
					 * succedent in the table
					 */
					for (Symbol ret : calledState.getSymbolsReturn()) {

						for (IState<Symbol, Content> returnLinearPred : calledState
								.getReturnLinearPred(ret)) {

							if (returnLinearPred == callingState) {

								NestedRun<Symbol, Content> run = buildNestedRun(
										sy, NestedWord.PLUS_INFINITY,
										callingState, calledState);
								for (IState<Symbol, Content> returnScc : calledState
										.getReturnSucc(callingState, ret)) {

									run = run.concatenate(buildNestedRun(ret,
											NestedWord.MINUS_INFINITY,
											calledState, returnScc));
									updateReachablityTable(m_stateIndexMap
											.get(callingState), m_stateIndexMap
											.get(returnScc), run);
								}
							}
						}
					}/* end */
				}
			}
		}

		/*
		 * Insert trivial reachability into worklist and reachability table.
		 * According to line 1 of pseudo code in Fig-3 in [1] page 163
		 */

		for (IState<Symbol, Content> preState : m_stateSet) {

			for (Symbol sy : preState.getSymbolsInternal()) {

				Collection<IState<Symbol, Content>> succStates = preState
						.getInternalSucc(sy);
				for (IState<Symbol, Content> succState : succStates) {
					int from = m_stateIndexMap.get(preState);
					int to = m_stateIndexMap.get(succState);
					if (m_reachablityTable[from][to] == null) {

						// insert a new entry in reachability table
						m_reachablityTable[from][to] = buildNestedRun(sy,
								NestedWord.INTERNAL_POSITION, preState,
								succState);

						// push reachabilitiy in worklist
						m_workList.push(new IState[] { preState, succState });
						if (m_debugMessages)
							KefeiEmptinessTest.s_Logger.info("+++["
									+ m_stateIndexMap.get(preState) + "]" + "["
									+ m_stateIndexMap.get(succState) + "]----");
					}
				}
			}
		}

		/*
		 * Compute the transitive closure. According to line 2-10 of pseudo code
		 * in Fig-3 in [1] page 163
		 */
		while (!m_workList.isEmpty()) {
			IState<Symbol, Content>[] workingRelation = m_workList.pop();
			IState<Symbol, Content> preState = workingRelation[0];
			IState<Symbol, Content> succState = workingRelation[1];

			if (m_debugMessages)
				if (m_reachablityTable[m_stateIndexMap.get(preState)][m_stateIndexMap
						.get(succState)] == null)
					KefeiEmptinessTest.s_Logger.info("???["
							+ m_stateIndexMap.get(preState) + "]" + "["
							+ m_stateIndexMap.get(succState) + "]----");
			/*
			 * Compute the rule 3. in [1] page 162 According to line 4-6 of
			 * pseudo code in Fig-3 in [1] page 163
			 */

			for (Symbol sy : succState.getSymbolsReturn()) {

				Collection<IState<Symbol, Content>> States = succState
						.getReturnLinearPred(sy);

				if (m_debugMessages) {
					if (sy == null)
						KefeiEmptinessTest.s_Logger
								.info("Warning!! statment is nullpoint");
				}
				for (IState<Symbol, Content> returnLinearPredState : States) {

					if (getValue(preState) != null
							&& getValue(preState).contains(
									returnLinearPredState)) {

						for (IState<Symbol, Content> returnSuccState : succState
								.getReturnSucc(returnLinearPredState, sy)) {

							NestedRun<Symbol, Content> run = buildNestedRun(
									getSymbol(returnLinearPredState, preState),
									NestedWord.PLUS_INFINITY,
									returnLinearPredState, preState);

							int from = m_stateIndexMap.get(preState);
							int to = m_stateIndexMap.get(succState);
							run = run
									.concatenate(m_reachablityTable[from][to])
									.concatenate(
											buildNestedRun(sy,
													NestedWord.MINUS_INFINITY,
													succState, returnSuccState));

							from = m_stateIndexMap.get(returnLinearPredState);
							to = m_stateIndexMap.get(returnSuccState);

							if (updateReachablityTable(from, to, run))
								m_workList
										.push(new IState[] {
												returnLinearPredState,
												returnSuccState });
						}
					}
				}
			}

			/*
			 * The following two "for-loop" compute the rule 3. in [1] page 162
			 * According to line 7-10 of pseudo code in Fig-3 in [1] page 163
			 */
			int over = m_stateIndexMap.get(preState);
			int to = m_stateIndexMap.get(succState);
			for (int from = 0; from < m_stateSet.size(); from++) {

				if (m_reachablityTable[from][over] != null) {

					if (m_debugMessages)
						KefeiEmptinessTest.s_Logger.info("---[" + from + "]" + "["
								+ over + "]----");
					if (m_reachablityTable[over][to] == null)
						KefeiEmptinessTest.s_Logger.info("!!![" + over + "]" + "["
								+ to + "]----");
					if (updateReachablityTable(from, to,
							m_reachablityTable[from][over]
									.concatenate(m_reachablityTable[over][to])))
						m_workList.push(new IState[] {
								m_indexStateMap.get(from), succState });
				}
			}

			int from = m_stateIndexMap.get(preState);
			over = m_stateIndexMap.get(succState);
			for (to = 0; to < m_stateSet.size(); to++) {

				if (m_reachablityTable[over][to] != null) {

					if (updateReachablityTable(from, to,
							m_reachablityTable[from][over]
									.concatenate(m_reachablityTable[over][to])))
						m_workList.push(new IState[] { preState,
								m_indexStateMap.get(to) });
				}
			}
		}
		/*
		 * Add call transition of NWA and compute the (reflexive) transitive
		 * closure of the resultant relation. According to line 12-13 of pseudo
		 * code in Fig-3 in [1] page 163
		 */
		// for every calling and called pair
		Iterator<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> it = m_callRelationList
				.iterator();
		while (it.hasNext()) {
			Pair<IState<Symbol, Content>, IState<Symbol, Content>> callRelation = it
					.next();
			IState<Symbol, Content> calling = callRelation.snd;
			IState<Symbol, Content> called = callRelation.fst;

			if (calling != null && called != null) {

				int from = m_stateIndexMap.get(calling);
				int to = m_stateIndexMap.get(called);

				NestedRun<Symbol, Content> run = buildNestedRun(getSymbol(
						calling, called), NestedWord.PLUS_INFINITY, calling,
						called);
				updateReachablityTable(from, to, run);

				/*
				 * update the entris in reachability table, which is reachable
				 * from every state to called state
				 */

				int over = from;
				for (from = 0; from < m_stateSet.size(); from++) {
					if (m_reachablityTable[from][over] != null) {
						run = m_reachablityTable[from][over]
								.concatenate(m_reachablityTable[over][to]);
						updateReachablityTable(from, to, run);
					}
				}
				// update the entris
				over = to;
				for (to = 0; to < m_stateSet.size(); to++) {

					if (m_reachablityTable[over][to] != null) {

						for (from = 0; from < m_stateSet.size(); from++) {

							if (m_reachablityTable[from][over] != null) {

								run = m_reachablityTable[from][over]
										.concatenate(m_reachablityTable[over][to]);
								updateReachablityTable(from, to, run);
							}// end-if
						}// end-for
					}// end-if
				}// end-for
			}
		}
	}

	private boolean updateReachablityTable(int from, int to,
			NestedRun<Symbol, Content> run) {
		if (m_reachablityTable[from][to] == null
				|| (m_reachablityTable[from][to] != null
						&& run.getNestedWord().length() < m_reachablityTable[from][to]
								.getNestedWord().length() && mb_compute_min_run)) {

			m_reachablityTable[from][to] = run;
			return true;
		} else
			return false;
	}

	public NestedRun<Symbol, Content> getNestedRun(
			IState<Symbol, Content> preState, IState<Symbol, Content> succState) {

		int from = m_stateIndexMap.get(preState);
		int to = m_stateIndexMap.get(succState);
		
		// assert (m_reachablityTable[from][to] == null) : "from "
		// + preState.toString() + " to " + succState.toString()
		// + " is unreachable!!";
		if (m_debugMessages)
			if (m_reachablityTable[from][to] == null)
				System.out.println("from " + preState.toString() + " to "
						+ succState.toString() + " is unreachable!!");

		return m_reachablityTable[from][to];
	}

	private NestedRun<Symbol, Content> buildNestedRun(Symbol sy, int pos,
			IState<Symbol, Content> pre, IState<Symbol, Content> succ) {

		Object word[] = new Object[] { sy };
		int[] posOfRelation = new int[] { pos };
		NestedWord<Symbol> nestedWord = new NestedWord<Symbol>((Symbol[]) word,
				posOfRelation);
		ArrayList<IState<Symbol, Content>> stateSequence = new ArrayList<IState<Symbol, Content>>();
		stateSequence.add(pre);
		stateSequence.add(succ);
		return new NestedRun<Symbol, Content>(nestedWord, stateSequence);
	}

	public void putCallRelation(IState<Symbol, Content> called,
			IState<Symbol, Content> calling, Symbol sy) {
		Pair<IState<Symbol, Content>, IState<Symbol, Content>> callRelation = new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
				called, calling);
		m_callRelationList.push(callRelation);
		m_callingSymbolMap.put(callRelation, sy);
	}

	private ArrayList<IState<Symbol, Content>> getValue(
			IState<Symbol, Content> key) {

		Iterator<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> it = m_callRelationList
				.iterator();
		ArrayList<IState<Symbol, Content>> valueArrayList = null;
		while (it.hasNext()) {

			Pair<IState<Symbol, Content>, IState<Symbol, Content>> states = it
					.next();
			if (states.fst == key) {
				if (valueArrayList == null)
					valueArrayList = new ArrayList<IState<Symbol, Content>>();
				valueArrayList.add(states.snd);
			}
		}

		return valueArrayList;
	}

	private Symbol getSymbol(IState<Symbol, Content> calling,
			IState<Symbol, Content> called) {

		Iterator<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> it = m_callRelationList
				.iterator();
		Symbol sy = null;
		while (it.hasNext()) {
			Pair<IState<Symbol, Content>, IState<Symbol, Content>> states = it
					.next();
			if (states.snd.equals(calling) && states.fst.equals(called)) {

				sy = m_callingSymbolMap.get(states);
			}
		}
		return sy;
	}

	/* get the shortest nested trace */
	public NestedRun<Symbol, Content> getNestedTrace() {

		// TODO compute the simplest shortest trace?
		NestedRun<Symbol, Content> trace = null;

		/* pick up a initial start state and a error state */
		for (IState<Symbol, Content> from : m_initialStateSet) {
			for (IState<Symbol, Content> to : m_stateSet) {

				if (from == null)
					throw new IllegalArgumentException(
							"The initial state must not be nullpointer!");
				if (to.isFinal()) {
					/* get the run from the reachability table */
					NestedRun<Symbol, Content> tempTrace = getNestedRun(from,
							to);
					/*
					 * if the trace shorter than the current trace, then update
					 * the current
					 */
					if (tempTrace != null) {
						if (trace == null)
							trace = tempTrace;
						else if (tempTrace.getNestedWord().length() < trace
								.getNestedWord().length())
							trace = tempTrace;
					}
				}
			}
		}
		if (trace == null)
			KefeiEmptinessTest.s_Logger
					.info("There is no nested error trace for the NWA!");
		else
			KefeiEmptinessTest.s_Logger.info("The nested error trace is: "
					+ trace.toString());
		return trace;
	}

	public void printReachabilityTable() {
		int size = m_stateSet.size();

		for (int i = 0; i < size; i++)
			for (int j = 0; j < size; j++) {

				String pre = m_indexStateMap.get(i).toString();
				String succ = m_indexStateMap.get(j).toString();
				if (m_reachablityTable[i][j] != null) {

					KefeiEmptinessTest.s_Logger.info("[" + i + "]" + "[" + j + "]."
							+ "(from " + pre + ",to " + succ + "): "
							+ m_reachablityTable[i][j].toString());
					if (m_debugMessages)
						System.out.println("[" + i + "]" + "[" + j + "]."
								+ "(from " + pre + ",to " + succ + "): "
								+ m_reachablityTable[i][j].toString());

				} else {

					KefeiEmptinessTest.s_Logger.info("[" + i + "]" + "[" + j + "]."
							+ "(from " + pre + ", to" + succ
							+ ") is unreachabl!!!");
				}
			}
	}
}
