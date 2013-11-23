package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.HashRelation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.InCaRe;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.StronglyConnectedComponents;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.StronglyConnectedComponents.SCC;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class for obtaining NestedLassoRun which are accepted by a 
 * NestedWordAutomatonReachableStates.
 * 
 * This class is buggy, old and superseded by the class LassoConstructor.
 *
 * @param <LETTER>
 * @param <STATE>
 */
class LassoExtractor<LETTER, STATE> {
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Nwars;

	private final NestedLassoRun<LETTER, STATE> m_nlr;

	public LassoExtractor(NestedWordAutomatonReachableStates<LETTER, STATE> nwars,
			StateContainer<LETTER, STATE> honda, 
			SCC scc, 
			HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries) {
		m_Nwars = nwars;
		Set<SuccInfo> forbiddenSummaries = Collections.emptySet();
		LoopFinder lf = new LoopFinder(honda, scc, true, 
				acceptingSummaries, forbiddenSummaries);
		NestedRun<LETTER, STATE> loop = lf.getNestedRun();
		assert loop.getLength() > 1 : "looping epsilon transition";
		NestedRun<LETTER, STATE> stem = (new RunConstructor<LETTER, STATE>(m_Nwars, honda, null, false)).constructRun();
		s_Logger.debug("Stem length: " + stem.getLength());
		s_Logger.debug("Loop length: " + loop.getLength());
		m_nlr = new NestedLassoRun<LETTER, STATE>(stem, loop);
		s_Logger.debug("Stem " + stem);
		s_Logger.debug("Loop " + loop);
		assert (new BuchiAccepts<LETTER, STATE>(m_Nwars, m_nlr.getNestedLassoWord())).getResult();
	}

	NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
		return m_nlr;
	}

	class LoopFinder extends RunFinder {
		private final StronglyConnectedComponents.SCC m_Scc;

		public LoopFinder(StateContainer<LETTER, STATE> goal, StronglyConnectedComponents.SCC scc, 
				boolean visitAccepting, 
				HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries, 
				Set<SuccInfo> forbiddenSummaries) {
			super(goal, goal, visitAccepting, acceptingSummaries, forbiddenSummaries);
			m_Scc = scc;
		}

		@Override
		protected int getMaximalIterationNumber() {
			return m_Scc.getAllStates().size();
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingReturnTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getHierPred());
			StateContainer<LETTER, STATE> linPredSc = m_Nwars.obtainSC(inTrans.getLinPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc, 
					InCaRe.SUMMARY, linPredSc, true, isGuaranteed);
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingCallTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc, 
					InCaRe.CALL, null, summaryUsed, isGuaranteed);
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingInternalTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteed) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			return possiblePredecessor(predSc, inTrans.getLetter(), succSc, 
					InCaRe.INTERNAL, null, summaryUsed, isGuaranteed);
		}

		private SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> predSc,
				LETTER letter,
				StateContainer<LETTER, STATE> succSc, InCaRe type, 
				StateContainer<LETTER, STATE> linPred, 
				boolean summaryUsed, boolean isGuaranteedSucc) {
			if (!m_Scc.getAllStates().contains(predSc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || m_Nwars.isFinal(predSc.getState());
			if (type == InCaRe.SUMMARY) {
				isGuaranteedPred = isGuaranteedPred || isAcceptingSummary(predSc, succSc);
			}
			if (alreadyVisited(predSc, summaryUsed, isGuaranteedPred)) {
				return null;
			}
			boolean goalFound = m_Goal.equals(predSc) && isGuaranteedPred;
			boolean guaranteeChanger = isGuaranteedSucc ^ isGuaranteedPred;
			SuccInfo succInfo = new SuccInfo(succSc, letter, type, linPred, 
					isGuaranteedPred, goalFound, guaranteeChanger);
			super.markVisited(predSc, summaryUsed, isGuaranteedPred);
			return succInfo;
		}
	}



	class SuccInfo {
		private final StateContainer<LETTER, STATE> m_Successor;
		private final LETTER m_Letter;
		private final InCaRe m_Type;
		private final StateContainer<LETTER, STATE> m_LinPred;
		private final boolean m_Guarantee;
		private final boolean m_GoalFound;
		private final boolean m_GuaranteeChanger;
		public SuccInfo(StateContainer<LETTER, STATE> successor,
				LETTER letter,
				InCaRe type, StateContainer<LETTER, STATE> linPred,
				boolean guarantee,
				boolean goalFound,
				boolean guaranteeChanger) {
			if (type == InCaRe.SUMMARY && linPred == null) {
				throw new IllegalArgumentException("for summary we need linPred");
			}
			if ((type == InCaRe.INTERNAL || type == InCaRe.CALL) && linPred != null) {
				throw new IllegalArgumentException("linPred not allowed for internal and call");
			}
			if (type == InCaRe.RETURN) {
				throw new IllegalArgumentException("we do not use return here");
			}
			m_Successor = successor;
			m_Letter = letter;
			m_Type = type;
			m_LinPred = linPred;
			m_Guarantee = guarantee;
			m_GoalFound = goalFound;
			m_GuaranteeChanger = guaranteeChanger;
		}
		public StateContainer<LETTER, STATE> getSuccessor() {
			return m_Successor;
		}
		public LETTER getLetter() {
			return m_Letter;
		}
		public InCaRe getType() {
			return m_Type;
		}
		public StateContainer<LETTER, STATE> getLinPred() {
			return m_LinPred;
		}
		public boolean isGuarantee() {
			return m_Guarantee;
		}
		public boolean goalFound() {
			return m_GoalFound;
		}
		public boolean isGuaranteeChanger() {
			return m_GuaranteeChanger;
		}
		@Override
		public String toString() {
			return "SuccInfo [m_Successor=" + m_Successor + ", m_Letter="
					+ m_Letter + ", m_Type=" + m_Type + ", m_LinPred="
					+ m_LinPred + ", m_Guarantee=" + m_Guarantee
					+ ", m_GoalFound=" + m_GoalFound
					+ ", m_GuaranteeChanger=" + m_GuaranteeChanger + "]";
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + (m_GoalFound ? 1231 : 1237);
			result = prime * result + (m_Guarantee ? 1231 : 1237);
			result = prime * result + (m_GuaranteeChanger ? 1231 : 1237);
			result = prime * result
					+ ((m_Letter == null) ? 0 : m_Letter.hashCode());
			result = prime * result
					+ ((m_LinPred == null) ? 0 : m_LinPred.hashCode());
			result = prime * result
					+ ((m_Successor == null) ? 0 : m_Successor.hashCode());
			result = prime * result
					+ ((m_Type == null) ? 0 : m_Type.hashCode());
			return result;
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			SuccInfo other = (SuccInfo) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (m_GoalFound != other.m_GoalFound)
				return false;
			if (m_Guarantee != other.m_Guarantee)
				return false;
			if (m_GuaranteeChanger != other.m_GuaranteeChanger)
				return false;
			if (m_Letter == null) {
				if (other.m_Letter != null)
					return false;
			} else if (!m_Letter.equals(other.m_Letter))
				return false;
			if (m_LinPred == null) {
				if (other.m_LinPred != null)
					return false;
			} else if (!m_LinPred.equals(other.m_LinPred))
				return false;
			if (m_Successor == null) {
				if (other.m_Successor != null)
					return false;
			} else if (!m_Successor.equals(other.m_Successor))
				return false;
			if (m_Type != other.m_Type)
				return false;
			return true;
		}
		private LassoExtractor<LETTER, STATE> getOuterType() {
			return LassoExtractor.this;
		}


	}


	abstract class RunFinder {

		protected final Set<SuccInfo> m_ForbiddenSummaries;

		protected final StateContainer<LETTER, STATE> m_Start;
		protected final StateContainer<LETTER, STATE> m_Goal;
		/**
		 * If true we search only for runs that visit an accepting state.
		 */
		protected final boolean m_VisitAccepting;
		/**
		 * Successor mapping. If you build a path starting with this mapping
		 * it is guaranteed that the requirement (e.g., final state visited)
		 * is fulfilled. If you are rebuilding a run and requirement is 
		 * already met, my may need m_SuccessorsNoGuarantee for the 
		 * remainder of the run.
		 * If there is no requirement all successor informations are in 
		 * these Maps.
		 */
		//	protected final List<Map<STATE, Object>> m_SuccessorsWithGuarantee;

		/**
		 * States that have already been visited (without start state) from 
		 * which there is a run to the start state (of this search) such the
		 * equirement (e.g., final state visited) is fulfilled.
		 */
		//	protected final Set<STATE> m_VisitedWithGuarantee;

		/**
		 * Successor mapping. I you use this to build a run, it is not
		 * guaranteed that the requirement (e.g., final state visited) is
		 * fulfilled.
		 */
		//	protected final List<Map<STATE, Object>> m_SuccessorsNoGuarantee;

		/**
		 * States that have already been visited (without start state) from 
		 * which there is a run to the start state (of this search) it is not
		 * guaranteed that the requirement (e.g., final state visited) is
		 * fulfilled.
		 */
		//	protected final Set<STATE> m_VisitedNoGuarantee;

		/**
		 * Contains a pair of states (pre,post) if there is an run from
		 * pre to post such that
		 * - this run visits an accepting state
		 * - this run starts with a call
		 * - this run ends with a return
		 * 
		 * May be null if visiting an accepting state is not required.
		 */
		private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;


		protected final List<Map<StateContainer<LETTER,STATE>, SuccInfo>> m_SuccessorsWithSummary;
		protected final List<Map<StateContainer<LETTER,STATE>, SuccInfo>> m_SuccessorsWithoutSummary;

		private final Set<StateContainer<LETTER,STATE>> m_Visited_WithoutSummary_WithoutGuarantee = 
				new HashSet<StateContainer<LETTER,STATE>>();
		private final Set<StateContainer<LETTER,STATE>> m_Visited_WithSummary_WithoutGuarantee = 
				new HashSet<StateContainer<LETTER,STATE>>();
		private final Set<StateContainer<LETTER,STATE>> m_Visited_WithoutSummary_WithGuarantee = 
				new HashSet<StateContainer<LETTER,STATE>>();
		private final Set<StateContainer<LETTER,STATE>> m_Visited_WithSummary_WithGuarantee = 
				new HashSet<StateContainer<LETTER,STATE>>();

		protected boolean foundWithSummary = false;
		protected boolean foundWithoutSummary = false;

		protected int m_Iteration;
		private int m_IterationFoundWithSummary;

		public RunFinder(StateContainer<LETTER, STATE> start, StateContainer<LETTER, STATE> goal, boolean visitAccepting, 
				HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries, Set<SuccInfo> forbiddenSummaries) {
			assert (start != null);
			assert (goal != null);
			m_Start = start;
			m_Goal = goal;
			m_VisitAccepting = visitAccepting;
			m_AcceptingSummaries = acceptingSummaries;
			m_ForbiddenSummaries = forbiddenSummaries;
			m_SuccessorsWithSummary = new ArrayList<Map<StateContainer<LETTER,STATE>, SuccInfo>>();
			m_SuccessorsWithoutSummary = new ArrayList<Map<StateContainer<LETTER,STATE>, SuccInfo>>();
			m_IterationFoundWithSummary = -1;
			m_Iteration = 0;
		}

		public NestedRun<LETTER, STATE> getNestedRun() {
			find(m_Start);
			if (foundWithoutSummary) {
				return constructRun(m_Iteration, false);
			} else {
				return constructRun(m_IterationFoundWithSummary, true);
			}
		}

		protected boolean isAcceptingSummary(StateContainer<LETTER, STATE> predSc,
				StateContainer<LETTER, STATE> succSc) {
			Set<Summary<LETTER, STATE>> summaries = m_AcceptingSummaries.getImage(predSc);
			if (summaries == null) {
				return false;
			} else {
				for (Summary<LETTER, STATE> summary : summaries) {
					if (summary.getSucc().equals(succSc)) {
						return true;
					}

				}
				return false;
			}
		}

		private boolean continueSearch() {
			if (foundWithoutSummary) {
				return false;
			}
			if (m_SuccessorsWithSummary.get(m_Iteration).isEmpty() 
					&& m_SuccessorsWithoutSummary.get(m_Iteration).isEmpty()) {
				return false;
			}
			return true;
		}

		private void find(StateContainer<LETTER,STATE> start) {
			m_SuccessorsWithoutSummary.add(new HashMap<StateContainer<LETTER,STATE>,SuccInfo>());
			m_SuccessorsWithSummary.add(new HashMap<StateContainer<LETTER,STATE>,SuccInfo>());
			findPredecessors(start, !m_VisitAccepting || m_Nwars.isFinal(start.getState()), false);
			while(continueSearch()) {
				assert (m_Iteration <= getMaximalIterationNumber()) : "too many iterations";
				m_Iteration++;
				m_SuccessorsWithoutSummary.add(new HashMap<StateContainer<LETTER,STATE>,SuccInfo>());
				m_SuccessorsWithSummary.add(new HashMap<StateContainer<LETTER,STATE>,SuccInfo>());
				if (!foundWithSummary) {
					for (StateContainer<LETTER,STATE> sc : m_SuccessorsWithSummary.get(m_Iteration-1).keySet()) {
						boolean isGuaranteed = m_SuccessorsWithSummary.get(m_Iteration-1).get(sc).isGuarantee();
						findPredecessors(sc, isGuaranteed, true);
					}
				}
				for (StateContainer<LETTER,STATE> sc : m_SuccessorsWithoutSummary.get(m_Iteration-1).keySet()) {
					boolean isGuaranteed = m_SuccessorsWithoutSummary.get(m_Iteration-1).get(sc).isGuarantee();
					findPredecessors(sc, isGuaranteed, false);
				}

			}
			assert (foundWithSummary || foundWithoutSummary) : "Bug in run reconstruction of new emptiness test.";
		}

		abstract protected int getMaximalIterationNumber();

		abstract protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, IncomingReturnTransition<LETTER, STATE> inTrans, boolean summaryUsed, boolean isGuaranteed);
		abstract protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, IncomingCallTransition<LETTER, STATE> inTrans, boolean summaryUsed, boolean isGuaranteed);
		abstract protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, IncomingInternalTransition<LETTER, STATE> inTrans, boolean summaryUsed, boolean isGuaranteed);


		/**
		 * Add for a predecessor predSc information about successors to succMap.
		 * If there is already a successor information that is as good as this
		 * (requirement already fulfilled) nothing is added.
		 * @param type call, internal, or summary
		 * @param linPred linear predecessor if type is summary
		 * @param succSc successor state
		 * @param isGuranteed is the requirement (e.g., accepting state) visited
		 * guaranteed?
		 */
		private void addSuccessorInformation(StateContainer<LETTER,STATE> predSc, 
				boolean summaryUsed,
				SuccInfo newSuccInfo) {
			Map<StateContainer<LETTER,STATE>, SuccInfo> succMap;
			if (summaryUsed) {
				foundWithSummary |= newSuccInfo.goalFound();
				succMap = m_SuccessorsWithSummary.get(m_Iteration);
			} else {
				foundWithoutSummary |= newSuccInfo.goalFound();
				succMap = m_SuccessorsWithoutSummary.get(m_Iteration);
			}
			SuccInfo current = succMap.get(predSc);
			if (current == null) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
			if (!current.isGuarantee() && newSuccInfo.isGuarantee()) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
			if (!current.goalFound() && newSuccInfo.goalFound()) {
				succMap.put(predSc, newSuccInfo);
				return;
			}
		}

		private void markVisited(StateContainer<LETTER,STATE> sc, boolean summaryUsed, boolean isGuranteed) {
			if (summaryUsed) {
				if (isGuranteed) {
					m_Visited_WithSummary_WithGuarantee.add(sc);
				} else {
					m_Visited_WithSummary_WithoutGuarantee.add(sc);
				}
			} else {
				if (isGuranteed) {
					m_Visited_WithoutSummary_WithGuarantee.add(sc);
				} else {
					m_Visited_WithoutSummary_WithoutGuarantee.add(sc);
				}
			}
		}

		protected boolean alreadyVisited(StateContainer<LETTER,STATE> sc, boolean summaryUsed, boolean isGuranteed) {
			if (summaryUsed) {
				if (isGuranteed) {
					return m_Visited_WithSummary_WithGuarantee.contains(sc);
				} else {
					return m_Visited_WithSummary_WithoutGuarantee.contains(sc);
				}
			} else {
				if (isGuranteed) {
					return m_Visited_WithoutSummary_WithGuarantee.contains(sc);
				} else {
					return m_Visited_WithoutSummary_WithoutGuarantee.contains(sc);
				}
			}
		}

		protected void findPredecessors(StateContainer<LETTER,STATE> sc,
				boolean isGuaranteed, boolean summaryUsed) {
			for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Nwars.internalPredecessors(sc.getState())) {
				SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
					addSuccessorInformation(predSc, summaryUsed, succInfo);
				}
			}
			for (IncomingCallTransition<LETTER, STATE> inTrans : m_Nwars.callPredecessors(sc.getState())) {
				SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
					addSuccessorInformation(predSc, summaryUsed, succInfo);
				}
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : m_Nwars.returnPredecessors(sc.getState())) {
				SuccInfo succInfo = possiblePredecessor(sc, inTrans, summaryUsed, isGuaranteed);
				if (succInfo != null) {
					StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getHierPred());
					addSuccessorInformation(predSc, true, succInfo);
				}
			}
			if (foundWithSummary && m_IterationFoundWithSummary == -1) {
				m_IterationFoundWithSummary = m_Iteration;
			}
		}






		/**
		 * Construct the run that has been found.
		 * @return
		 */
		private NestedRun<LETTER, STATE> constructRun(int iteration, boolean foundWithSummary) {
			boolean visitAcceptingStillRequired = m_VisitAccepting;
			NestedRun<LETTER, STATE> result = new NestedRun<LETTER,STATE>(m_Goal.getState());

			for (int i = iteration; i>=0; i--) {
				StateContainer<LETTER, STATE> currentState = m_Nwars.obtainSC(result.getStateAtPosition(result.getLength()-1));
				if (m_Nwars.isFinal(currentState.getState())) {
					visitAcceptingStillRequired = false;
				}
				SuccInfo succs = null;
				if (foundWithSummary) {
					succs = m_SuccessorsWithSummary.get(i).get(currentState);
				}
				if (succs == null) {
					succs = m_SuccessorsWithoutSummary.get(i).get(currentState);
				}
				assert succs != null : "No successor found!";
				NestedRun<LETTER, STATE> newSuffix;
				if (succs.getType() == InCaRe.INTERNAL) {
					newSuffix = new NestedRun<LETTER, STATE>(currentState.getState(), 
							succs.getLetter(),
							NestedWord.INTERNAL_POSITION, 
							succs.getSuccessor().getState());
				} else if (succs.getType() == InCaRe.CALL) {
					newSuffix = new NestedRun<LETTER, STATE>(currentState.getState(), 
							succs.getLetter(), 
							NestedWord.PLUS_INFINITY, 
							succs.getSuccessor().getState());
				} else if (succs.getType() == InCaRe.SUMMARY) {
					boolean findAcceptingSummary;
					if (visitAcceptingStillRequired && succs.isGuaranteeChanger() && !m_Nwars.isFinal(currentState.getState())) {
						assert (isAcceptingSummary(currentState, succs.getSuccessor()));
						findAcceptingSummary = true;
					} else {
						findAcceptingSummary = false;
					}
					Set<SuccInfo> forbiddenSummaries = new HashSet<SuccInfo>();
					forbiddenSummaries.addAll(m_ForbiddenSummaries);
					assert !forbiddenSummaries.contains(succs);
					forbiddenSummaries.add(succs);
					SummaryFinder summaryFinder = new SummaryFinder(
							succs.getLinPred(), currentState, 
							findAcceptingSummary, m_AcceptingSummaries, 
							forbiddenSummaries);
					newSuffix = summaryFinder.getNestedRun();
					NestedRun<LETTER, STATE> retSuffix = 
							new NestedRun<LETTER, STATE>(
									succs.getLinPred().getState(), 
									succs.getLetter(), 
									NestedWord.MINUS_INFINITY, 
									succs.getSuccessor().getState());
					newSuffix = newSuffix.concatenate(retSuffix);
					if (findAcceptingSummary) {
						visitAcceptingStillRequired = false;
					}
				} else {
					throw new AssertionError("unknown transition");
				}
				result = result.concatenate(newSuffix);
			}
			return result;
		}
	}









	class SummaryFinder extends RunFinder {


		public SummaryFinder(StateContainer<LETTER, STATE> returnPredecessor, StateContainer<LETTER, STATE> callPredecessor, 
				boolean visitAccepting,	
				HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> acceptingSummaries,
				Set<SuccInfo> forbiddenSummaries) {
			super(returnPredecessor, callPredecessor, visitAccepting, acceptingSummaries, forbiddenSummaries);
		}

		@Override
		protected int getMaximalIterationNumber() {
			return m_Nwars.size();
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingInternalTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteedSucc) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			if (!goalIsDownState(predSc, isGuaranteedSucc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || m_Nwars.isFinal(predSc.getState());
			if (alreadyVisited(predSc, summaryUsed, isGuaranteedPred)) {
				return null;
			}
			boolean guaranteeChanger = isGuaranteedPred ^ isGuaranteedSucc;
			SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(), 
					InCaRe.INTERNAL, null, isGuaranteedPred, false, guaranteeChanger);
			super.markVisited(predSc, summaryUsed, isGuaranteedPred);
			return succInfo;
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingCallTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteedSucc) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			if (!isGuaranteedSucc || !m_Goal.equals(predSc)) {
				return null;
			}
			SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(), 
					InCaRe.CALL, null, isGuaranteedSucc, true, false);
			super.markVisited(predSc, summaryUsed, isGuaranteedSucc);
			return succInfo;
		}

		@Override
		protected SuccInfo possiblePredecessor(StateContainer<LETTER, STATE> succSc, 
				IncomingReturnTransition<LETTER, STATE> inTrans,
				boolean summaryUsed, boolean isGuaranteedSucc) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getHierPred());
			if (!goalIsDownState(predSc, isGuaranteedSucc)) {
				return null;
			}
			boolean isGuaranteedPred = isGuaranteedSucc;
			isGuaranteedPred = isGuaranteedPred || m_Nwars.isFinal(predSc.getState());
			isGuaranteedPred = isGuaranteedPred || isAcceptingSummary(predSc, succSc);
			if (alreadyVisited(predSc, true, isGuaranteedPred)) {
				return null;
			}
			boolean guaranteeChanger = isGuaranteedPred ^ isGuaranteedSucc;
			StateContainer<LETTER, STATE> linPredSc = m_Nwars.obtainSC(inTrans.getLinPred());
			SuccInfo succInfo = new SuccInfo(succSc, inTrans.getLetter(), 
					InCaRe.SUMMARY, linPredSc, isGuaranteedPred, false, guaranteeChanger);
			if (m_ForbiddenSummaries.contains(succInfo)) {
				return null;
			}
			super.markVisited(predSc, true, isGuaranteedPred);
			return succInfo;
		}

		private boolean goalIsDownState(StateContainer<LETTER,STATE> predSc, boolean isGuranteed) {
			if (!predSc.getDownStates().containsKey(m_Goal.getState())) {
				return false;
			}
			if (isGuranteed) {
				return true;
			} else {
				return predSc.hasDownProp(m_Goal.getState(), 
						DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL);
			}
		}

	}

}



