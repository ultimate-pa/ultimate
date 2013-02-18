package local.stalin.automata.nwalibrary;

import java.util.Collection;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.HashMap;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.Stack;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.core.api.StalinServices;
import local.stalin.model.*;

import org.apache.log4j.Logger;

/**
 * DESCRIPTION: build the difference automaton from two (non-)deterministic
 * automata by directly calculation of the intersection and determinization
 * during parallel running through the both of the automata
 * 
 * @author: Kefei Chen
 * 
 */

// jung visualization accepts no nwa with empty transition and symbol??

public class KefeiDifferenceAutomatonBuilder<Symbol, Content> {

	// private static Logger s_Logger = Logger.getLogger(Activator.PLUGIN_ID);
	private static final Boolean mb_debugMessages = false;
	private static Logger s_Logger = StalinServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	public KefeiDifferenceAutomatonBuilder() {

	}

	public INestedWordAutomaton<Symbol, Content> getDifferenceautomaton(
			INestedWordAutomaton<Symbol, Content> nwa1,
			INestedWordAutomaton<Symbol, Content> nwa2) {

		if (nwa1 == null || nwa2 == null)
			throw new NullPointerException();

		// create a result automaton
		Collection<Symbol> newInternals = nwa1.getInternalAlphabet();
		Collection<Symbol> newCalls = nwa1.getCallAlphabet();
		Collection<Symbol> newReturns = nwa1.getReturnAlphabet();

		INestedWordAutomaton<Symbol, Content> resNwa = new NestedWordAutomaton<Symbol, Content>(
				newInternals, newCalls, newReturns,
				((NestedWordAutomaton) nwa1).getContentFactory());

		// Initialize the state queue: This queue holds the states which are to
		// be processed
		Queue<DiffState> stateQueue = new ConcurrentLinkedQueue<DiffState>();

		// Create a new BuilderMap to store all needed data
		BuilderMap builderMap = new BuilderMap(nwa1, nwa2, resNwa, stateQueue);

		// Create a new initial state of Difference Automaton
		// =====================================================

		// find out the equivalence initial state from (non-det) nwa2
		Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> initDetSet = new TreeSet<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();

		for (IState<Symbol, Content> state : nwa2.getInitialStates()) {

			initDetSet
					.add(new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
							state, state));
		}

		// find out the initial state from nwa1
		for (IState<Symbol, Content> state : nwa1.getInitialStates()) {

			// build the product state of the both initial states
			Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>> initDiffPairState = new Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>(
					state, initDetSet);

			DiffState initDiffState = builderMap
					.getbuiltState(initDiffPairState);
			builderMap.m_result_nwa.initialStates
					.add(initDiffState.m_diffState);
			// Start by queuing the first state
			stateQueue.add(initDiffState);
		}

		while (!stateQueue.isEmpty()) {

			// Get the new state that will be processed
			DiffState diffState = stateQueue.poll();

			// Process all internal transitions
			// ================================

			for (Symbol symbol : diffState.m_diffPair.fst.getSymbolsInternal()) {

				Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> succStateDetSet = new TreeSet<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();

				for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : diffState.m_diffPair.snd) {

					for (IState<Symbol, Content> nextState : pair.snd
							.getInternalSucc(symbol)) {
						succStateDetSet
								.add(new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
										pair.fst, nextState));
					}
				}

				/*
				 * Build resulting succDiffState for Difference NWA by computing
				 * product state and add internal transition
				 */
				// if(!succStateDetSet.isEmpty()){

				for (IState<Symbol, Content> state : diffState.m_diffPair.fst
						.getInternalSucc(symbol)) {

					IState<Symbol, Content> temp = builderMap
							.getbuiltState(new Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>(
									state, succStateDetSet)).m_diffState;

					builderMap.m_result_nwa.addInternalTransition(
							diffState.m_diffState, symbol, temp);
				}
			}
			// }

			// Process all call transitions
			// ================================

			for (Symbol symbol : diffState.m_diffPair.fst.getSymbolsCall()) {

				// Process the part of determinization
				// ======================================

				Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> succStateDetSet = new TreeSet<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();

				for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : diffState.m_diffPair.snd) {

					for (IState<Symbol, Content> nextState : pair.snd
							.getCallSucc(symbol)) {
						succStateDetSet
								.add(new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
										pair.snd, nextState));
					}
				}

				/*
				 * Build resulting succDiffState for Difference NWA by computing
				 * product state and add call transition
				 * =============================================
				 */
				// if(!succStateDetSet.isEmpty()){
				for (IState<Symbol, Content> state : diffState.m_diffPair.fst
						.getCallSucc(symbol)) {

					IState<Symbol, Content> temp = builderMap
							.getbuiltState(new Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>(
									state, succStateDetSet)).m_diffState;

					builderMap.m_result_nwa.addCallTransition(
							diffState.m_diffState, symbol, temp);
				}
			}
			// }

			/*
			 * Process all return transitions according to the following method:
			 * Insert new return transition ((q1,S), (q1',S'), a, (q1",S")),
			 * where (q1, q1', q1") âˆˆ Î´r^nwa1 and S" = {(q, q') | (p, p') âˆˆ
			 * S, (q, p) âˆˆ S', (p', p, a, q') âˆˆ Î´r^nwa2 }
			 * ==================
			 * ==================================================
			 */

			for (Symbol symbol : diffState.m_diffPair.fst.getSymbolsReturn()) {

				Set<DiffState> processedDiffStateSet = new TreeSet<DiffState>(
						CompareByHash.instance);
				processedDiffStateSet.addAll(builderMap.getAllBuiltStates());

				// For all of processed DiffState
				for (DiffState pocessedDiffState : processedDiffStateSet) {

					// Only consider the states that have call transitions
					if (pocessedDiffState.m_diffState.getSymbolsCall()
							.isEmpty())
						continue;

					// Process the part of determinization
					// ======================================
					Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> succStateDetSet = new TreeSet<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();

					for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : diffState.m_diffPair.snd) {

						/*
						 * Transition availability test: is δr empty? (p, p') ∈
						 * S(corresponding pair), (p', p, a, q') ∈ δr^nwa2
						 */
						if (pair.snd.getReturnSucc(pair.fst, symbol).isEmpty())
							continue;

						for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> otherPair : pocessedDiffState.m_diffPair.snd) {

							/*
							 * Transition availability test (p, p') ∈
							 * S(corresponding pair), (q, p) ∈ S' (corresponding
							 * otherPair)
							 */
							if (otherPair.snd != pair.fst)
								continue;

							Collection<IState<Symbol, Content>> returns = pair.snd
									.getReturnSucc(pair.fst, symbol);
							if (!returns.isEmpty()) {

								for (IState<Symbol, Content> retState : returns)

									succStateDetSet
											.add(new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
													otherPair.fst, retState));
							}
						}
					}
					// Process the part of production
					// ======================================
					// if (!succStateDetSet.isEmpty()) {

					for (IState<Symbol, Content> state : diffState.m_diffPair.fst
							.getReturnSucc(pocessedDiffState.m_diffPair.fst,
									symbol)) {

						IState<Symbol, Content> temp = builderMap
								.getbuiltState(new Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>(
										state, succStateDetSet)).m_diffState;

						builderMap.m_result_nwa.addReturnTransition(
								diffState.m_diffState,
								pocessedDiffState.m_diffState, symbol, temp);
					}
				}
			}
			// }
			// Check for return transitions using dState as predecessor
			// ============================
			if (!diffState.m_diffState.getSymbolsCall().isEmpty()) {

				for (Symbol symbol : resNwa.getReturnAlphabet()) {

					Set<DiffState> currentDiffStateSet = new TreeSet<DiffState>(
							CompareByHash.instance);
					currentDiffStateSet.addAll(builderMap.getAllBuiltStates());

					// For all of current DiffState
					for (DiffState currentDiffState : currentDiffStateSet) {

						// Process the part of determinization
						// ======================================
						Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>> succStateDetSet = new TreeSet<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>();

						for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : currentDiffState.m_diffPair.snd) {

							if (pair.snd.getReturnSucc(pair.fst, symbol)
									.isEmpty())
								continue;

							for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> otherPair : diffState.m_diffPair.snd) {

								if (otherPair.snd != pair.fst)
									continue;

								Collection<IState<Symbol, Content>> returns = pair.snd
										.getReturnSucc(pair.fst, symbol);
								if (!returns.isEmpty()) {

									for (IState<Symbol, Content> retState : returns)

										succStateDetSet
												.add(new Pair<IState<Symbol, Content>, IState<Symbol, Content>>(
														otherPair.fst, retState));
								}
							}
						}
						// Process the part of production
						// ======================================
						// if (!succStateDetSet.isEmpty()) {

						for (IState<Symbol, Content> state : currentDiffState.m_diffPair.fst
								.getReturnSucc(diffState.m_diffPair.fst, symbol)) {

							IState<Symbol, Content> temp = builderMap
									.getbuiltState(new Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>(
											state, succStateDetSet)).m_diffState;

							builderMap.m_result_nwa.addReturnTransition(
									currentDiffState.m_diffState,
									diffState.m_diffState, symbol, temp);
						}
					}
				}
			}
			// }
			// =========end the check ====================

			/*
			 * sum of states in difference NWA must be less than
			 * Q_nwa1x2^{Q_nwa2xQ_nwa2}
			 */

			assert builderMap.m_result_nwa.states.size() <= ((NestedWordAutomaton) nwa1).states
					.size()
					* Math.pow(2, Math.pow(((NestedWordAutomaton) nwa2).states
							.size(), 2)) : "size problem";
		}

//		s_Logger
//				.info("The NWA1 has "
//						+ ((NestedWordAutomaton) nwa1).states.size()
//						+ " states, und the NWAe has "
//						+ ((NestedWordAutomaton) nwa2).states.size()
//						+ " states. The resulting (non-deterministic)difference NWA has "
//						+ builderMap.m_result_nwa.states.size() + " states");

		// compare the result
		//INestedWordAutomaton res1 = nwa1.intersect(nwa2.determinize()
		//		.complement());
		INestedWordAutomaton res2 = builderMap.m_result_nwa;
		// assert (((NestedWordAutomaton<Symbol, Content>)
		// res1.intersect(res1)).qAndDAcceptingRun() != null);

		if (mb_debugMessages) {

			int i = 0;
			for (IState<Symbol, Content> resState : builderMap.m_result_nwa
					.getAllStates()) {

				if (resState.isFinal()) {
					i++;
					s_Logger.debug("###########--" + i + "-final state: "
							+ resState.toString() + "--###############");
				}
			}
			s_Logger
					.debug("########### Difference computation is finished #############");

		}
		return res2;
	}

	/**
	 * This is just a shorter way to write Pair<IState<Symbol, Content>,
	 * Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>. The IState
	 * is stored for performance reasons
	 */
	private class DiffState {
		public DiffState(
				Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>> diffPair,
				IState<Symbol, Content> diffState) {
			assert diffPair != null;
			assert diffState != null;
			this.m_diffPair = diffPair;
			this.m_diffState = diffState;
		}

		Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>> m_diffPair;

		IState<Symbol, Content> m_diffState;
	}

	/**
	 * Data structure to store the mapping from processed states to the created
	 * states of the difference automaton, and to get relations among the two
	 * old automata and the new result automaton.
	 */
	private class BuilderMap {
		/*
		 * the mapping from processed states in old automata to the created new
		 * state in difference automaton
		 */
		Map<Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>, DiffState> m_stateMap;

		// These need to be accessed at new state creation
		NestedWordAutomaton<Symbol, Content> m_old_nwa1;
		NestedWordAutomaton<Symbol, Content> m_old_nwa2;

		// result automaton
		NestedWordAutomaton<Symbol, Content> m_result_nwa;

		// it stores the created states, but not be processed yet
		Queue<DiffState> m_stateQueue;

		boolean isInitial = false;

		// Constructor initializes the data structure
		public BuilderMap(INestedWordAutomaton<Symbol, Content> old_nwa1,
				INestedWordAutomaton<Symbol, Content> old_nwa2,
				INestedWordAutomaton<Symbol, Content> result_nwa,
				Queue<DiffState> stateQueue) {

			this.m_old_nwa1 = (NestedWordAutomaton<Symbol, Content>) old_nwa1;
			this.m_old_nwa2 = (NestedWordAutomaton<Symbol, Content>) old_nwa2;
			this.m_result_nwa = (NestedWordAutomaton<Symbol, Content>) result_nwa;
			this.m_stateQueue = stateQueue;
			this.m_stateMap = new TreeMap<Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>>, DiffState>(
					CompareByHash.instance);
		}

		/**
		 * @param
		 * 
		 * @return
		 */
		public DiffState getbuiltState(
				Pair<IState<Symbol, Content>, Set<Pair<IState<Symbol, Content>, IState<Symbol, Content>>>> diffPair) {
			// Check whether the state was already created at some point
			if (m_stateMap.containsKey(diffPair)) {

				return m_stateMap.get(diffPair);
			} else {

				// Create new content
				Collection<Pair<Content, Content>> cPairList = new ArrayList<Pair<Content, Content>>();
				if (diffPair.snd != null) {
					for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : diffPair.snd)

						cPairList.add(new Pair<Content, Content>(pair.fst
								.getContent(), pair.snd.getContent()));
				} else
					cPairList = null;
				Content content = m_result_nwa.m_contentFactory
						.createContentOnDifference(diffPair.fst.getContent(),
								cPairList);

				// Check whether state is final
				boolean isFinal = false;
				if (diffPair.fst.isFinal()) {

					if ((!diffPair.snd.isEmpty()) && diffPair.snd != null) {

						for (Pair<IState<Symbol, Content>, IState<Symbol, Content>> pair : diffPair.snd) {

							if ((m_old_nwa2.initialStates.contains(pair.fst) && pair.snd
									.isFinal())) {
								isFinal = false;
								break;
							}
							isFinal = true;
						}
					} else
						isFinal = true;
				}

				IState<Symbol, Content> newState = m_result_nwa.addState(
						isInitial, isFinal, content);
				DiffState diffState = new DiffState(diffPair, newState);

				// Store the new diffState in BuilderMap to find it later
				this.m_stateMap.put(diffPair, diffState);

				// Queue new diffState!
				this.m_stateQueue.add(diffState);

				return diffState;
			}
		}

		/**
		 * @return a Collection of all processed states of difference automaton
		 */
		public Collection<DiffState> getAllBuiltStates() {
			return this.m_stateMap.values();
		}

	}
}

/*
 * Remark: Following file be changed, because ContentFactory is needed for
 * content.
 * 
 * 1.) In: package local.stalin.automata.nwalibrary; public interface
 * IContentFactory<Content>
 * 
 * Added: Content createContentOnDifferenc(Content c1, Collection<Pair<Content,
 * Content>> cPairList);
 * 
 * 2.) In: package local.stalin.automata.nwalibrary; public class
 * StateNameFactory implements IContentFactory<String>
 */
