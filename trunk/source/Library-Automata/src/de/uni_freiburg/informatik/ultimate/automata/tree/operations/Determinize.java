package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;

/**
 * Determinize a given tree automaton.
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> letter of the tree automaton.
 * @param <STATE> state of the tree automaton.
 */
public class Determinize<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IMergeStateFactory<STATE> mStateFactory;
	private final Map<Set<STATE>, STATE> mReducedStates;
	
	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final AutomataLibraryServices mServices;

	public Determinize(final AutomataLibraryServices services, final IMergeStateFactory<STATE> factory, 
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mServices = services;
		mReducedStates = new HashMap<>();
		mStateFactory = factory;
		mTreeAutomaton = tree;
		
		mResult = computeResult();
	}
	
	private STATE reduceState(final Set<STATE> key) {
		if (!mReducedStates.containsKey(key)) {
			mReducedStates.put(key, mStateFactory.merge(key));
		}
		return mReducedStates.get(key);
	}
	
	@Override
	public String operationName() {
		return "Determinization";
	}

	@Override
	public String startMessage() {
		return "Starting determinization";
	}

	@Override
	public String exitMessage() {
		return "Exiting determinization";
	}
	
	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		final Map<STATE, Set<STATE>> stateToSState = new HashMap<>();
		
		final Map<LETTER, Map<List<Set<STATE>>, Set<STATE>>> rules = new HashMap<>();
		
		/*
		// Dummy rules
		final STATE dummyState = stateFactory.createEmptyStackState();
		final Set<STATE> superSet = new HashSet<STATE>();
		superSet.addAll(treeAutomaton.getStates());
		superSet.add(dummyState);

		if (!stateToSState.containsKey(dummyState)) {
			final Set<STATE> nw = new HashSet<>();
			nw.add(dummyState);
			stateToSState.put(dummyState, nw);
		}
		for (final TreeAutomatonRule<LETTER, STATE> rule : treeAutomaton.getRules()) {
			if (!rules.containsKey(rule.getLetter())) {
				rules.put(rule.getLetter(), new HashMap<>());
			}
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(rule.getLetter());
			final List<Set<STATE>> source = new ArrayList<>();
			for (int i = 0; i < rule.getSource().size(); ++i) {
				source.add(superSet);
			}
			if (!mp.containsKey(source)) {
				mp.put(source, new HashSet<STATE>());
			}
			mp.get(source).add(dummyState);
		}
		// Dummy Rules end.
		*/
		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRules()) {
			if (!rules.containsKey(rule.getLetter())) {
				rules.put(rule.getLetter(), new HashMap<>());
			}
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(rule.getLetter());
			final List<Set<STATE>> source = new ArrayList<>();
			for (final STATE sr : rule.getSource()) {
				if (!stateToSState.containsKey(sr)) {
					final Set<STATE> nw = new HashSet<>();
					nw.add(sr);
					stateToSState.put(sr, nw);
				}
				source.add(stateToSState.get(sr));
			}
			final STATE sr = rule.getDest();
			if (!stateToSState.containsKey(sr)) {
				final Set<STATE> nw = new HashSet<>();
				nw.add(sr);
				stateToSState.put(sr, nw);
			}
			if (!mp.containsKey(source)) {
				mp.put(source, new HashSet<STATE>());
			}
			mp.get(source).add(sr);
		}
		
		final LinkedList<Set<STATE>> worklist = new LinkedList<>();
		for (final LETTER letter : rules.keySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
			for (final List<Set<STATE>> st : mp.keySet()) {
				if (mp.get(st).size() > 1) {
					worklist.add(mp.get(st));
				}
			}
		}
		final Set<Set<STATE>> visited = new HashSet<>();
		while (!worklist.isEmpty()) {
			final Set<STATE> state = worklist.poll();
			if (visited.contains(state))  {
				continue;
			}
			visited.add(state);
			final Map<LETTER, Map<List<Set<STATE>>, Set<Set<STATE>>>> newRules = new HashMap<>();
			for (final LETTER letter : rules.keySet()) {
				if (!newRules.containsKey(letter)) {
					newRules.put(letter, new HashMap<>());
				}
				final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
				for (final List<Set<STATE>> key : mp.keySet()) {
					final ArrayList<Set<STATE>> src = (ArrayList<Set<STATE>>) key;
					final Set<STATE> dest = mp.get(key);
					// letter(src) -> dest
					int idx = 0;
					for (final Set<STATE> srcQ : src) {
						if (state.containsAll(srcQ)) {
							final ArrayList<Set<STATE>> toAdd = (ArrayList<Set<STATE>>) src.clone();
							toAdd.set(idx, state);
							
							if (!newRules.get(letter).containsKey(toAdd)) {
								newRules.get(letter).put(toAdd, new HashSet<Set<STATE>>());
							}
							newRules.get(letter).get(toAdd).add(dest);
						}
						++idx;
					}
				}
			}
			for (final LETTER letter : newRules.keySet()) {
				final Map<List<Set<STATE>>, Set<Set<STATE>>> mp = newRules.get(letter);
				for (final List<Set<STATE>> st : mp.keySet()) {
				
					final Set<Set<STATE>> dest = mp.get(st);
					final Set<STATE> uni = new HashSet<>();
					for (final Set<STATE> s : dest) {
						uni.addAll(s);
					}
					rules.get(letter).put(st, uni);
					if (mp.get(st).size() > 1) {
						worklist.add(uni);
					}
				}
			}
		}
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();

		res.extendAlphabet(mTreeAutomaton.getAlphabet());
		
		for (final LETTER letter : rules.keySet()) {
			final Map<List<Set<STATE>>, Set<STATE>> mp = rules.get(letter);
			for (final List<Set<STATE>> sSrc : mp.keySet()) {
				final List<STATE> src = new ArrayList<>();
				for (final Set<STATE> sub : sSrc) {
					src.add(reduceState(sub));
				}
				final Set<STATE> sDest = mp.get(sSrc);
				final STATE dest = reduceState(sDest);
				res.addRule(new TreeAutomatonRule<>(letter, src, dest));
				
				for (final Set<STATE> sub : sSrc) {
					final STATE state = reduceState(sub);
					for (final STATE s : sub) {
						if (mTreeAutomaton.isInitialState(s)) {
							res.addInitialState(state);
						}
						if (mTreeAutomaton.isFinalState(s)) {
							res.addFinalState(state);
						}
					}
				}
				for (final STATE s : sDest) {
					if (mTreeAutomaton.isFinalState(s)) {
						res.addFinalState(dest);
					}
					if (mTreeAutomaton.isInitialState(s)) {
						res.addInitialState(dest);
					}
				}
			}
		}

		final Totalize<LETTER, STATE> op = new Totalize<>(mServices, mStateFactory, res);
		return op.getResult();
	}
	
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}

	public static void main(final String[] args) throws AutomataLibraryException {
		final TreeAutomatonBU<String, String> treeA = new TreeAutomatonBU<>();
		
		final String Q0 = "Q0", Q1 = "Q1", Q2 = "Q2", Q3 = "Q3";
		
		treeA.addInitialState(Q0);
		treeA.addFinalState(Q3);
		treeA.addRule(new TreeAutomatonRule<>("F", new ArrayList<>(Arrays.asList(new String[]{Q0, Q1})), Q2));
		treeA.addRule(new TreeAutomatonRule<>("F", new ArrayList<>(Arrays.asList(new String[]{Q0, Q1})), Q3));
		treeA.addRule(new TreeAutomatonRule<>("G", new ArrayList<>(Arrays.asList(new String[]{Q2})), Q3));
		treeA.addRule(new TreeAutomatonRule<>("G", new ArrayList<>(Arrays.asList(new String[]{Q3})), Q3));
		treeA.addRule(new TreeAutomatonRule<>("H", new ArrayList<>(Arrays.asList(new String[]{Q0, Q2})), Q1));
		treeA.addRule(new TreeAutomatonRule<>("H", new ArrayList<>(Arrays.asList(new String[]{Q0, Q3})), Q1));
		
		
		final UltimateServiceProviderMock usp = new UltimateServiceProviderMock();
		final AutomataLibraryServices services = new AutomataLibraryServices(usp);
		
		final StringFactory fac = new StringFactory();
		final Determinize<String, String> op = new Determinize<>(services, fac, treeA);
		final ITreeAutomatonBU<String, String> res = op.getResult();
		
		System.out.println(treeA.toString() + "\n");
		System.out.println(res.toString() + "\n");
		
		final TreeAutomatonBU<String, String> treeB = new TreeAutomatonBU<>();
		
		final String NAT = "NAT", NatList = "NatList", Bool = "Bool", BoolList = "BoolList", initA = "_", initB = "_";
		treeB.addInitialState(initA);
		treeB.addFinalState(NatList);
		treeB.addRule(new TreeAutomatonRule<>("0", new ArrayList<>(Arrays.asList(new String[]{initA})), NAT));
		treeB.addRule(new TreeAutomatonRule<>("s", new ArrayList<>(Arrays.asList(new String[]{NAT})), NAT));
		treeB.addRule(new TreeAutomatonRule<>("nil", new ArrayList<>(Arrays.asList(new String[]{initA})), NatList));
		treeB.addRule(new TreeAutomatonRule<>("cons", new ArrayList<>(Arrays.asList(new String[]{NAT, NatList})), NatList));


		final Determinize<String, String> opB = new Determinize<>(services, fac, treeB);
		final ITreeAutomatonBU<String, String> resB = opB.getResult();
		

		System.out.println(treeB.toString() + "\n");
		System.out.println(resB.toString() + "\n");
		
	}
}
