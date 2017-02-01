package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

public class Totalize<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IStateFactory<STATE> mStateFactory;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final Map<Integer, List<List<STATE>>> mMemCombinations;

	private final STATE mDummyState;
	private final Set<STATE> mStates;

	public Totalize(final AutomataLibraryServices services, final IStateFactory<STATE> factory,
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mTreeAutomaton = tree;
		mStateFactory = factory;
		mMemCombinations = new HashMap<>();
		mDummyState = mStateFactory.createEmptyStackState();
		mStates = new HashSet<>();
		mStates.add(mDummyState);
		mStates.addAll(tree.getStates());

		mResult = computeResult();
	}

	public List<List<STATE>> combinations(final int siz) {
		if (mMemCombinations.containsKey(siz)) {
			return mMemCombinations.get(siz);
		}
		final ArrayList<List<STATE>> res = new ArrayList<>();
		if (siz == 0) {
			final ArrayList<STATE> st = new ArrayList<>();
			res.add(st);
			mMemCombinations.put(siz, res);
			return res;
		}
		final List<List<STATE>> subres = combinations(siz - 1);
		for (final STATE st : mStates) {
			for (final List<STATE> subst : subres) {
				final List<STATE> t = new ArrayList<>(subst.size());
				t.addAll(subst);
				t.add(st);
				res.add(t);
			}
		}
		mMemCombinations.put(siz, res);
		return res;
	}

	public TreeAutomatonBU<LETTER, STATE> computeResult() {
		final TreeAutomatonBU<LETTER, STATE> res = new TreeAutomatonBU<>();
		for (final STATE st : mStates) {
			res.addState(st);
			if (mTreeAutomaton.isFinalState(st)) {
				res.addFinalState(st);
			}
			if (mTreeAutomaton.isInitialState(st)) {
				res.addInitialState(st);
			}
		}

		for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getRules()) {
			res.addRule(rule);
			for (final List<STATE> srcSt : combinations(rule.getArity())) {
				final Iterable<STATE> st = mTreeAutomaton.getSuccessors(srcSt, rule.getLetter());
				if (st != null && !st.iterator().hasNext()) {
					res.addRule(new TreeAutomatonRule<>(rule.getLetter(), srcSt, mDummyState));
				}
			}

		}
		for (final LETTER sym : mTreeAutomaton.getAlphabet()) {
			Method getAr = null;
			int arity = -1;
			try {
				getAr = sym.getClass().getMethod("getArity");
			} catch (final Exception e) {
				continue;
			}
			try {
				arity = (int) getAr.invoke(sym);
			} catch (final Exception e) {
				continue;
			}
			if (arity >= 0) {
				// System.err.println(sym);
				for (final List<STATE> srcSt : combinations(arity)) {
					final Iterable<STATE> st = mTreeAutomaton.getSuccessors(srcSt, sym);
					if (st != null && !st.iterator().hasNext()) {
						res.addRule(new TreeAutomatonRule<>(sym, srcSt, mDummyState));
					}
				}
			}
		}
		return res;
	}

	@Override
	public String operationName() {
		return "Totalize";
	}

	@Override
	public String startMessage() {
		return "Starting " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Finishing " + operationName();
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}

}
