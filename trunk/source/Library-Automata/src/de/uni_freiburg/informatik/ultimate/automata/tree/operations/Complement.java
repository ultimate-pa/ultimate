package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

/**
 * Complements a given treeAutomaton.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	private final IMergeStateFactory<STATE> mStateFactory;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final AutomataLibraryServices mServices;

	public Complement(final AutomataLibraryServices services, final IMergeStateFactory<STATE> factory,
			final ITreeAutomatonBU<LETTER, STATE> tree) {
		mServices = services;
		mTreeAutomaton = tree;
		mStateFactory = factory;

		mResult = computeResult();
	}

	@Override
	public String operationName() {
		return "Complement";
	}

	@Override
	public String startMessage() {
		return "Starting complementing";
	}

	@Override
	public String exitMessage() {
		return "Exiting complementing";
	}

	private ITreeAutomatonBU<LETTER, STATE> computeResult() {
		final Determinize<LETTER, STATE> op = new Determinize<>(mServices, mStateFactory, mTreeAutomaton);
		final TreeAutomatonBU<LETTER, STATE> res = (TreeAutomatonBU<LETTER, STATE>) op.getResult();
		res.complementFinals();
		final Minimize<LETTER, STATE> mini = new Minimize<>(mServices, mStateFactory, res);
		return mini.getResult();
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
}
