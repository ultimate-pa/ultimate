package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/***
 * Check if a given tree automaton is total or not.
 * @author mostafa
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class isTotal<LETTER extends IRankedLetter, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	
	private final boolean mResultTreeRun;
	
	public isTotal(AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		mTreeAutomaton = tree;
		// mResultTreeRun = computeResult();
		mResultTreeRun = computeResult() && new isDetereministic<>(services, mTreeAutomaton).getResult();
	}

	private boolean computeResult() {
		final Map<LETTER, Set<List<STATE>>> mp = new HashMap<>();
		for (final List<STATE> src : mTreeAutomaton.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getSuccessors(src)) {
				final LETTER letter = rule.getLetter();
				if (!mp.containsKey(letter)) {
					mp.put(letter, new HashSet<>());
				}
				mp.get(letter).add(rule.getSource());
			}
		}
		final int states = mTreeAutomaton.getStates().size();
		for (final LETTER letter : mTreeAutomaton.getAlphabet()) {
			if (!mp.containsKey(letter)) {
				return false;
			}
			int siz = mp.get(letter).size();
			for (int rank = letter.getRank(); rank > 0; --rank, siz /= states) {
				if (siz % states != 0) {
					return false;
				}
			}
			if (siz != 1) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public Boolean getResult() {
		return mResultTreeRun;
	}

	@Override
	public String startMessage() {
		return "Starting totality check";
	}

	@Override
	public String exitMessage() {
		return "Exit totality check";
	}

	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
