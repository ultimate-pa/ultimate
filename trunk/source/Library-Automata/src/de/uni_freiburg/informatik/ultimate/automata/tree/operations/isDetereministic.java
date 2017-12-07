package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.util.CombinatoricsUtils;

/***
 * Check if a given tree automaton is deterministic.
 * @author mostafa
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class isDetereministic<LETTER extends IRankedLetter, STATE> extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {

	private ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	
	private boolean mResultTreeRun;
	
	public isDetereministic(final AutomataLibraryServices services, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		mTreeAutomaton = tree;
		mResultTreeRun = computeResult();
	}

	private boolean computeResult() {
		for (final List<STATE> src : mTreeAutomaton.getSourceCombinations()) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : mTreeAutomaton.getSuccessors(src)) {
				if (CombinatoricsUtils.iterateAll(mTreeAutomaton.getSuccessors(rule.getSource(), rule.getLetter())).size() != 1) {
					return false;
				}
			}
		}
		return true;
	}
	@Override
	public String startMessage() {
		return "Starting determinism check";
	}

	@Override
	public String exitMessage() {
		return "Exit determinism check";
	}
	@Override
	public Boolean getResult() {
		return mResultTreeRun;
	}

	@Override
	public boolean checkResult(IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
