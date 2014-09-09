package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SalomAA;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class DeterminizeRAFA<LETTER extends IElement> implements IOperation<LETTER, IPredicate> {

	NestedWordAutomaton<LETTER, IPredicate> m_result;

	// SmtManager m_smtManager;
	// PredicateUnifier m_predicateUnifier;

	public DeterminizeRAFA(SalomAA<LETTER, IPredicate> salomAA,
	// SmtManager smtManager, PredicateUnifier predicateUnifier
			Object o1, Object o2) {

		// this.m_smtManager = smtManager;
		// this.m_predicateUnifier = predicateUnifier;

		// Instead of bitsets, one could also stick to predicates and make
		// conjunctions -- would this be useful??
		// NestedWordAutomaton<LETTER, BitSet> newNwa = new
		// NestedWordAutomaton<LETTER, BitSet>(salomAA.getAlphabet(),
		NestedWordAutomaton<LETTER, IPredicate> newNwa = new NestedWordAutomaton<LETTER, IPredicate>(
				salomAA.getAlphabet(), Collections.<LETTER> emptySet(), Collections.<LETTER> emptySet(),
				salomAA.getStateFactory());

		ArrayDeque<BitSet> newQ = new ArrayDeque<>();
		newQ.add(salomAA.getFinalStates());

		newNwa.addState(true, salomAA.getAcceptingFunction().applyTo(salomAA.getFinalStates()),
				makePredicateFromBitVector(salomAA.getFinalStates(), salomAA.getStateList()));

		while (!newQ.isEmpty()) {
			BitSet u = newQ.getFirst();
			// newNwa.addState(false,
			// salomAA.getAcceptingFunction().applyTo(u),
			// u);

			for (LETTER l : newNwa.getInternalAlphabet()) {
				BitSet targetState = new BitSet();
				for (int i = 0; i < salomAA.getStateList().size(); i++) {
					IPredicate s = salomAA.getStateList().get(i);
					if (salomAA.getTransitionFunction().get(s).get(l).applyTo(u))
						targetState.set(i);
				}
				if (!newNwa.getStates().contains(targetState)) {
					newQ.add(targetState);
					newNwa.addState(false, salomAA.getAcceptingFunction().applyTo(targetState),
							makePredicateFromBitVector(targetState, salomAA.getStateList()));
				}

				newNwa.addInternalTransition(makePredicateFromBitVector(u, salomAA.getStateList()), l,
						makePredicateFromBitVector(targetState, salomAA.getStateList()));
			}
			newQ.removeFirst();
		}

		m_result = newNwa;
	}

	private IPredicate makePredicateFromBitVector(BitSet finalStates, ArrayList<IPredicate> stateList) {
		// IPredicate pred = m_predicateUnifier.getTruePredicate(); //FIXME:
		// move PredicateUnifier and SMTmanager
		int setBit = finalStates.nextSetBit(0);
		while (setBit != -1) {
			// pred = m_predicateUnifier.getOrConstructPredicate( //FIXME: move
			// PredicateUnifier and SMTmanager
			// m_smtManager.and(pred, stateList.get(setBit)));
			setBit = finalStates.nextSetBit(setBit + 1);
		}
		// return pred;
		return null; // FIXME
	}

	@Override
	public String operationName() {
		return "determinizeAndReverse";
	}

	@Override
	public String startMessage() {
		return "starting determinizeAndReverse";
	}

	@Override
	public String exitMessage() {
		return "exiting determinizeAndReverse";
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() throws OperationCanceledException {
		return m_result;
	}

	@Override
	public boolean checkResult(StateFactory<IPredicate> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return false;
	}

}
