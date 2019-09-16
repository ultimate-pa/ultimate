package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.Arrays;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

public class EprEqualityPredicate extends EprPredicate {

	public EprEqualityPredicate(final FunctionSymbol fs, final EprTheory eprTheory) {
		super(fs, eprTheory);
		// TODO Auto-generated constructor stub
	}


	@Override
	public String toString() {
		return "EprEQPred";
	}

	public DawgState<ApplicationTerm, Boolean> computeOverallSymmetricTransitiveClosureForPositiveEqualityPred(
			final DawgState<ApplicationTerm, Boolean> dawg) {
		final DawgFactory<ApplicationTerm, TermVariable> factory = mEprTheory.getDawgFactory();
		final DawgState<ApplicationTerm, Boolean> result = factory.computeSymmetricTransitiveClosure(dawg);
		return result;
	}

	public DawgState<ApplicationTerm, Boolean> getIrreflexivity() {
		DawgState<ApplicationTerm, EprTheory.TriBool> dawg = getDawg();
		for (Map.Entry<DawgState<ApplicationTerm, EprTheory.TriBool>, DawgLetter<ApplicationTerm>> first : dawg.getTransitions()
				.entrySet()) {
			for (Map.Entry<DawgState<ApplicationTerm, EprTheory.TriBool>, DawgLetter<ApplicationTerm>> second : first.getKey().getTransitions()
				.entrySet()) {
				if (second.getKey().getFinalValue() == EprTheory.TriBool.FALSE) {
					if (!first.getValue().isDisjoint(second.getValue())) {
						// we found a counterexample for reflexivity.  It is enough to return one of them.
						DawgLetter<ApplicationTerm> intersect = first.getValue().intersect(second.getValue());
						@SuppressWarnings("unchecked")
						DawgLetter<ApplicationTerm>[] word = new DawgLetter[] { intersect, intersect };
						return mEprTheory.getDawgFactory().createSingletonPattern(getTermVariablesForArguments(),
								Arrays.asList(word));
					}
				}
			}
		}
		return mEprTheory.getDawgFactory().createConstantDawg(getTermVariablesForArguments(), Boolean.FALSE);
	}
}
