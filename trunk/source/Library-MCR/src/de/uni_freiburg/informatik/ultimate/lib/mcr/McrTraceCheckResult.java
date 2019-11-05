package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class McrTraceCheckResult<LETTER extends IIcfgTransition<?>> {
	private final List<LETTER> mTrace;
	private final LBool mIsCorrect;
	private final NestedWordAutomaton<LETTER, IPredicate> mAutomaton;
	private final List<IPredicate> mInterpolants;

	public McrTraceCheckResult(final List<LETTER> trace, final LBool isCorrect,
			final NestedWordAutomaton<LETTER, IPredicate> automaton, final List<IPredicate> interpolants) {
		mTrace = trace;
		mIsCorrect = isCorrect;
		mAutomaton = automaton;
		mInterpolants = interpolants;
	}

	public List<LETTER> getTrace() {
		return mTrace;
	}

	public LBool isCorrect() {
		return mIsCorrect;
	}

	public NestedWordAutomaton<LETTER, IPredicate> getAutomaton() {
		return mAutomaton;
	}

	public List<IPredicate> getInterpolants() {
		return mInterpolants;
	}
}
