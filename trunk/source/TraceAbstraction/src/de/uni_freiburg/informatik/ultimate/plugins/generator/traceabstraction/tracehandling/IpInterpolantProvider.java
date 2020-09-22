package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 *
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class IpInterpolantProvider<LETTER extends IIcfgTransition<?>> implements IInterpolantProvider<LETTER> {
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateFactory mPredicateFactory;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	private final TaskIdentifier mTaskIdentifier;

	public IpInterpolantProvider(final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IPredicateUnifier predicateUnifier, final PredicateFactory predicateFactory,
			final AssertionOrderModulation<LETTER> assertionOrderModulation, final TaskIdentifier taskIdentifier) {
		mPrefs = prefs;
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = predicateFactory;
		mAssertionOrderModulation = assertionOrderModulation;
		mTaskIdentifier = taskIdentifier;
	}

	@Override
	public IPredicate[] getInterpolants(final IPredicate precondition, final List<LETTER> trace,
			final IPredicate postcondition) {
		final IInterpolatingTraceCheck<LETTER> traceCheck = new IpTcStrategyModulePreferences<>(mTaskIdentifier,
				mPrefs.getUltimateServices(), mPrefs, new StatelessRun<>(trace), precondition, postcondition,
				mAssertionOrderModulation, mPredicateUnifier, mPredicateFactory).getOrConstruct();
		assert traceCheck.isCorrect() == LBool.UNSAT : "The trace " + trace + " is feasible";
		return traceCheck.getInterpolants();
	}
}

class StatelessRun<LETTER, STATE> implements IRun<LETTER, STATE> {
	private final Word<LETTER> mWord;

	public StatelessRun(final List<LETTER> list) {
		@SuppressWarnings("unchecked")
		final LETTER[] array = (LETTER[]) list.toArray(new Object[list.size()]);
		mWord = new Word<>(array);
	}

	@Override
	public Word<LETTER> getWord() {
		return mWord;
	}

	@Override
	public LETTER getSymbol(final int position) {
		return mWord.getSymbol(position);
	}

	@Override
	public int getLength() {
		return mWord.length();
	}

	@Override
	public List<STATE> getStateSequence() {
		throw new UnsupportedOperationException(getClass().getName() + " cannot provide a state sequence");
	}
}
