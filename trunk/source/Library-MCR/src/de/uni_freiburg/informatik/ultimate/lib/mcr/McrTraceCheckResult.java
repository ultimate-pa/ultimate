package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class McrTraceCheckResult<LETTER extends IIcfgTransition<?>> {
	private final List<LETTER> mTrace;
	private final LBool mIsCorrect;
	private final Collection<QualifiedTracePredicates> mQualifiedTracePredicates;
	private final IStatisticsDataProvider mStatistics;
	private final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mExecution;

	private NestedWordAutomaton<LETTER, IPredicate> mAutomaton;

	private McrTraceCheckResult(final List<LETTER> trace, final LBool isCorrect,
			final Collection<QualifiedTracePredicates> qualifiedTracePredicates,
			final IStatisticsDataProvider statistics,
			final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> execution) {
		mTrace = trace;
		mIsCorrect = isCorrect;
		mQualifiedTracePredicates = qualifiedTracePredicates;
		mStatistics = statistics;
		mExecution = execution;
	}

	public static <LETTER extends IIcfgTransition<?>> McrTraceCheckResult<LETTER> constructFeasibleResult(
			final List<LETTER> trace, final LBool isCorrect, final IStatisticsDataProvider statistics,
			final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> execution) {
		return new McrTraceCheckResult<>(trace, isCorrect, Collections.emptyList(), statistics, execution);
	}

	public static <LETTER extends IIcfgTransition<?>> McrTraceCheckResult<LETTER> constructInfeasibleResult(
			final List<LETTER> trace, final Collection<QualifiedTracePredicates> qualifiedTracePredicates,
			final IStatisticsDataProvider statistics) {
		return new McrTraceCheckResult<>(trace, LBool.UNSAT, qualifiedTracePredicates, statistics, null);
	}

	public List<LETTER> getTrace() {
		return mTrace;
	}

	public LBool isCorrect() {
		return mIsCorrect;
	}

	public void setAutomaton(final NestedWordAutomaton<LETTER, IPredicate> automaton) {
		mAutomaton = automaton;
	}

	public NestedWordAutomaton<LETTER, IPredicate> getAutomaton() {
		return mAutomaton;
	}

	public IPredicate[] getInterpolants() {
		if (mQualifiedTracePredicates.isEmpty()) {
			return null;
		}
		// TODO: Look for perfect predicates instead?
		final List<IPredicate> predicates = mQualifiedTracePredicates.stream().findAny().get().getPredicates();
		return predicates.toArray(new IPredicate[predicates.size()]);
	}

	public Collection<QualifiedTracePredicates> getQualifiedTracePredicates() {
		return mQualifiedTracePredicates;
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getExecution() {
		return mExecution;
	}

	public boolean providesExecution() {
		return mExecution != null;
	}
}
