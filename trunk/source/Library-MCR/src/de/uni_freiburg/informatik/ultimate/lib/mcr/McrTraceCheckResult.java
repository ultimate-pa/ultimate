package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class McrTraceCheckResult<L extends IIcfgTransition<?>> {
	private final List<L> mTrace;
	private final LBool mIsCorrect;
	private final Collection<QualifiedTracePredicates> mQualifiedTracePredicates;
	private final IStatisticsDataProvider mStatistics;
	private final IProgramExecution<L, Term> mExecution;

	private NestedWordAutomaton<L, IPredicate> mAutomaton;

	private McrTraceCheckResult(final List<L> trace, final LBool isCorrect,
			final Collection<QualifiedTracePredicates> qualifiedTracePredicates,
			final IStatisticsDataProvider statistics, final IProgramExecution<L, Term> execution) {
		mTrace = trace;
		mIsCorrect = isCorrect;
		mQualifiedTracePredicates = qualifiedTracePredicates;
		mStatistics = statistics;
		mExecution = execution;
	}

	public static <L extends IIcfgTransition<?>> McrTraceCheckResult<L> constructFeasibleResult(final List<L> trace,
			final LBool isCorrect, final IStatisticsDataProvider statistics,
			final IProgramExecution<L, Term> execution) {
		return new McrTraceCheckResult<>(trace, isCorrect, Collections.emptyList(), statistics, execution);
	}

	public static <L extends IIcfgTransition<?>> McrTraceCheckResult<L> constructInfeasibleResult(final List<L> trace,
			final Collection<QualifiedTracePredicates> qualifiedTracePredicates,
			final IStatisticsDataProvider statistics) {
		return new McrTraceCheckResult<>(trace, LBool.UNSAT, qualifiedTracePredicates, statistics, null);
	}

	public List<L> getTrace() {
		return mTrace;
	}

	public LBool isCorrect() {
		return mIsCorrect;
	}

	public void setAutomaton(final NestedWordAutomaton<L, IPredicate> automaton) {
		mAutomaton = automaton;
	}

	public NestedWordAutomaton<L, IPredicate> getAutomaton() {
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

	public IProgramExecution<L, Term> getExecution() {
		return mExecution;
	}

	public boolean providesExecution() {
		return mExecution != null;
	}
}
