package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class MCR<LETTER extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<LETTER> {
	private final ILogger mLogger;
	private final IPredicateUnifier mPredicateUnifier;
	private final IHoareTripleChecker mHtc;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;

	private final HashRelation<LETTER, String> mReads2Variables;
	private final HashRelation<LETTER, String> mWrites2Variables;
	private final HashRelation<String, LETTER> mVariables2Writes;
	private final HashRelation<LETTER, LETTER> mMhbInverse;
	private final Map<LETTER, Map<String, LETTER>> mPreviousWrite;
	private final Map<LETTER, TermVariable> mActions2TermVars;

	private final List<LETTER> mTrace;
	private final LBool mIsCorrect;
	private final NestedWordAutomaton<LETTER, IPredicate> mAutomaton;
	private final ITraceCheckFactory<LETTER> mTraceCheckFactory;

	public MCR(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final List<LETTER> trace,
			final ITraceCheckFactory<LETTER> traceCheckFactory) {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mHtc = htc;
		mServices = prefs.getUltimateServices();
		mManagedScript = prefs.getCfgSmtToolkit().getManagedScript();
		mTraceCheckFactory = traceCheckFactory;
		mTruePred = predicateUnifier.getOrConstructPredicate(mManagedScript.getScript().term("true"));
		mFalsePred = predicateUnifier.getOrConstructPredicate(mManagedScript.getScript().term("false"));
		mReads2Variables = new HashRelation<>();
		mWrites2Variables = new HashRelation<>();
		mVariables2Writes = new HashRelation<>();
		mMhbInverse = new HashRelation<>();
		mPreviousWrite = new HashMap<>();
		mActions2TermVars = new HashMap<>();
		// Explore all the interleavings of trace
		final Triple<List<LETTER>, LBool, NestedWordAutomaton<LETTER, IPredicate>> result = exploreInterleavings(trace);
		mTrace = result.getFirst();
		mIsCorrect = result.getSecond();
		mAutomaton = result.getThird();
	}

	private Triple<List<LETTER>, LBool, NestedWordAutomaton<LETTER, IPredicate>>
			exploreInterleavings(final List<LETTER> initialTrace) {
		getReadsAndWrites();
		final LinkedList<List<LETTER>> queue = new LinkedList<>();
		final Set<List<LETTER>> visited = new HashSet<>();
		queue.add(initialTrace);
		// TODO: Initialize empty automaton
		final NestedWordAutomaton<LETTER, IPredicate> automaton = null;
		while (!queue.isEmpty()) {
			final List<LETTER> trace = queue.remove();
			if (visited.contains(trace)) {
				continue;
			}
			visited.add(trace);
			preprocess(trace);
			final IPredicate[] interpolants;
			// TODO: if trace in mAutomaton
			if (false) {
				// TODO: Get the interpolants from mAutomaton
				interpolants = null;
			} else {
				final ITraceCheck traceCheck = mTraceCheckFactory.getTraceCheck(trace);
				final LBool isCorrect = traceCheck.isCorrect();
				if (isCorrect != LBool.UNSAT) {
					// We found a feasible error trace
					return new Triple<>(trace, isCorrect, automaton);
				}
				interpolants = getInterpolants(traceCheck);
				final NestedWordAutomaton<LETTER, String> mcrAutomaton = getMcrAutomaton(trace, interpolants);
				// TOOD: Get the interpolants from mcrAutomaton (DAG-interpolation?) and add them to automaton
			}
			queue.addAll(generateSeedInterleavings(trace, interpolants));
		}
		return new Triple<>(initialTrace, LBool.UNSAT, automaton);
	}

	@SuppressWarnings("unchecked")
	private IPredicate[] getInterpolants(final ITraceCheck traceCheck) {
		assert traceCheck instanceof IInterpolantGenerator;
		return ((IInterpolantGenerator<LETTER>) traceCheck).getInterpolants();
	}

	private void getReadsAndWrites() {
		for (final LETTER action : mTrace) {
			if (action instanceof IcfgEdge) {
				final ReadWriteFinder finder = new ReadWriteFinder((IcfgEdge) action);
				mReads2Variables.addAllPairs(action, finder.getReadVars());
				for (final String var : finder.getWrittenVars()) {
					mVariables2Writes.addPair(var, action);
				}
			}
		}
	}

	private void preprocess(final List<LETTER> trace) {
		mMhbInverse.clear();
		mPreviousWrite.clear();
		mActions2TermVars.clear();
		// TODO: How to construct the MHB relation?
		final Map<String, LETTER> lastWrittenBy = new HashMap<>();
		for (final LETTER action : trace) {
			final Set<String> reads = mReads2Variables.getImage(action);
			if (reads.isEmpty()) {
				continue;
			}
			final Map<String, LETTER> previousWrites = new HashMap<>();
			for (final String read : reads) {
				previousWrites.put(read, lastWrittenBy.get(read));
			}
			mPreviousWrite.put(action, previousWrites);
			for (final String written : mWrites2Variables.getImage(action)) {
				lastWrittenBy.put(written, action);
			}
		}
		for (final LETTER action : trace) {
			// TODO: There might be duplicate action, is this a problem?
			mActions2TermVars.put(action,
					mManagedScript.getScript().variable(action.toString(), SmtSortUtils.getIntSort(mManagedScript)));
		}
	}

	// TODO: Avoid duplicates by caching?
	private Collection<List<LETTER>> generateSeedInterleavings(final List<LETTER> trace,
			final IPredicate[] interpolants) {
		final Script script = mManagedScript.getScript();
		final List<List<LETTER>> result = new ArrayList<>();
		for (final LETTER read : trace) {
			final Set<String> readVars = mReads2Variables.getImage(read);
			if (readVars.isEmpty()) {
				continue;
			}
			final Term preRead = getPrecondition(read, trace, interpolants);
			for (final String var : readVars) {
				for (final LETTER write : mVariables2Writes.getImage(var)) {
					if (writeDoesNotImply(write, preRead, trace, interpolants) == LBool.UNSAT) {
						continue;
					}
					script.push(1);
					// If the constraints are satisfiable, add a trace based on them
					script.assertTerm(getConstraints(trace, read, write, interpolants));
					if (script.checkSat() == LBool.SAT) {
						result.add(constructTraceFromModel(script.getModel()));
					}
					script.pop(1);
				}
			}
		}
		return result;
	}

	/**
	 * Encode a new trace in a formula, that is equivalent to trace, except that write happens right before read.
	 */
	// TODO: All the following methods with formulae can be extracted and this can be the only public method
	private Term getConstraints(final List<LETTER> trace, final LETTER read, final LETTER write,
			final IPredicate[] interpolants) {
		final Script script = mManagedScript.getScript();
		final List<Term> conjuncts = new ArrayList<>();
		// Add the MHB-constraints
		for (final Entry<LETTER, LETTER> entry : mMhbInverse.entrySet()) {
			final TermVariable var1 = mActions2TermVars.get(entry.getValue());
			final TermVariable var2 = mActions2TermVars.get(entry.getKey());
			conjuncts.add(SmtUtils.less(script, var1, var2));
		}
		conjuncts.addAll(getRwConstraints(read, trace, interpolants));
		conjuncts.addAll(getRwConstraints(write, trace, interpolants));
		conjuncts.addAll(getValueConstraints(read, getPostcondition(write, trace, interpolants), trace, interpolants));
		return SmtUtils.and(script, conjuncts);
	}

	private Collection<Term> getRwConstraints(final LETTER action, final List<LETTER> trace,
			final IPredicate[] interpolants) {
		final List<Term> result = new ArrayList<>();
		for (final LETTER prevRead : mMhbInverse.getImage(action)) {
			final Term preRead = getPrecondition(prevRead, trace, interpolants);
			result.addAll(getValueConstraints(prevRead, preRead, trace, interpolants));
		}
		return result;
	}

	private Collection<Term> getValueConstraints(final LETTER read, final Term constraint, final List<LETTER> trace,
			final IPredicate[] interpolants) {
		final Script script = mManagedScript.getScript();
		final List<Term> result = new ArrayList<>();
		final TermVariable readVar = mActions2TermVars.get(read);
		for (final String var : mReads2Variables.getImage(read)) {
			final List<Term> disjuncts = new ArrayList<>();
			for (final LETTER write : mVariables2Writes.getImage(var)) {
				if (writeDoesNotImply(write, constraint, trace, interpolants) != LBool.UNSAT) {
					continue;
				}
				final List<Term> conjuncts = new ArrayList<>();
				final TermVariable writeVar = mActions2TermVars.get(write);
				conjuncts.add(SmtUtils.less(script, writeVar, readVar));
				for (final LETTER otherWrite : mVariables2Writes.getImage(var)) {
					// TODO: Can we cache writeDoesNotImply?
					// TODO: Is this the correct condition?
					if (write.equals(otherWrite)
							|| writeDoesNotImply(otherWrite, constraint, trace, interpolants) == LBool.UNSAT) {
						continue;
					}
					final TermVariable otherWriteVar = mActions2TermVars.get(otherWrite);
					final Term beforeWrite = SmtUtils.less(script, otherWriteVar, writeVar);
					final Term afterRead = SmtUtils.less(script, readVar, otherWriteVar);
					conjuncts.add(SmtUtils.or(script, beforeWrite, afterRead));
				}
				disjuncts.add(SmtUtils.and(script, conjuncts));
			}
			result.add(SmtUtils.or(mManagedScript.getScript(), disjuncts));
		}
		return result;
	}

	private LBool writeDoesNotImply(final LETTER write, final Term constraint, final List<LETTER> trace,
			final IPredicate[] interpolants) {
		final Script script = mManagedScript.getScript();
		script.assertTerm(getPostcondition(write, trace, interpolants));
		script.assertTerm(SmtUtils.not(script, constraint));
		final LBool result = script.checkSat();
		script.pop(2);
		return result;
	}

	private List<LETTER> constructTraceFromModel(final Model model) {
		return mActions2TermVars.keySet().stream()
				.sorted((a1, a2) -> getIntValue(model, a1).compareTo(getIntValue(model, a2)))
				.collect(Collectors.toList());
	}

	// TODO: Is this the correct way?
	private BigInteger getIntValue(final Model model, final LETTER action) {
		final Term term = model.evaluate(mActions2TermVars.get(action));
		assert term instanceof ConstantTerm;
		final Object value = ((ConstantTerm) term).getValue();
		if (value instanceof BigInteger) {
			return (BigInteger) value;
		}
		assert value instanceof Rational;
		final Rational rational = (Rational) value;
		assert rational.denominator().equals(BigInteger.ONE);
		return rational.numerator();
	}

	private NestedWordAutomaton<LETTER, String> getMcrAutomaton(final List<LETTER> trace,
			final IPredicate[] interpolants) {
		// TODO: Create the MCR automaton from trace (using intersection and removing all self-loops?)
		return null;
	}

	private Term getPrecondition(final LETTER action, final List<LETTER> trace, final IPredicate[] interpolants) {
		// TODO: Use mPreviousWrite?
		return interpolants[trace.indexOf(action)].getFormula();
	}

	private Term getPostcondition(final LETTER action, final List<LETTER> trace, final IPredicate[] interpolants) {
		return interpolants[trace.indexOf(action) + 1].getFormula();
	}

	public NestedWordAutomaton<LETTER, IPredicate> getAutomaton() {
		return mAutomaton;
	}

	@Override
	public List<LETTER> getTrace() {
		return mTrace;
	}

	@Override
	public IPredicate[] getInterpolants() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LBool isCorrect() {
		return mIsCorrect;
	}

	@Override
	public IPredicate getPrecondition() {
		return mTruePred;
	}

	@Override
	public IPredicate getPostcondition() {
		return mFalsePred;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIsCorrect != LBool.SAT;
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ToolchainCanceledException getToolchainCanceledExpection() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return false;
	}

	private class ReadWriteFinder extends RCFGEdgeVisitor {
		private final Set<String> mReadVars;
		private final Set<String> mWrittenVars;

		@Override
		protected void visit(final StatementSequence c) {
			// TODO: Statement is not API
			// for (final Statement s : c.getStatements()) {
			// if (s instanceof AssumeStatement) {
			// // TODO: For reads visit ((AssumeStatement)s).getFormula()
			// }
			// if (s instanceof AssignmentStatement) {
			// AssignmentStatement a = (AssignmentStatement) s;
			// // TODO: For writes visit a.getLhs()
			// // TODO: For reads visit a.getRhs()
			// }
			// // TODO: Other cases?
			// }
			super.visit(c);
		}

		ReadWriteFinder(final IcfgEdge action) {
			mReadVars = new HashSet<>();
			mWrittenVars = new HashSet<>();
			visit(action);
		}

		Set<String> getReadVars() {
			return mReadVars;
		}

		Set<String> getWrittenVars() {
			return mWrittenVars;
		}
	}

	public interface ITraceCheckFactory<LETTER> {
		ITraceCheck getTraceCheck(final List<LETTER> trace);
	}
}
