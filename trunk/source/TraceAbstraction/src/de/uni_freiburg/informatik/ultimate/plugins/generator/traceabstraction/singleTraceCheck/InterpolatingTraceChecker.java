package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

/**
 * Check if a trace fulfills a specification and additionally compute a 
 * sequence of interpolants if the trace check was positive.
 * This sequence of interpolants is a Hoare annotation for program that
 * corresponds to this trace (see IInterpolantGenerator).
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class InterpolatingTraceChecker extends TraceChecker implements IInterpolantGenerator {

	/**
	 * Data structure that unifies Predicates with respect to its Term.
	 */
	protected final PredicateUnifier m_PredicateUnifier;

	protected IPredicate[] m_Interpolants;
	
	protected void unlockSmtManager() {
		super.unlockSmtManager();
		if (m_Interpolants != null) {
			assert !inductivityOfSequenceCanBeRefuted();
		}
	}

	/**
	 * Check if trace fulfills specification given by precondition,
	 * postcondition and pending contexts. The pendingContext maps the positions
	 * of pending returns to predicates which define possible variable
	 * valuations in the context to which the return leads the trace.
	 * 
	 * @param assertCodeBlocksIncrementally
	 *            If set to false, check-sat is called after all CodeBlocks are
	 *            asserted. If set to true we use Betims heuristic an
	 *            incrementally assert CodeBlocks and do check-sat until all
	 *            CodeBlocks are asserted or the result to a check-sat is UNSAT.
	 * @param logger
	 * @param services
	 * @param predicateUnifier 
	 * @param interpolation 
	 */
	public InterpolatingTraceChecker(IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals, AssertCodeBlockOrder assertCodeBlocksIncrementally,
			IUltimateServiceProvider services, boolean computeRcfgProgramExecution, 
			PredicateUnifier predicateUnifier) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				new DefaultTransFormulas(trace, precondition, postcondition, pendingContexts, modifiedGlobals, false),
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, false);
		m_PredicateUnifier = predicateUnifier;
	}


	/**
	 * 
	 * @param interpolation
	 * @return
	 */
	protected int getTotalNumberOfPredicates(INTERPOLATION interpolation) {
		return m_Interpolants != null ? m_Interpolants.length : 0;
	}

	/**
	 * Return a sequence of nested interpolants φ_1,...,φ_{n-1} that is
	 * inductive for the trace, precondition φ_0, and postcondition φ_n that
	 * were checked last. Interpolants are only available if the trace fulfilled
	 * its specification. The length of the returned sequence is the length of
	 * the trace minus one.
	 * <p>
	 * For each two interpolants φ_i, φ_j which are similar (represented by the
	 * same term) the TraceChecker will use the same predicate. This means the
	 * returned array may contain the same object several times.
	 * <p>
	 * Furthermore throughout the lifetime of the TraceChecker, the TraceChecker
	 * will always use one predicate object for all interpolants which are
	 * similar (represented by the same term).
	 * <p>
	 * 
	 * @param interpolatedPositions
	 *            Positions at which we compute interpolants. If
	 *            interpolatedPositions==null each interpolant φ_0,...,φ_n is
	 *            computed. Otherwise for each index i (but zero and n) that
	 *            does not occur in interpolatedPositions φ_i will be an
	 *            UnknownPredicate.
	 *            <p>
	 *            interpolatedPositions has to be sorted (ascending) and its
	 *            entries have to be smaller than or equal to m_Trace.size()
	 * @param predicateUnifier
	 *            A PredicateUnifier in which precondition, postcondition and
	 *            all pending contexts are representatives.
	 * @param interpolation
	 *            Method that is used to compute the interpolants.
	 */
	protected abstract void computeInterpolants(Set<Integer> interpolatedPositions,
			INTERPOLATION interpolation);

	private boolean testRelevantVars() {
		boolean result = true;
		RelevantVariables rv = new RelevantVariables(m_DefaultTransFormulas, m_ModifiedGlobals);
		for (int i = 0; i < m_Interpolants.length; i++) {
			IPredicate itp = m_Interpolants[i];
			Set<BoogieVar> vars = itp.getVars();
			Set<BoogieVar> frel = rv.getForwardRelevantVariables()[i + 1];
			Set<BoogieVar> brel = rv.getBackwardRelevantVariables()[i + 1];
			if (!frel.containsAll(vars)) {
				mLogger.warn("forward relevant variables wrong");
				result = false;
			}
			if (!brel.containsAll(vars)) {
				mLogger.warn("backward relevant variables wrong");
				result = false;
			}
		}
		return result;
	}

	public IPredicate[] getInterpolants() {
		if (isCorrect() == LBool.UNSAT) {
			if (m_Interpolants == null) {
				throw new AssertionError("No Interpolants");
			}
			assert m_Interpolants.length == m_Trace.length() - 1;
			return m_Interpolants;
		} else {
			throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
		}
	}

	public final PredicateUnifier getPredicateUnifier() {
		return m_PredicateUnifier;
	}

	/**
	 * Return true iff m_Interpolants is an inductive sequence of nested
	 * interpolants.
	 */
	protected final boolean inductivityOfSequenceCanBeRefuted() {
		boolean result = false;
		for (int i = 0; i < m_Trace.length(); i++) {
			if (m_Trace.isCallPosition(i)) {
				LBool inductive = m_SmtManager.isInductiveCall(getInterpolant(i - 1), (Call) m_Trace.getSymbol(i),
						getInterpolant(i), true);
				result |= (inductive == LBool.SAT);
			} else if (m_Trace.isReturnPosition(i)) {
				IPredicate context;
				if (m_Trace.isPendingReturn(i)) {
					context = m_PendingContexts.get(i);
				} else {
					int callPosition = ((NestedWord<CodeBlock>) m_Trace).getCallPosition(i);
					context = getInterpolant(callPosition - 1);
				}
				LBool inductive = m_SmtManager.isInductiveReturn(getInterpolant(i - 1), context,
						(Return) m_Trace.getSymbol(i), getInterpolant(i), true);
				result |= (inductive == LBool.SAT);
			} else {
				LBool inductive = m_SmtManager.isInductive(getInterpolant(i - 1), m_Trace.getSymbol(i),
						getInterpolant(i), true);
				result |= (inductive == LBool.SAT);
			}
			assert !result;
		}
		return result;
	}

	private final IPredicate getInterpolant(int i) {
		if (i == -1) {
			return m_Precondition;
		} else if (i == m_Interpolants.length) {
			return m_Postcondition;
		} else {
			return m_Interpolants[i];
		}
	}



	/**
	 * Set<Integer> implementation that has only a contains method. The method
	 * always returns true;
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 * 
	 */
	public static class AllIntegers implements Set<Integer> {

		@Override
		public int size() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isEmpty() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean contains(Object o) {
			return true;
		}

		@Override
		public Iterator<Integer> iterator() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Object[] toArray() {
			throw new UnsupportedOperationException();
		}

		@Override
		public <T> T[] toArray(T[] a) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean add(Integer e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(Collection<? extends Integer> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}

	}



}