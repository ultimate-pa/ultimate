/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
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
	protected final PredicateUnifier mPredicateUnifier;

	protected IPredicate[] mInterpolants;
	
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
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<? extends IAction> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals, AssertCodeBlockOrder assertCodeBlocksIncrementally,
			IUltimateServiceProvider services, boolean computeRcfgProgramExecution, 
			PredicateUnifier predicateUnifier, SmtManager tcSmtManager) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				new DefaultTransFormulas(trace, precondition, postcondition, pendingContexts, modifiedGlobals, false),
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, false, tcSmtManager);
		mPredicateUnifier = predicateUnifier;
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
	 *            entries have to be smaller than or equal to mTrace.size()
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
		RelevantVariables rv = new RelevantVariables(mNestedFormulas, mModifiedGlobals);
		for (int i = 0; i < mInterpolants.length; i++) {
			IPredicate itp = mInterpolants[i];
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
			if (mInterpolants == null) {
				throw new AssertionError("No Interpolants");
			}
			assert mInterpolants.length == mTrace.length() - 1;
			return mInterpolants;
		} else {
			throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
		}
	}

	public final PredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
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
