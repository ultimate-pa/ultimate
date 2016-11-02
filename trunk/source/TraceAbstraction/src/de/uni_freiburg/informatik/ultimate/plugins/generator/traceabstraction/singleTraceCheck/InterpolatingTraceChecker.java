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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * Check if a trace fulfills a specification and additionally compute a 
 * sequence of interpolants if the trace check was positive.
 * This sequence of interpolants is a Hoare annotation for program that
 * corresponds to this trace (see IInterpolantGenerator).
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class InterpolatingTraceChecker extends TraceChecker implements IInterpolantGenerator {
	
	protected final SimplificationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Data structure that unifies Predicates with respect to its Term.
	 */
	protected final PredicateUnifier mPredicateUnifier;
	protected final PredicateFactory mPredicateFactory;

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
	 * @param simplificationTechnique 
	 * @param xnfConversionTechnique 
	 * @param symbolTable 
	 * @param interpolation 
	 */
	public InterpolatingTraceChecker(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<? extends IAction> trace, final ManagedScript smtManager,
			final ModifiableGlobalVariableManager modifiedGlobals, final AssertCodeBlockOrder assertCodeBlocksIncrementally,
			final IUltimateServiceProvider services, final boolean computeRcfgProgramExecution, 
			final PredicateUnifier predicateUnifier, final ManagedScript tcSmtManager, 
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique, 
			final Boogie2SmtSymbolTable symbolTable) {
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				new DefaultTransFormulas(trace, precondition, postcondition, pendingContexts, modifiedGlobals, false),
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, false, tcSmtManager, symbolTable);
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = predicateUnifier.getPredicateFactory();
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
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
			InterpolationTechnique interpolation);

	private boolean testRelevantVars() {
		boolean result = true;
		final RelevantVariables rv = new RelevantVariables(mNestedFormulas, mModifiedGlobals);
		for (int i = 0; i < mInterpolants.length; i++) {
			final IPredicate itp = mInterpolants[i];
			final Set<IProgramVar> vars = itp.getVars();
			final Set<IProgramVar> frel = rv.getForwardRelevantVariables()[i + 1];
			final Set<IProgramVar> brel = rv.getBackwardRelevantVariables()[i + 1];
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

	@Override
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

	@Override
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
		public boolean contains(final Object o) {
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
		public <T> T[] toArray(final T[] a) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean add(final Integer e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(final Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(final Collection<? extends Integer> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(final Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}

	}



}
