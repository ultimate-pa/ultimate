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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * Check if a trace fulfills a specification and additionally compute a sequence of interpolants if the trace check was
 * positive. This sequence of interpolants is a Hoare annotation for program that corresponds to this trace (see
 * IInterpolantGenerator).
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class InterpolatingTraceCheck<LETTER extends IAction> extends TraceCheck<LETTER>
		implements IInterpolantGenerator<LETTER> {

	protected final SimplificationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Data structure that unifies Predicates with respect to its Term.
	 */
	protected final IPredicateUnifier mPredicateUnifier;
	protected final PredicateFactory mPredicateFactory;

	protected IPredicate[] mInterpolants;

	protected List<? extends Object> mControlLocationSequence;

	/**
	 * Check if trace fulfills specification given by precondition, postcondition and pending contexts. The
	 * pendingContext maps the positions of pending returns to predicates which define possible variable valuations in
	 * the context to which the return leads the trace.
	 *
	 * @param predicateFactory
	 * @param assertCodeBlocksIncrementally
	 *            If set to false, check-sat is called after all CodeBlocks are asserted. If set to true we use Betims
	 *            heuristic an incrementally assert CodeBlocks and do check-sat until all CodeBlocks are asserted or the
	 *            result to a check-sat is UNSAT.
	 */
	public InterpolatingTraceCheck(final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final NestedWord<LETTER> trace,
			final List<? extends Object> controlLocationSequence, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final ManagedScript tcSmtManager, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final AssertCodeBlockOrder assertCodeBlocksIncrementally,
			final boolean computeRcfgProgramExecution, final boolean collectInterpolatSequenceStatistics,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		super(precondition, postcondition, pendingContexts, trace,
				new DefaultTransFormulas(trace, precondition, postcondition, pendingContexts,
						csToolkit.getOldVarsAssignmentCache(), false),
				services, csToolkit, tcSmtManager, assertCodeBlocksIncrementally, computeRcfgProgramExecution,
				collectInterpolatSequenceStatistics, false);
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = predicateFactory;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mControlLocationSequence = controlLocationSequence;
	}

	/**
	 * Return a sequence of nested interpolants φ_1,...,φ_{n-1} that is inductive for the trace, precondition φ_0, and
	 * postcondition φ_n that were checked last. Interpolants are only available if the trace fulfilled its
	 * specification. The length of the returned sequence is the length of the trace minus one.
	 * <p>
	 * For each two interpolants φ_i, φ_j which are similar (represented by the same term) the traceCheck will use the
	 * same predicate. This means the returned array may contain the same object several times.
	 * <p>
	 * Furthermore throughout the lifetime of the {@link TraceCheck}, the traceCheck will always use one predicate
	 * object for all interpolants which are similar (represented by the same term).
	 * <p>
	 *
	 * @param interpolatedPositions
	 *            Positions at which we compute interpolants. If interpolatedPositions==null each interpolant
	 *            φ_0,...,φ_n is computed. Otherwise for each index i (but zero and n) that does not occur in
	 *            interpolatedPositions φ_i will be an UnknownPredicate.
	 *            <p>
	 *            interpolatedPositions has to be sorted (ascending) and its entries have to be smaller than or equal to
	 *            mTrace.size()
	 * @param mPedicateUnifier
	 *            A IPredicateUnifier in which precondition, postcondition and all pending contexts are representatives.
	 * @param interpolation
	 *            Method that is used to compute the interpolants.
	 */
	protected abstract void computeInterpolants(Set<Integer> interpolatedPositions,
			InterpolationTechnique interpolation);

	private boolean testRelevantVars() {
		boolean result = true;
		final RelevantVariables rv = new RelevantVariables(mNestedFormulas, mCsToolkit.getModifiableGlobalsTable());
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
		}
		throw new UnsupportedOperationException("Interpolants are only available if trace is correct.");
	}

	@Override
	public final IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		final int perfectSequences = (int) getTraceCheckBenchmark()
				.getValue(TraceCheckStatisticsDefinitions.PerfectInterpolantSequences.toString());
		assert perfectSequences == 0 || perfectSequences == 1 || perfectSequences == 2;
		return perfectSequences == 1;
	}

	/**
	 * Integer set implementation that has only a contains method. The method always returns true.
	 *
	 * @author heizmann@informatik.uni-freiburg.de
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
		public boolean contains(final Object obj) {
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
		public <T> T[] toArray(final T[] array) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean add(final Integer elem) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(final Object obj) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsAll(final Collection<?> coll) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(final Collection<? extends Integer> coll) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(final Collection<?> coll) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(final Collection<?> coll) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}
	}
}
