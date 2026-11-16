/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.afa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;

public class AfaConditionalCommutativityChecker<L extends IAction> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;
	private final TransFormulaSymmetricDifference<L> mDifference;
	private final ICopyActionFactory<L> mCopyFactory;
	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final Function<Counterexample<L>, IRefinementStrategy<L>> mBuildStrategy;

	public AfaConditionalCommutativityChecker(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final ICopyActionFactory<L> copyFactory,
			final Function<Counterexample<L>, IRefinementStrategy<L>> buildStrategy,
			final IIndependenceRelation<IPredicate, L> independenceRelation) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(getClass());
		mDifference = new TransFormulaSymmetricDifference<>(mServices, mManagedScript);
		mCopyFactory = copyFactory;
		mBuildStrategy = buildStrategy;
		mIndependenceRelation = independenceRelation;
	}

	public Result<L> checkCommutativity(final NestedWord<L> trace, final int index, final IPredicate state,
			final List<?> controlConfigurations, final L templateLetter) {

		if (index < 0 || index + 1 >= trace.length()) {
			throw new IllegalArgumentException("Index does not identify two consecutive trace letters");
		}

		final L letter1 = trace.getSymbol(index);
		final L letter2 = trace.getSymbol(index + 1);

		final Dependence dependence = mIndependenceRelation.isIndependent(state, letter1, letter2);

		if (dependence == Dependence.INDEPENDENT) {
			return new Result<>(ResultType.ALREADY_INDEPENDENT);
		}

		// Compute the symmetric difference
		final UnmodifiableTransFormula difference = mDifference.compute(letter1, letter2);

		return checkDifferenceTrace(trace, index, controlConfigurations, templateLetter, difference);
	}

	private Result<L> checkDifferenceTrace(final NestedWord<L> trace, final int index,
			final List<?> controlConfigurations, final L templateLetter, final UnmodifiableTransFormula difference) {

		if (index < 0 || index + 1 >= trace.length()) {
			throw new IllegalArgumentException("Index does not identify two consecutive trace letters");
		}

		if (controlConfigurations.size() != trace.length() + 1) {
			throw new IllegalArgumentException("Unexpected number of control configurations");
		}

		// Create a letter representing the symmetric difference
		final L differenceLetter = mCopyFactory.copy(templateLetter, difference, null);

		// Replace the two consecutive letters by the difference letter
		final NestedWord<L> prefix = trace.getSubWord(0, index);
		final NestedWord<L> replacement = NestedWord.nestedWord(new Word<>(differenceLetter));
		final NestedWord<L> suffix = trace.getSubWord(index + 2, trace.length());

		final NestedWord<L> modifiedTrace = prefix.concatenate(replacement).concatenate(suffix);

		// Remove the control configuration between the two replaced letters
		final List<Object> modifiedControlConfigurations = new ArrayList<>(controlConfigurations);
		modifiedControlConfigurations.remove(index + 1);

		final Counterexample<L> ctex = new Counterexample<>(modifiedTrace, modifiedControlConfigurations);

		// Do the trace check
		final IRefinementStrategy<L> strategy = mBuildStrategy.apply(ctex);
		final var afe = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy);
		final var result = afe.getResult();

		return switch (result.getCounterexampleFeasibility()) {
		case UNKNOWN -> new Result<>(ResultType.UNKNOWN_CHECK);
		case SAT -> new Result<>(ResultType.FAILURE);
		case UNSAT -> {
			if (!result.somePerfectSequenceFound()) {
				yield new Result<>(ResultType.PROOF_IMPERFECT);
			}
			yield new Result<>(result);
		}
		};
	}

	public static final class Result<L extends IAction> {
		private final ResultType mType;
		private final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> mRefinementResult;

		private Result(final ResultType type) {
			mType = type;
			mRefinementResult = null;
			assert !isSuccess() : "successful result must have refinement result";
		}

		private Result(final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> refinementResult) {
			mType = ResultType.SUCCESS;
			mRefinementResult = Objects.requireNonNull(refinementResult);
		}

		public boolean isSuccess() {
			return mType == ResultType.SUCCESS;
		}

		public ResultType getType() {
			return mType;
		}

		public IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> getRefinementResult() {
			assert mRefinementResult != null : "No proof of commutativity found";
			return mRefinementResult;
		}
	}

	public enum ResultType {
		ALREADY_INDEPENDENT, PROOF_IMPERFECT, UNKNOWN_CHECK, FAILURE, SUCCESS
	}
}
