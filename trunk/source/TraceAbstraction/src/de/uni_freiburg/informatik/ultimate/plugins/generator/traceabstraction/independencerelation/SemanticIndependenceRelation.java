/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * An independence relation that implements an SMT-based inclusion or equality check on the semantics.
 *
 * It is recommended to wrap this relation in a {@link CachedIndependenceRelation} for better performance.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters whose independence is checked.
 */

public class SemanticIndependenceRelation<L extends IAction> implements IIndependenceRelation<IPredicate, L> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private static final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private static final XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final boolean mConditional;
	private final boolean mSymmetric;

	private long mPositiveQueries;
	private long mNegativeQueries;
	private long mUnknownQueries;
	private long mComputationTimeNano;

	private final Map<IProgramVarOrConst, IProgramVarOrConst> mTransferCache = new HashMap<>();
	private final TermTransferrer mTransferrer;

	public SemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean conditional, final boolean symmetric) {
		this(services, mgdScript, conditional, symmetric, null);
	}

	/**
	 * Create a new variant of the semantic independence relation.
	 *
	 * @param conditional
	 *            If set to true, the relation will be conditional: It will use the given {@link IPredicate} as context
	 *            to enable additional commutativity. This subsumes the non-conditional variant.
	 * @param symmetric
	 *            If set to true, the relation will check for full commutativity. If false, only semicommutativity is
	 *            checked, which subsumes full commutativity.
	 */
	public SemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean conditional, final boolean symmetric, final TermTransferrer transferrer) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mTransferrer = transferrer;

		mConditional = conditional;
		mSymmetric = symmetric;
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(final IPredicate state, final L a, final L b) {
		final IPredicate context = mConditional ? state : null;
		if (context instanceof IMLPredicate) {
			// Locations will be ignored. However, using predicates with the same formula but different locations will
			// negatively affect cache efficiency. Hence output a warning message.
			mLogger.warn("Predicates with locations should not be used for independence.");
		}

		final long startTime = System.nanoTime();

		final UnmodifiableTransFormula tfA = getTransFormula(a);
		final UnmodifiableTransFormula tfB = getTransFormula(b);

		final LBool subset = performInclusionCheck(context, tfA, tfB);
		final LBool result;
		if (mSymmetric && subset != LBool.SAT) {
			final LBool superset = performInclusionCheck(context, tfB, tfA);
			if (subset == LBool.UNSAT && superset == LBool.UNSAT) {
				result = LBool.UNSAT;
			} else if (superset == LBool.SAT) {
				result = LBool.SAT;
			} else {
				result = LBool.UNKNOWN;
			}
		} else {
			result = subset;
		}
		final long checkTime = System.nanoTime() - startTime;
		mComputationTimeNano += checkTime;

		mLogger.debug("Independence Inclusion Check Time: %d ms", checkTime / 1_000_000);
		if (checkTime > 1_000_000_000) {
			// For queries that take more than 1s, report details.
			mLogger.warn("Expensive independence query (%d ms) for statements %s and %s under condition %s",
					checkTime / 1_000_000, a, b, context);
		}

		switch (result) {
		case SAT:
			mNegativeQueries++;
			break;
		case UNKNOWN:
			mUnknownQueries++;
			break;
		case UNSAT:
			mPositiveQueries++;
			break;
		default:
			throw new AssertionError("Unexpected inclusion check result: " + result);
		}
		return result == LBool.UNSAT;
	}

	private UnmodifiableTransFormula getTransFormula(final L a) {
		return getTransFormula(a.getTransformula());
	}

	private UnmodifiableTransFormula getTransFormula(final UnmodifiableTransFormula tf) {
		if (mTransferrer == null) {
			return tf;
		}
		return TransFormulaBuilder.transferTransformula(mTransferrer, mManagedScript, mTransferCache, tf)
				.getTransformula();
	}

	private final LBool performInclusionCheck(final IPredicate context, final UnmodifiableTransFormula a,
			final UnmodifiableTransFormula b) {
		if (context != null && SmtUtils.isFalseLiteral(context.getFormula())) {
			return LBool.UNSAT;
		}

		if (mManagedScript.isLocked()) {
			final long releaseStart = System.currentTimeMillis();
			mLogger.warn("Requesting ManagedScript unlock before implication check");
			final boolean unlocked = mManagedScript.requestLockRelease();
			final long releaseEnd = System.currentTimeMillis();
			mLogger.debug("Script Release Time: " + (releaseEnd - releaseStart) + "ms");
			if (!unlocked) {
				mLogger.warn("Failed to unlock ManagedScript. Unable to check independence, returning UNKNOWN.");
				return LBool.UNKNOWN;
			}
		}

		UnmodifiableTransFormula transFormula1 = compose(a, b);
		final UnmodifiableTransFormula transFormula2 = compose(b, a);

		if (context != null) {
			final UnmodifiableTransFormula guard =
					TransFormulaBuilder.constructTransFormulaFromPredicate(context, mManagedScript);
			transFormula1 = compose(getTransFormula(guard), transFormula1);
		}
		return TransFormulaUtils.checkImplication(transFormula1, transFormula2, mManagedScript);
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;

		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		final boolean tryAuxVarElimination = false;

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify,
				tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique,
				Arrays.asList(first, second));
	}

	public long getPositiveQueries() {
		return mPositiveQueries;
	}

	public long getNegativeQueries() {
		return mNegativeQueries;
	}

	public long getUnknownQueries() {
		return mUnknownQueries;
	}

	public long getComputationTimeNano() {
		return mComputationTimeNano;
	}

	/**
	 * An independence relation that can be used as a wrapper around conditional instances of
	 * {@link SemanticIndependenceRelation}. It eliminates useless conditions, leading to simpler SMT queries. If the
	 * results of the {@link SemanticIndependenceRelation} are cached, this wrapper should instead wrap the
	 * {@link CachedIndependenceRelation}, in order to also improve caching efficiency.
	 *
	 * A condition is deemed useless for the independence of statements a and b, if the condition is consistent
	 * (satisfiable), but does not contain any free variable that is read by either a or b.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters being cached.
	 */
	public static final class ConditionEliminator<L extends IAction> implements IIndependenceRelation<IPredicate, L> {

		private final IIndependenceRelation<IPredicate, L> mUnderlying;
		private final Predicate<IPredicate> mIsInconsistent;

		/**
		 * Creates a new wrapper around a given independence relation.
		 *
		 * @param underlying
		 *            The underlying independence relation to which queries will be delegated (after possibly
		 *            eliminating the condition). This relation should be able to handle null as condition.
		 * @param isInconsistent
		 *            An inconsistency test to be used for conditions given to this relation. To truly gain efficiency,
		 *            this test should be very efficient. It must return true for all inconsistent conditions this
		 *            relation is used on, in order to ensure soundness. It may over-approximate inconsistency, i.e.,
		 *            also return true for some consistent predicates -- this affects efficiency but not soundness.
		 */
		public ConditionEliminator(final IIndependenceRelation<IPredicate, L> underlying,
				final Predicate<IPredicate> isInconsistent) {
			assert underlying.isConditional() : "Condition elimination for non-conditional relations is useless";
			mUnderlying = underlying;
			mIsInconsistent = isInconsistent;
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlying.isSymmetric();
		}

		@Override
		public boolean isConditional() {
			return mUnderlying.isConditional();
		}

		@Override
		public boolean contains(final IPredicate state, final L a, final L b) {
			return mUnderlying.contains(normalize(state, a, b), a, b);
		}

		private IPredicate normalize(final IPredicate condition, final L a, final L b) {
			final Term formula = condition.getFormula();

			// Syntactically determine if condition is possibly relevant to independence.
			final Set<TermVariable> inputVars = Stream
					.concat(a.getTransformula().getInVars().keySet().stream(),
							b.getTransformula().getInVars().keySet().stream())
					.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
			final boolean isRelevant = Arrays.stream(formula.getFreeVars()).anyMatch(inputVars::contains);
			if (!isRelevant && !mIsInconsistent.test(condition)) {
				// Fall back to independence without condition.
				return null;
			}

			return condition;
		}

	}
}
