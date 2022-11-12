/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Arrays;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.TimedIndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

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

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final boolean mConditional;
	private final boolean mSymmetric;

	private final TimedIndependenceStatisticsDataProvider mStatistics =
			new TimedIndependenceStatisticsDataProvider(SemanticIndependenceRelation.class);

	private final TransferrerWithVariableCache mTransferrer;

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
			final boolean conditional, final boolean symmetric, final TransferrerWithVariableCache transferrer) {
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
	public Dependence isIndependent(final IPredicate state, final L a, final L b) {
		final var result = toDependence(contains(state, a, b));
		mStatistics.reportQuery(result, mConditional && state != null);
		return result;
	}

	/**
	 * Implements {@link #isIndependent(IPredicate, IAction, IAction)} but returns {@code UNKNOWN} if the solver is
	 * unable to decide commutativity.
	 */
	private LBool contains(final IPredicate state, final L a, final L b) {
		final IPredicate context = mConditional ? state : null;
		if (context instanceof IMLPredicate) {
			// Locations will be ignored. However, using predicates with the same formula but different locations will
			// negatively affect cache efficiency. Hence output a warning message.
			mLogger.warn("Predicates with locations should not be used for independence.");
		}

		mStatistics.startQuery();
		final UnmodifiableTransFormula tfA = getTransFormula(a);
		final UnmodifiableTransFormula tfB = getTransFormula(b);

		// TODO We do composition twice for symmetric relations (in performInclusionCheck). Why?
		final LBool subset = performInclusionCheck(context, tfA, tfB);
		if (!mSymmetric) {
			return subset;
		}

		return and(subset, () -> performInclusionCheck(context, tfB, tfA));
	}

	private UnmodifiableTransFormula getTransFormula(final L a) {
		return getTransFormula(a.getTransformula());
	}

	private UnmodifiableTransFormula getTransFormula(final UnmodifiableTransFormula tf) {
		if (mTransferrer == null) {
			return tf;
		}
		return mTransferrer.transferTransFormula(tf);
	}

	private final LBool performInclusionCheck(IPredicate context, final UnmodifiableTransFormula a,
			final UnmodifiableTransFormula b) {
		if (context != null && SmtUtils.isFalseLiteral(context.getFormula())) {
			return LBool.UNSAT;
		}

		if (mManagedScript.isLocked()) {
			mLogger.warn("Requesting ManagedScript unlock before implication check");
			final boolean unlocked = mManagedScript.requestLockRelease();
			if (!unlocked) {
				mLogger.warn("Failed to unlock ManagedScript. Unable to check independence, returning UNKNOWN.");
				return LBool.UNKNOWN;
			}
		}

		UnmodifiableTransFormula transFormula1 = compose(a, b);
		final UnmodifiableTransFormula transFormula2 = compose(b, a);

		if (context != null) {
			if (mTransferrer != null) {
				context = mTransferrer.transferPredicate(context);
			}
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
				tryAuxVarElimination, false, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE,
				Arrays.asList(first, second));
	}

	private static LBool and(final LBool lhs, final Supplier<LBool> getRhs) {
		if (lhs == LBool.SAT) {
			return LBool.SAT;
		}
		final LBool rhs = getRhs.get();
		if (rhs == LBool.SAT) {
			return LBool.SAT;
		}
		if (lhs == LBool.UNSAT && rhs == LBool.UNSAT) {
			return LBool.UNSAT;
		}
		return LBool.UNKNOWN;
	}

	private static Dependence toDependence(final LBool value) {
		switch (value) {
		case UNSAT:
			return Dependence.INDEPENDENT;
		case SAT:
			return Dependence.DEPENDENT;
		case UNKNOWN:
			return Dependence.UNKNOWN;
		}
		throw new IllegalArgumentException("Unknown value: " + value);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}
}
