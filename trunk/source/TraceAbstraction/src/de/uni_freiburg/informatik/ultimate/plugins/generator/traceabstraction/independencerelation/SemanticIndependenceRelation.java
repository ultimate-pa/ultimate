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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * An independence relation that implements an SMT-based inclusion or equality check on the semantics.
 *
 * It is recommended to wrap this relation in a {@link CachedIndependenceRelation} for better performance.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */

public class SemanticIndependenceRelation<L extends IAction> implements IIndependenceRelation<IPredicate, L> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final static SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final static XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final boolean mConditional;
	private final boolean mSymmetric;

	private long mPositiveQueries;
	private long mNegativeQueries;
	private long mUnknownQueries;
	private long mComputationTimeNano;

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
			final boolean conditional, final boolean symmetric) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

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
		final long startTime = System.nanoTime();
		final IPredicate context = mConditional ? state : null;
		final LBool subset = performInclusionCheck(context, a, b);

		final LBool result;
		if (mSymmetric) {
			final LBool superset = performInclusionCheck(context, b, a);
			if (subset == LBool.UNSAT && superset == LBool.UNSAT) {
				result = LBool.UNSAT;
			} else if (subset == LBool.UNKNOWN || superset == LBool.UNKNOWN) {
				result = LBool.UNKNOWN;
			} else {
				result = LBool.SAT;
			}
		} else {
			result = subset;
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
			throw new AssertionError();
		}
		mComputationTimeNano += (System.nanoTime() - startTime);
		return result == LBool.UNSAT;
	}

	private final LBool performInclusionCheck(final IPredicate context, final L a, final L b) {
		UnmodifiableTransFormula transFormula1 = compose(a.getTransformula(), b.getTransformula());
		final UnmodifiableTransFormula transFormula2 = compose(b.getTransformula(), a.getTransformula());

		if (context != null) {
			// TODO: This represents conjunction with guard (precondition) as composition
			// with assume. Is this a good way?
			final UnmodifiableTransFormula guard =
					TransFormulaBuilder.constructTransFormulaFromPredicate(context, mManagedScript);
			transFormula1 = compose(guard, transFormula1);
		}

		final LBool result = TransFormulaUtils.checkImplication(transFormula1, transFormula2, mManagedScript);
		return result;
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;

		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		final boolean tryAuxVarElimination = true;

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
}
