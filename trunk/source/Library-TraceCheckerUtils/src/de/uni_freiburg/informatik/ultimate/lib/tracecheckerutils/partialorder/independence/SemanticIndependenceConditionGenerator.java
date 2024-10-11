/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUnification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.abduction.Abducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Generates conditions under which given transitions commute semantically (in the sense of conditional
 * {@link SemanticIndependenceRelation} instances). Uses abduction (see {@link Abducer}) to generate such conditions.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class SemanticIndependenceConditionGenerator implements IIndependenceConditionGenerator {
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;

	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final BasicPredicateFactory mFactory;
	private final boolean mSymmetric;
	private final boolean mStrongQuantifierElimination;

	/**
	 * Create a new instance.
	 *
	 * @param services
	 *            Ultimate services instance
	 * @param mgdScript
	 *            A script that is used for name management, satisfiability checking and quantifier elimination.
	 * @param factory
	 *            A factory that is used to create {@link IPredicate} instances representing the conditions
	 * @param symmetric
	 *            Whether to generate conditions that are strong enough for symmetric independence (otherwise conditions
	 *            might only be strong enough for non-symmetric independence).
	 */
	public SemanticIndependenceConditionGenerator(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory factory, final boolean symmetric) {
		this(services, mgdScript, factory, symmetric, false);
	}

	/**
	 * Create a new instance.
	 *
	 * @param services
	 *            Ultimate services instance
	 * @param mgdScript
	 *            A script that is used for name management, satisfiability checking and quantifier elimination.
	 * @param factory
	 *            A factory that is used to create {@link IPredicate} instances representing the conditions
	 * @param symmetric
	 *            Whether to generate conditions that are strong enough for symmetric independence (otherwise conditions
	 *            might only be strong enough for non-symmetric independence).
	 * @param strongQuantifierElimination
	 *            If set to true, a more expensive and more powerful quantifier elimination algorithm is used. This
	 *            helps in cases where otherwise no independence condition can be found, because solvers return UNKNOWN
	 *            for complex quantified formulae.
	 */
	public SemanticIndependenceConditionGenerator(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final BasicPredicateFactory factory, final boolean symmetric,
			final boolean strongQuantifierElimination) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(SemanticIndependenceConditionGenerator.class);
		mMgdScript = mgdScript;
		mFactory = factory;
		mSymmetric = symmetric;
		mStrongQuantifierElimination = strongQuantifierElimination;
	}

	/**
	 * Generate a condition under which the given transitions are independent.
	 *
	 * @param context
	 *            A context that is already known, but not sufficient for commutativity
	 * @param a
	 *            The first transition
	 * @param b
	 *            The second transition
	 *
	 * @return a sufficient condition for independence
	 */
	@Override
	public IPredicate generateCondition(final IPredicate context, final UnmodifiableTransFormula a,
			final UnmodifiableTransFormula b) {
		// Generate both compositions, possibly adding a guard where applicable
		final UnmodifiableTransFormula ab = withGuard(context, compose(a, b));
		final UnmodifiableTransFormula ba = withGuard(mSymmetric ? context : null, compose(b, a));

		// Make sure both compositions don't contain free auxiliary variables, and refer to the same in/out variables
		final TransFormulaUnification unification = new TransFormulaUnification(mMgdScript, ab, ba);
		final Term lhsFormula = quantify(unification.getAuxVars(), unification.getUnifiedFormula(ab));
		final Term rhsFormula = quantify(unification.getAuxVars(), unification.getUnifiedFormula(ba));

		// Generate a condition that induces commutativity, and does not refer to (pure) output variables
		final Set<TermVariable> forbidden = new HashSet<>(unification.getOutVars().values());
		forbidden.removeAll(unification.getInVars().values());
		final Term condition;
		if (mSymmetric) {
			condition = new Abducer(mServices, mMgdScript, forbidden, mStrongQuantifierElimination)
					.abduceEquivalence(lhsFormula, rhsFormula);
		} else {
			condition = new Abducer(mServices, mMgdScript, forbidden, mStrongQuantifierElimination).abduce(lhsFormula,
					rhsFormula);
		}
		if (condition == null) {
			return null;
		}

		// Substitute generated term variables for input variable's default term variables
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : unification.getInVars().entrySet()) {
			assert !substitution.containsKey(entry.getValue());
			substitution.put(entry.getValue(), entry.getKey().getTermVariable());
		}
		final Term restoredCondition = Substitution.apply(mMgdScript, substitution, condition);

		// Create a predicate
		return mFactory.newPredicate(restoredCondition);
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used locally
		final boolean simplify = false;

		// try to eliminate auxiliary variables to avoid quantifier alternation
		final boolean tryAuxVarElimination = true;

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, simplify, tryAuxVarElimination,
				false, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE, Arrays.asList(first, second));
	}

	private final UnmodifiableTransFormula withGuard(final IPredicate guard, final UnmodifiableTransFormula tf) {
		if (guard == null) {
			return tf;
		}
		return compose(TransFormulaBuilder.constructTransFormulaFromPredicate(guard, mMgdScript), tf);
	}

	private final Term quantify(final Set<TermVariable> vars, final Term formula) {
		final Term quantified = SmtUtils.quantifier(mMgdScript.getScript(), QuantifiedFormula.EXISTS, vars, formula);
		if (mStrongQuantifierElimination) {
			return PartialQuantifierElimination.eliminate(mServices, mMgdScript, quantified, SIMPLIFICATION_TECHNIQUE);
		}
		return PartialQuantifierElimination.eliminateLight(mServices, mMgdScript, quantified);
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}
}
