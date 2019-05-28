/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class ExplicitValueDomain implements IDomain<IPredicate> {

	private final PredicateUtils mPredicateUtils;
	private final IUltimateServiceProvider mServices;
	private int mDisjunctThreshold;

	public ExplicitValueDomain(final IUltimateServiceProvider services, final PredicateUtils predicateUtils) {
		mPredicateUtils = predicateUtils;
		mServices = services;
	}

	@Override
	public IPredicate join(final IPredicate first, final IPredicate second) {
		// TODO decide whether or not to use simplification or use a setting
		final boolean simplifyDDA = true;
		return mPredicateUtils.getFactory().or(simplifyDDA, first, second);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO implement non-trivial version
		return mPredicateUtils.top();
	}

	@Override
	public boolean isBottom(final IPredicate pred) {
		return mPredicateUtils.isFalse(pred);
	}

	@Override
	public boolean isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mPredicateUtils.implies(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		// TODO consider using QuantifierPusher to push quantifiers as inwards as possible

		// you can ensure that there are no let terms by using the unletter, but there should not be any let terms
		// final Term unletedTerm = new FormulaUnLet().transform(pred.getFormula());

		final Term dnf = SmtUtils.toDnf(mServices, mPredicateUtils.getScript(), pred.getFormula(),
				SmtUtils.XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final Term[] disjuncts = SmtUtils.getDisjuncts(dnf);
		final Set<Term> rewrittenDisjuncts = new HashSet<>();
		final DnfToExplicitValue rewriter = new DnfToExplicitValue(mServices, mPredicateUtils);
		for (int i = 0; i < disjuncts.length; ++i) {
			// rewrite each disjunct with DnfToExplicitvalue
			rewrittenDisjuncts.add(rewriter.transform((disjuncts[i])));
		}

		// decide how many of the unique disjuncts are allowed to survive, join if necessary
		if (rewrittenDisjuncts.size() > mDisjunctThreshold) {
			// TODO: Join
		}
		return mPredicateUtils.or(rewrittenDisjuncts);
	}

}
