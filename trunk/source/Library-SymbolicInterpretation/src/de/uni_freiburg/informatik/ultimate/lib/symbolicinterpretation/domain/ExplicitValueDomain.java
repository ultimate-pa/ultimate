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

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class ExplicitValueDomain implements IDomain {

	private final SymbolicTools mTools;
	private final IUltimateServiceProvider mServices;
	private int mDisjunctThreshold;

	public ExplicitValueDomain(final IUltimateServiceProvider services, final SymbolicTools tools) {
		mTools = tools;
		mServices = services;
	}

	@Override
	public IPredicate join(final IPredicate first, final IPredicate second) {
		// TODO decide whether or not to use simplification or use a setting
		final boolean simplifyDDA = true;
		return mTools.getFactory().or(simplifyDDA, first, second);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO implement non-trivial version
		return mTools.top();
	}

	@Override
	public boolean isBottom(final IPredicate pred) {
		return mTools.isFalse(pred);
	}

	@Override
	public boolean isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return mTools.implies(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		// TODO consider using QuantifierPusher to push quantifiers as inwards as possible

		// you can ensure that there are no let terms by using the unletter, but there should not be any let terms
		// final Term unletedTerm = new FormulaUnLet().transform(pred.getFormula());

		final Term dnf = SmtUtils.toDnf(mServices, mTools.getScript(), pred.getFormula(),
				SmtUtils.XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final DnfToExplicitValue rewriter = new DnfToExplicitValue(mServices, mTools);
		final Set<Term> rewrittenDisjuncts = Arrays.stream(SmtUtils.getDisjuncts(dnf))
				.map(rewriter::transform)
				.collect(Collectors.toSet());
		// decide how many of the unique disjuncts are allowed to survive, join if necessary
		if (rewrittenDisjuncts.size() > mDisjunctThreshold) {
			// TODO: Join
		}
		return mTools.or(rewrittenDisjuncts);
	}

}
