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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class ExplicitValueDomain implements IDomain {

	private final SymbolicTools mTools;
	private final IUltimateServiceProvider mServices;
	private final int mMaxDisjuncts = 2;

	public ExplicitValueDomain(final IUltimateServiceProvider services, final SymbolicTools tools) {
		mTools = tools;
		mServices = services;
	}

	@Override
	public IPredicate join(final IPredicate first, final IPredicate second) {
		return joinAccordingToMax(mTools.or(first, second));
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// join will reach a fixpoint on every sequence since
		// - we limited the number of disjuncts to mMaxDisjuncts and
		// - the number of variables in every (non-recursive) program is finite
		return join(old, widenWith);
	}

	@Override
	public boolean isBottom(final IPredicate pred) {
		// TODO do not use SMT solver
		return mTools.isFalse(pred);
	}

	@Override
	public boolean isSubsetEq(final IPredicate subset, final IPredicate superset) {
		// TODO do not use SMT solver
		return mTools.implies(subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		// TODO consider using QuantifierPusher to push quantifiers as inwards as possible

		// you can ensure that there are no let terms by using the unletter, but there should not be any let terms
		// final Term unletedTerm = new FormulaUnLet().transform(pred.getFormula());

		final Term dnf = SmtUtils.toDnf(mServices, mTools.getManagedScript(), pred.getFormula(),
				SmtUtils.XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final DnfToExplicitValue rewriter = new DnfToExplicitValue(mServices, mTools);
		final Term[] rewrittenDisjuncts = Arrays.stream(SmtUtils.getDisjuncts(dnf))
				.map(rewriter::transform)
				.toArray(Term[]::new);
		// TODO use a more strict normal form, where assignments have a variable on the left and a number on the right?
		return mTools.or(joinAccordingToMax(rewrittenDisjuncts));
	}

	private IPredicate joinAccordingToMax(final IPredicate dnfPredicate) {
		return mTools.or(joinAccordingToMax(SmtUtils.getDisjuncts(dnfPredicate.getFormula())));
	}

	private Term[] joinAccordingToMax(final Term[] disjuncts) {
		if (disjuncts.length <= mMaxDisjuncts) {
			return disjuncts;
		}
		// TODO at the moment we group disjunctions to be joined based on their order ...
		// ... Using a heuristic could lead to less precision loss.
		final Term[] joined = new Term[mMaxDisjuncts];
		int sourceIdx = 0;
		for (int targetIdx = 0; targetIdx < joined.length; ++targetIdx) {
			final int joinGroupSize = (int) Math.ceil((disjuncts.length - sourceIdx) /
					(double) (joined.length - targetIdx));
			joined[targetIdx] = Arrays.stream(disjuncts, sourceIdx, sourceIdx + joinGroupSize)
					.reduce(disjuncts[sourceIdx], this::joinConjunctions);
			sourceIdx += joinGroupSize;
		}
		return joined;
	}

	private Term joinConjunctions(final Term leftConjn, final Term rightConjn) {
		return mapToConjunction(joinMapsOfVarsToValues(mapVarsToValues(leftConjn), mapVarsToValues(rightConjn)));
	}

	private Term mapToConjunction(final Map<Term, Term> equalities) {
		return mTools.and(equalities.entrySet().stream().map(this::entryToEq).toArray(Term[]::new)).getFormula();
	}

	private Term entryToEq(final Map.Entry<Term, Term> entry) {
		return mTools.getScript().term("=", entry.getKey(), entry.getValue());
	}

	private static Map<Term, Term> joinMapsOfVarsToValues(
			final Map<Term, Term> leftMap, final Map<Term, Term> rightMap) {
		leftMap.entrySet().retainAll(rightMap.entrySet());
		return leftMap;
	}

	private static Map<Term, Term> mapVarsToValues(final Term conjunction) {
		final Map<Term, Term> map = new LinkedHashMap<>();
		for (final Term conjunct : SmtUtils.getConjuncts(conjunction)) {
			addPairsToMap(map, conjunct);
		}
		return map;
	}

	private static void addPairsToMap(final Map<Term, Term> map, final Term eqTerm) {
		final Term[] subterms = subtermsOfEq(eqTerm);
		final Optional<Term> value = extractValue(subterms);
		if (!value.isPresent()) {
			return;
		}
		extractVariables(subterms).forEach(var -> map.put(var, value.get()));
	}

	private static Term[] subtermsOfEq(final Term eqTerm) {
		if (eqTerm instanceof ApplicationTerm) {
			final ApplicationTerm applTerm = (ApplicationTerm) eqTerm;
			if ("=".equals(applTerm.getFunction().getName())) {
				return applTerm.getParameters();
			}
		}
		// not an equality
		return new Term[0];
	}

	private static Collection<Term> extractVariables(final Term[] terms) {
		final Collection<Term> vars = new ArrayList<>(terms.length);
		for (final Term term : terms) {
			if (term instanceof TermVariable) {
				vars.add(term);
			}
		}
		return vars;
	}

	private static Optional<Term> extractValue(final Term[] terms) {
		Term constant = null;
		for (final Term term : terms) {
			if (term instanceof ConstantTerm) {
				if (constant != null) {
					throw new AssertionError("More than one constant. Expected simplification to remove them.");
				}
				constant = term;
			}
		}
		return Optional.ofNullable(constant);
	}
}





























