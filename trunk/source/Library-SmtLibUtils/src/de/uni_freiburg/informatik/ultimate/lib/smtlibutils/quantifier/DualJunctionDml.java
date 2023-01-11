/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Katharina Wagner
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Div-mod liberation (DML) for conjunctions (resp. disjunctions).
 * <br>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Katharina Wagner
 */
public class DualJunctionDml extends DualJunctionQuantifierElimination {


	public DualJunctionDml(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "div mod liberation";
	}

	@Override
	public String getAcronym() {
		return "DML";
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {

		// Iterate over all variable that should be eliminated
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			// Iterate over all conjuncts
			final Term[] conjuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
			for (final Term conjunct : conjuncts) {
				// find subterms
				//SubTermFinder.find(term, predicate, onlyOutermost)

				final Term term = null;
				// get free variables of term
				term.getFreeVars();

				// convert to polynomial
				final IPolynomialTerm poly = PolynomialTermTransformer.convert(mScript, term);
			}
		}

		// construct fresh variable
		// mMgdScript.constructFreshTermVariable(name, sort)

		// apply substitution
		//Substitution.apply(mMgdScript, substitutionMapping, term);

		// construct conjunction
		// SmtUtils.and(script, terms)

		// construct sum
		// SmtUtils.sum(script, sort, summands)

		// remove ite terms
		// new IteRemover(mMgdScript).transform(term)

		return null;
	}


	private boolean isModTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			if (((ApplicationTerm) term).getFunction().getApplicationString().equals("mod")) {
				return true;
			}
		}
		return false;
	}


}
