/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Term domain operations that are needed for {@link PredicateTransformer}
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TermDomainOperationProvider implements IDomainSpecificOperationProvider<Term, IPredicate, TransFormula> {
	protected final ManagedScript mMgdScript;
	protected final IUltimateServiceProvider mServices;

	public TermDomainOperationProvider(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mServices = services;
		mMgdScript = mgdScript;
	}

	@Override
	public Term getConstraint(final IPredicate p) {
		return p.getFormula();
	}

	@Override
	public boolean isConstraintUnsatisfiable(final Term constraint) {
		return SmtUtils.isFalseLiteral(constraint);
	}

	@Override
	public boolean isConstraintValid(final Term constraint) {
		return SmtUtils.isTrueLiteral(constraint);
	}

	@Override
	public Term getConstraintFromTransitionRelation(final TransFormula tf) {
		return tf.getFormula();
	}

	@Override
	public Term renameVariables(final Map<Term, Term> substitutionForTransFormula, final Term constraint) {
		final Term renamedTransFormula =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionForTransFormula).transform(constraint);
		return renamedTransFormula;
	}

	@Override
	public Term constructConjunction(final List<Term> conjuncts) {
		return SmtUtils.and(mMgdScript.getScript(), conjuncts);
	}

	@Override
	public Term constructDisjunction(final List<Term> disjuncts) {
		return SmtUtils.or(mMgdScript.getScript(), disjuncts);
	}

	@Override
	public Term constructNegation(final Term operand) {
		return SmtUtils.not(mMgdScript.getScript(), operand);
	}

	@Override
	public Term projectExistentially(final Set<TermVariable> varsToProjectAway, final Term constraint) {
		return constructQuantifiedFormula(Script.EXISTS, varsToProjectAway, constraint);
	}

	@Override
	public Term projectUniversally(final Set<TermVariable> varsToProjectAway, final Term constraint) {
		return constructQuantifiedFormula(Script.FORALL, varsToProjectAway, constraint);
	}

	private Term constructQuantifiedFormula(final int quantifier, final Set<TermVariable> varsToQuantify,
			final Term term) {
		final Term quantified = SmtUtils.quantifier(mMgdScript.getScript(), quantifier, varsToQuantify, term);
		final Term pushed =
				new QuantifierPusher(mMgdScript, mServices, false, PqeTechniques.ONLY_DER).transform(quantified);
		return pushed;
	}

}
