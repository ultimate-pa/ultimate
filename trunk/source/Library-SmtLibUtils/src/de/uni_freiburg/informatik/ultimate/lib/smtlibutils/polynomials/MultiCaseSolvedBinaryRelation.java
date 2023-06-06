/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a binary relation that has been solved for a subject x. Unlike
 * {@link SolvedBinaryRelation} object of this class can also represent binary
 * relations for which a case distinction is necessary. E.g., if we solve y*x<t
 * for subject x the result is the following disjunction.
 *
 * <pre>
 * x < (div t y) ∧ (mod t y) = 0 ∧ y > 0
 * ∨ x > (div t y) ∧ (mod t y) = 0 ∧ y < 0
 * ∨ y = 0 ∧ t = 0
 * </pre>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiCaseSolvedBinaryRelation implements ITermProvider {

	public enum IntricateOperation {
		/**
		 * Indicates that we had to divide by a non-constant term in order to
		 * solve the relation. Necessary e.g,. if we want to solve y*x=t for x
		 * and y is a variable. This operation is intricate because we now have
		 * to distinguish the cases that y is zero and that y is non-zero. (If
		 * the relation symbol is an inequality we even have to take into
		 * account that the relation symbol is "swapped" if y is negative.)
		 */
		DIV_BY_NONCONSTANT,
		/**
		 * Indicates that we had to divide by an integer literal in order to
		 * solve the relation. Necessary e.g,. if we want to solve k*x=t for x
		 * and k is a (non-zero) integer literal. This operation is intricate
		 * because if we divide by k, we loose the information that t is
		 * divisible by k.
		 */
		DIV_BY_INTEGER_CONSTANT,
		/**
		 * Indicates that we had to multiply by an integer literal in order to
		 * solve the relation. Necessary e.g,. if we want to solve (div x k)=t
		 * for x and k is a (non-zero) integer literal. This operation is
		 * intricate because if we multiply by k, we loose the information that
		 * e.g., t can be zero if x is k-1.
		 */
		MUL_BY_INTEGER_CONSTANT,
	}

	public enum Xnf {
		CNF, DNF;

		public static Xnf fromQuantifier(final int quantifier) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				return Xnf.DNF;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				return Xnf.CNF;
			} else {
				throw new AssertionError();
			}
		}
	}

	private final Term mSubject;
	private final List<Case> mCases;
	private final Set<TermVariable> mAdditionalAuxiliaryVariables;
	private final EnumSet<IntricateOperation> mAdditionalIntricateOperations;
	private final Xnf mXnf;

	/**
	 *
	 * @param additionalIntricateOperations
	 *            {@link IntricateOperation}s that were made and do not already
	 *            occur in one of the {@link SupportingTerm}s of the
	 *            {@link Case}s.
	 * @param xnf
	 *            If CNF each case is a disjunction and this class represents a
	 *            conjunction of cases. If DNF each case is a conjunction and
	 *            this class represents a disjunction of cases.
	 */
	public MultiCaseSolvedBinaryRelation(final Term subject, final List<Case> cases,
			final Set<TermVariable> additionalAuxiliaryVariables,
			final EnumSet<IntricateOperation> additionalIntricateOperations, final Xnf xnf) {
		super();
		mSubject = subject;
		mCases = cases;
		mAdditionalAuxiliaryVariables = additionalAuxiliaryVariables;
		mAdditionalIntricateOperations = additionalIntricateOperations;
		mXnf = xnf;
	}

	public Term getSubject() {
		return mSubject;
	}

	public List<Case> getCases() {
		return mCases;
	}

	public Set<IntricateOperation> getIntricateOperations() {
		return Stream.concat(mAdditionalIntricateOperations.stream(),
				mCases.stream().flatMap(Case::streamOfIntricateOperations)).collect(Collectors.toSet());
	}

	public Set<TermVariable> getAuxiliaryVariables() {
		return Stream.concat(mAdditionalAuxiliaryVariables.stream(),
				mCases.stream().flatMap(x -> x.getAuxiliaryVariables().stream())).collect(Collectors.toSet());
	}

	public Xnf getXnf() {
		return mXnf;
	}

	@Override
	public Term toTerm(final Script script) {
		final Collection<Term> params = mCases.stream().map(x -> x.toTerm(script)).collect(Collectors.toList());
		final Term body;
		final int quantifier;
		switch (mXnf) {
		case CNF:
			body = SmtUtils.and(script, params);
			quantifier = QuantifiedFormula.FORALL;
			break;
		case DNF:
			body = SmtUtils.or(script, params);
			quantifier = QuantifiedFormula.EXISTS;
			break;
		default:
			throw new AssertionError("unknown case " + mXnf);
		}
		final Set<TermVariable> vars = getAuxiliaryVariables();
		final Term result = SmtUtils.quantifier(script, quantifier, vars, body);
		return result;
	}


	public MultiCaseSolutionBuilder constructCopy() {
		final MultiCaseSolutionBuilder result = new MultiCaseSolutionBuilder(getSubject(), getXnf());
		result.splitCases(getCases());
		for (final TermVariable add : mAdditionalAuxiliaryVariables) {
			result.reportAdditionalAuxiliaryVariable(add);
		}
		for (final IntricateOperation add : mAdditionalIntricateOperations) {
			result.reportAdditionalIntricateOperation(add);
		}
		return result;
	}

	public boolean isSubjectOnlyOnRhs() {
		for (final Case c : getCases()) {
			final boolean isSubjectOnlyOnRhs = isSubjectOnlyOnRhs(mSubject, c);
			if (!isSubjectOnlyOnRhs) {
				return false;
			}
		}
		return true;
	}

	private boolean isSubjectOnlyOnRhs(final Term subject, final Case c) {
		if (c.getSolvedBinaryRelation() != null) {
			if (!c.getSolvedBinaryRelation().getLeftHandSide().equals(subject)) {
				throw new AssertionError("illegal subject");
			}
		}
		for (final SupportingTerm st : c.getSupportingTerms()) {
			final boolean containsSubject = SmtUtils.isSubterm(st.getTerm(), subject);
			if (containsSubject) {
				return false;
			}
		}
		return true;
	}

}
