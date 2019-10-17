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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject;

import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ITermProviderOnDemand;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a binary relation that has been solved for a subject x. I.e. this
 * represents a formula of the form x ▷ φ, where x is a variable, φ is a term in
 * which x does not occur. Here, the binary relation symbol ▷ is an element of
 * the following list.
 * <p>
 * ▷ ∈ { =, !=, \<=, \<, \>=, \> }
 * </p>
 * Additionally, this class may provide a Boolean formula ψ and if such a
 * formula is provided the formula x ▷ φ holds only under the assumption that ψ
 * holds.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiCaseSolvedBinaryRelation implements ITermProviderOnDemand {

	public enum IntricateOperation {
		DIV_BY_NONCONSTANT, DIV_BY_INTEGER_CONSTANT, MUL_BY_INTEGER_CONSTANT,
	}

	public enum Xnf {
		CNF, DNF
	}

	private final Term mSubject;
	private final List<Case> mCases;
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
			final EnumSet<IntricateOperation> additionalIntricateOperations, final Xnf xnf) {
		super();
		mSubject = subject;
		mCases = cases;
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
		return Stream
				.concat(mAdditionalIntricateOperations.stream(), mCases.stream()
						.flatMap(x -> x.getSupportingTerms().stream()).map(x -> x.getIntricateOperation()))
				.collect(Collectors.toSet());
	}

	public Xnf getXnf() {
		return mXnf;
	}

	@Override
	public Term asTerm(final Script script) {
		final Collection<Term> params = mCases.stream().map(x -> x.asTerm(script)).collect(Collectors.toList());
		final Term result;
		switch (mXnf) {
		case CNF:
			result = SmtUtils.and(script, params);
			break;
		case DNF:
			result = SmtUtils.or(script, params);
			break;
		default:
			throw new AssertionError("unknown case " + mXnf);
		}
		return result;
	}

}
