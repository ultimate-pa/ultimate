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
import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a case of a {@link MultiCaseSolvedBinaryRelation}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class Case implements ITermProvider {

	protected final SolvedBinaryRelation mSolvedBinaryRelation;
	protected final Set<SupportingTerm> mSupportingTerms;
	protected final Xnf mXnf;

	/**
	 *
	 * @param solvedBinaryRelation
	 *            The {@link SolvedBinaryRelation} of this case. Can be null it
	 *            this {@link Case} of a {@link MultiCaseSolvedBinaryRelation}
	 *            consists only of {@link SupportingTerm}s.
	 * @param xnf
	 *            Defines if the {@link MultiCaseSolvedBinaryRelation} is given
	 *            in CNF or DNF. If the {@link MultiCaseSolvedBinaryRelation} is
	 *            given in CNF, this {@link Case} represents a disjunction,
	 *            otherwise this {@link Case} represents a conjunction.
	 */
	public Case(final SolvedBinaryRelation solvedBinaryRelation, final Set<SupportingTerm> supportingTerms,
			final Xnf xnf) {
		super();
		mSolvedBinaryRelation = solvedBinaryRelation;
		mSupportingTerms = supportingTerms;
		mXnf = xnf;
	}

	public SolvedBinaryRelation getSolvedBinaryRelation() {
		return mSolvedBinaryRelation;
	}

	public Set<SupportingTerm> getSupportingTerms() {
		return Collections.unmodifiableSet(mSupportingTerms);
	}

	/**
	 * @return the auxiliary variables of all {@link SupportingTerm}s.
	 */
	public Set<TermVariable> getAuxiliaryVariables() {
		return mSupportingTerms.stream().flatMap(x -> x.getNewAuxiliaryVariables().stream())
				.collect(Collectors.toSet());
	}

	public Stream<IntricateOperation> streamOfIntricateOperations() {
		if (mSolvedBinaryRelation != null && mSolvedBinaryRelation.getIntricateOperation() != null) {
			return Stream.concat(mSolvedBinaryRelation.getIntricateOperation().stream(),
					getSupportingTerms().stream().map(x -> x.getIntricateOperation()));
		} else {
			return getSupportingTerms().stream().map(x -> x.getIntricateOperation());
		}
	}

	@Override
	public Term toTerm(final Script script) {
		final Collection<Term> params = mSupportingTerms.stream().map(x -> x.getTerm()).collect(Collectors.toList());
		if (mSolvedBinaryRelation != null) {
			params.add(mSolvedBinaryRelation.toTerm(script));
		}
		final Term result;
		switch (mXnf) {
		case CNF:
			result = SmtUtils.or(script, params);
			break;
		case DNF:
			result = SmtUtils.and(script, params);
			break;
		default:
			throw new AssertionError("unknown case " + mXnf);
		}
		return result;
	}

	@Override
	public String toString() {
		String junctor;
		String result;
		switch (mXnf) {
		case CNF:
			junctor = " \\/ ";
			break;
		case DNF:
			junctor = " /\\ ";
			break;
		default:
			throw new AssertionError("unknown case " + mXnf);
		}
		if (mSolvedBinaryRelation == null) {
			result = "{";
		}else {
			result = "{" + mSolvedBinaryRelation.toString();
		}
		for (final SupportingTerm supp : mSupportingTerms) {
			if (result == "{") {
				result = result + supp.toString();
			}else {
				result = result + junctor + supp.toString();
			}
		}
		result = result + "}";
		return result;
	}
}
