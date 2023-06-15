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

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermWrapper;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents an additional conjunct (resp. disjunct) of a {@link Case} in a
 * {@link MultiCaseSolvedBinaryRelation}. The term that is represented by this
 * class must not contain the subject for which the binary relation is solved.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Leonard Fichtner (leonard.fichtner@web.de)
 */
public class SupportingTerm implements ITermWrapper {

	private final Term mTerm;
	private final IntricateOperation mIntricateOperation;
	private final Set<TermVariable> mNewAuxiliaryVariables;

	public SupportingTerm(final Term term, final IntricateOperation intricateOperation,
			final Set<TermVariable> newAuxiliaryVariables) {
		super();
		Objects.requireNonNull(term);
		mTerm = term;
		mIntricateOperation = intricateOperation;
		mNewAuxiliaryVariables = newAuxiliaryVariables;
	}

	/**
	 * @return The {@link IntricateOperation} that caused the introduction of
	 *         this {@link SupportingTerm}.
	 */
	public IntricateOperation getIntricateOperation() {
		return mIntricateOperation;
	}

	/**
	 * @return Auxiliary variables that occur in this term and were introduced
	 *         while solving a binary relation for a subject.
	 */
	public Set<TermVariable> getNewAuxiliaryVariables() {
		return mNewAuxiliaryVariables;
	}

	@Override
	public Term getTerm() {
		return mTerm;
	}

	@Override
	public String toString() {
		String info = "[";
		info = info + mTerm.toString();
		info = info + ", " + mIntricateOperation.toString();
		info = info + ", AuxVars: ";
		for (final TermVariable termVar : mNewAuxiliaryVariables) {
			info = info + termVar.toString() + ", ";
		}
		info = info + "]";
		return info;
	}

}
