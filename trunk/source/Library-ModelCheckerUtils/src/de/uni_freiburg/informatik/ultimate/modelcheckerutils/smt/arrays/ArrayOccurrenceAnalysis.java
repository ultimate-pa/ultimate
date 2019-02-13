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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Analyse for a given term and a given (wanted) array in which kinds of
 * subterms the array occurs.
 *
 * @author Matthias Heizmann
 */
public class ArrayOccurrenceAnalysis {
	private final Term mAnalyzedTerm;
	private final Term mWantedArray;

	private final List<ArraySelectOverStore> mArraySelectOverStores = new ArrayList<>();
	private final List<NestedArrayStore> mNestedArrayStores = new ArrayList<>();
	private final List<ArraySelect> mArraySelects = new ArrayList<>();
	private final List<Term> mArrayEqualities = new ArrayList<>();
	private final List<Term> mArrayDisequalities = new ArrayList<>();
	private final List<Term> mOtherFunctionApplications = new ArrayList<>();

	public ArrayOccurrenceAnalysis(final Term analyzedTerm, final Term wantedArray) {
		super();
		mAnalyzedTerm = analyzedTerm;
		mWantedArray = wantedArray;
	}
	/**
	 * @return from the analyzed term all select-over-store subterms whose array is the wantedArray
	 */
	public List<ArraySelectOverStore> getArraySelectOverStores() {
		return mArraySelectOverStores;
	}
	/**
	 * @return from the analyzed term all (possibly nested) store subterms whose array is the wantedArray
	 * such that the store subterms are not part of a select-over-store subterm.
	 */
	public List<NestedArrayStore> getNestedArrayStores() {
		return mNestedArrayStores;
	}
	/**
	 * @return from the analyzed term all (possibly nested) store subterms whose array is the wantedArray
	 */
	public List<ArraySelect> getArraySelects() {
		return mArraySelects;
	}

	/**
	 * @return from the analyzed term all binary equality subterms such that the
	 *         wanted array occurs on one side of the equality. The resulting
	 *         equality is represented by the term that occurs on the other side of
	 *         the binary equality
	 */
	public List<Term> getArrayEqualities() {
		return mArrayEqualities;
	}

	/**
	 * @return from the analyzed term all binary disequality subterms such that the
	 *         wanted array occurs on one side of the disequality. The resulting
	 *         disequality is represented by the term that occurs on the other side of
	 *         the binary disequality
	 */

	public List<Term> getArrayDisequalities() {
		return mArrayDisequalities;
	}

	/**
	 * @return from the analyzed term all function application subterms such that
	 *         the wanted array is an argument. However, as an exception all cases
	 *         that are already handled by this class are omitted (i.e., if the
	 *         wanted array is first argument of store/select or occurs on one side
	 *         of an equality/disequality)
	 */
	public List<Term> getOtherFunctionApplications() {
		return mOtherFunctionApplications;
	}


}
