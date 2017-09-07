/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

public class IndexAnalysisResult extends EqualityAnalysisResult {
	

	
	/**
	 * Doubletons that we do not check because they do not occur in the formula.
	 */
	private final Set<Doubleton<Term>> mIgnoredDoubletons;
	
	public IndexAnalysisResult(Set<Doubleton<Term>> equalDoubletons, 
			Set<Doubleton<Term>> distinctDoubletons,
			Set<Doubleton<Term>> unknownDoubletons,
			Set<Doubleton<Term>> ignoredDoubletons) {
		super(equalDoubletons, distinctDoubletons, unknownDoubletons);
		mIgnoredDoubletons = ignoredDoubletons;
	}
	
	public EqualityStatus isEqual(List<Term> index1, List<Term> index2) {
		assert index1.size() == index2.size();
		boolean oneEntryWasUnknown = false;
		for (int i=0; i<index1.size(); i++) {
			if (index1.get(i) == index2.get(i)) {
				continue;
			}
			if (isDistinctDoubleton(index1.get(i), index2.get(i))) {
				return EqualityStatus.NOT_EQUAL;
			}
			if (isUnknownDoubleton(index1.get(i), index2.get(i))) {
				oneEntryWasUnknown = true;
			} else if (isIgnoredDoubleton(index1.get(i), index2.get(i))) {
				oneEntryWasUnknown = true;
			} else {
				assert (isEqualDoubleton(index1.get(i), index2.get(i)));
			}
		}
		if (oneEntryWasUnknown) {
			return EqualityStatus.UNKNOWN;
		} else {
			return EqualityStatus.EQUAL;
		}
	}
	
	public boolean isEqualDoubleton(Term t1, Term t2) {
		return getEqualDoubletons().contains(new Doubleton<Term>(t1, t2));
	}
	
	public boolean isDistinctDoubleton(Term t1, Term t2) {
		return getDistinctDoubletons().contains(new Doubleton<Term>(t1, t2));
	}
	
	public boolean isUnknownDoubleton(Term t1, Term t2) {
		return getUnknownDoubletons().contains(new Doubleton<Term>(t1, t2));
	}
	
	public boolean isIgnoredDoubleton(Term t1, Term t2) {
		return mIgnoredDoubletons.contains(new Doubleton<Term>(t1, t2));
	}
}
