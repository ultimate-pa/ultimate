/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Provide information for the questions which Terms are equivalent at a
 * given location.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IEqualityAnalysisResultProvider<LOC> {

	public EqualityAnalysisResult getAnalysisResult(LOC location, Set<Doubleton<Term>> doubletons);
	
	
	public static class EqualityAnalysisResult {
		private final Set<Doubleton<Term>> mEqualDoubletons;
		private final Set<Doubleton<Term>> mDistinctDoubletons;
		private final Set<Doubleton<Term>> mUnknownDoubletons;
		
		public EqualityAnalysisResult(Set<Doubleton<Term>> equalDoubletons, 
				Set<Doubleton<Term>> distinctDoubletons,
				Set<Doubleton<Term>> unknownDoubletons) {
			super();
			this.mEqualDoubletons = equalDoubletons;
			this.mDistinctDoubletons = distinctDoubletons;
			this.mUnknownDoubletons = unknownDoubletons;
		}

		/**
		 * @return all Doubletons (t1,t2) such that our analysis was able
		 * to prove that t1==t2 holds.
		 */
		public Set<Doubleton<Term>> getEqualDoubletons() {
			return mEqualDoubletons;
		}

		/**
		 * @return all Doubletons (t1,t2) such that our analysis was able
		 * to prove that t1!=t2 holds.
		 */
		public Set<Doubleton<Term>> getDistinctDoubletons() {
			return mDistinctDoubletons;
		}

		/**
		 * @return all Doubletons (t1,t2) such that our analysis was neither able
		 * to prove that t1==t2 holds nor that t1!=t2 holds.
		 */
		public Set<Doubleton<Term>> getUnknownDoubletons() {
			return mUnknownDoubletons;
		}
		
		
	}
	
}
