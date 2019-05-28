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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DnfToExplicitValue extends TermTransformer {

	private final int mMaxValsPerVar = 4;

	public DnfToExplicitValue(final IUltimateServiceProvider services, final PredicateUtils predicateUtils) {

	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof TermVariable) {
			setResult(term);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm applTerm = (ApplicationTerm) term;
			if ("or".equals(applTerm.getFunction().getName())) {
				// TODO add walkers for each and term, add explicit value for each term
			}
		} else {
			// TODO handle let expressions?
		}
	}

	/** Only used to make {@link #getConverted()} visible to walkers. */
	Term[] getConvertedArray(final Term[] oldArgs) {
		return getConverted(oldArgs);
	}

	protected class WalkOuterOr implements Walker {
		/** the application term to convert. */
		private final ApplicationTerm mAppTerm;

		public WalkOuterOr(final ApplicationTerm term) {
			mAppTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			// TODO implement -- right now this is only a copy of TermTransformer's walker
			final DnfToExplicitValue transformer = (DnfToExplicitValue) engine;
			final Term[] oldArgs = mAppTerm.getParameters();
			final Term[] newArgs = transformer.getConvertedArray(oldArgs);
			transformer.convertApplicationTerm(mAppTerm, newArgs);
		}

		@Override
		public String toString() {
			return mAppTerm.getFunction().getApplicationString();
		}
	}

	protected class WalkInnerAnd implements Walker {
		/** the application term to convert. */
		private final ApplicationTerm mAppTerm;

		public WalkInnerAnd(final ApplicationTerm term) {
			mAppTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			// TODO implement -- right now this is only a copy of TermTransformer's walker
			final DnfToExplicitValue transformer = (DnfToExplicitValue) engine;
			final Term[] oldArgs = mAppTerm.getParameters();
			final Term[] newArgs = transformer.getConvertedArray(oldArgs);
			transformer.convertApplicationTerm(mAppTerm, newArgs);
		}

		@Override
		public String toString() {
			return mAppTerm.getFunction().getApplicationString();
		}
	}
}
