/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;

public class ArrayStoreAnnotation implements IAnnotation {
	
	private final ApplicationTerm mStore;
	private final String mSource;
	
	public ArrayStoreAnnotation(ApplicationTerm store, String source) {
		mStore = store;
		mSource = source;
	}
	
	public ArrayStoreAnnotation(ApplicationTerm store, IAnnotation source) {
		mStore = store;
		if (source instanceof SourceAnnotation)
			mSource = ((SourceAnnotation) source).getAnnotation();
		else
			mSource = "";
	}
	
	public ApplicationTerm getStore() {
		return mStore;
	}
	
	public String getSource() {
		return mSource;
	}

	@Override
	public String toSExpr(Theory smtTheory) {
		return mStore + " :store"
				+ (mSource.isEmpty() ? "" : " " + new QuotedObject(mSource));
	}

	@Override
	public Term toTerm(Clause cls, Theory theory) {
		Term base = cls.toTerm(theory);
		return theory.term("@lemma", theory.annotatedTerm(new Annotation[] {
			new Annotation(":store", mStore),
			new Annotation(":input", mSource)
		}, base));
	}

}
