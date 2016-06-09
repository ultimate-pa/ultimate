/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Annotations for Nelson-Oppen equality translating lemmas.
 * 
 * These annotations have no data, so we can share them.
 * 
 * @author Jochen Hoenicke
 *
 */
public final class EQAnnotation implements IAnnotation {
	/**
	 * The singleton EQAnnotation instance.
	 */
	public static final EQAnnotation EQ = new EQAnnotation();

	private final Annotation[] mAnnots = new Annotation[] {
		new Annotation(":EQ", null)
	};
	
	private EQAnnotation() {
	}

	@Override
	public Term toTerm(Clause cls, Theory theory) {
		final Term base = cls.toTerm(theory);
		return theory.term("@lemma", theory.annotatedTerm(mAnnots, base));
	}
}
