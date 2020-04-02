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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class SharedTermEvaluator {
	private final Clausifier mClausifier;

	public SharedTermEvaluator(final Clausifier clausifier) {
		mClausifier = clausifier;
	}

	public Rational evaluate(final Term term, final Theory t) {
		SMTAffineTerm affine = SMTAffineTerm.create(term);
		Rational value = affine.getConstant();
		for (Entry<Term, Rational> entry : affine.getSummands().entrySet()) {
			LinVar var = mClausifier.getLinVar(entry.getKey());
			value = value.addmul(mClausifier.getLASolver().realValue(var), entry.getValue());
		}
		return value;
	}
}
