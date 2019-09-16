/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

/**
 * Represents an Atom that is known to the EprTheory.
 * Note that, although this class inherits from DPLLAtom, only some EprAtoms are known to
 * the DPLLEngine, namely those that are of the form "(P c_1 ... c_n)" where P is an
 * uninterpreted predicate and the c_i are constants. In contrast, every EprAtom that contains
 * a TermVariable is only known to the EprTheory.
 *
 * @author Alexander Nutz
 *
 */
public abstract class EprAtom extends DPLLAtom {

	private final Term mTerm;
	private TermTuple mArgsAsTermTuple = null;

	private final SourceAnnotation mSourceAnnotation;

	public EprAtom(final Term term, final int hash, final int assertionstacklevel, final SourceAnnotation source) {
		super(hash, assertionstacklevel);
		this.mTerm = term;
		this.mSourceAnnotation = source;
	}

	public Term[] getArguments() {
		return ((ApplicationTerm) mTerm).getParameters();
	}

	public TermTuple getArgumentsAsTermTuple() {
		if (mArgsAsTermTuple == null)
			mArgsAsTermTuple = new TermTuple(this.getArguments());
		return mArgsAsTermTuple;
	}

	@Override
	public String toString() {
		final String res =  mTerm.toStringDirect();
		if (res.contains("AUX")) {
			final EprPredicateAtom predAtom = (EprPredicateAtom) this;
			return "(AUX " + predAtom.getEprPredicate().hashCode() + " " + Arrays.toString(((ApplicationTerm) mTerm).getParameters()) + ")";
		}
		return res;
	}

	public Term getTerm() {
		return mTerm;
	}

	public SourceAnnotation getSourceAnnotation() {
		return mSourceAnnotation;
	}
}
