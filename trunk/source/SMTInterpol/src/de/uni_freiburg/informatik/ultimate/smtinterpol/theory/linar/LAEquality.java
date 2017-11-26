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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class LAEquality extends DPLLAtom {
	public final static Annotation[] QUOTED_LA = new Annotation[] { new Annotation(":quotedLA", null) };
	private final LinVar mVar;
	private final Rational mBound;
	private final ArrayList<CCEquality> mDependentEqualities;

	public LAEquality(final int stackLevel, final LinVar var, final Rational bound) {
		super(HashUtils.hashJenkins(~var.hashCode(), bound), stackLevel);
		mVar = var;
		mBound = bound;
		mDependentEqualities = new ArrayList<>();
	}

	public Rational getBound() {
		return mBound;
	}

	public LinVar getVar() {
		return mVar;
	}

	@Override
	public String toStringNegated() {
		return "[" + hashCode() + "]" + mVar + " != " + mBound;
	}

	@Override
	public String toString() {
		return "[" + hashCode() + "]" + mVar + " == " + mBound;
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
		final MutableAffinTerm at = new MutableAffinTerm();
		at.add(Rational.ONE, mVar);
		at.add(mBound.negate());
		final boolean isInt = mVar.mIsInt && mBound.isIntegral();
		final Sort s = smtTheory.getSort(isInt ? "Int" : "Real");
		final Sort[] binfunc = { s, s };
		final FunctionSymbol comp = smtTheory.getFunction("=", binfunc);
		final Term res = smtTheory.term(comp, at.toSMTLib(smtTheory, isInt, quoted), Rational.ZERO.toTerm(s));
		return quoted ? smtTheory.annotatedTerm(QUOTED_LA, res) : res;
	}

	public void addDependentAtom(final CCEquality eq) {
		mDependentEqualities.add(eq);
	}

	public void removeDependentAtom(final CCEquality eq) {
		mDependentEqualities.remove(eq);
	}

	public Iterable<CCEquality> getDependentEqualities() {
		return mDependentEqualities;
	}

	@Override
	public boolean equals(final Object other) { // NOCHECKSTYLE
		if (other instanceof LAEquality) {
			final LAEquality o = (LAEquality) other;
			return o.mVar == mVar && o.mBound.equals(mBound);
		}
		return false;
	}
}
