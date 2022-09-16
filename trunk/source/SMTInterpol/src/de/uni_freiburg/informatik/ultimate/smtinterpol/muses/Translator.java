/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;

/**
 * This class is responsible for translating between bit set representation and term representation of constraints.
 *
 * @author LeonardFichtner
 *
 */
public class Translator {

	HashMap<String, Integer> mNameOfConstraint2Index;
	ArrayList<NamedAtom> mIndex2AtomOfConstraint;
	int mPushPopLevel;

	public Translator() {
		mNameOfConstraint2Index = new HashMap<>();
		mIndex2AtomOfConstraint = new ArrayList<>();
		mPushPopLevel = 0;
	}

	/**
	 * The NamedAtom must be named by the AnnotatedTerm representing the constraint. Also the Polarity (preffered
	 * Status) must be set to TRUE for the Unexplored Map to behave correctly. If a term with the same name has already
	 * be declared, this method throws an SMTLIBException.
	 */
	public void declareConstraint(final NamedAtom atom) throws SMTLIBException {
		final String name = getName(atom);
		if (mNameOfConstraint2Index.containsKey(name)) {
			throw new SMTLIBException("This name already exists.");
		}
		final int numberOfConstraints = mIndex2AtomOfConstraint.size();
		mNameOfConstraint2Index.put(name, numberOfConstraints);
		mIndex2AtomOfConstraint.add(atom);
	}

	public Term translate2Constraint(final int index) {
		return getTerm(mIndex2AtomOfConstraint.get(index));
	}

	public NamedAtom translate2Atom(final int index) {
		return mIndex2AtomOfConstraint.get(index);
	}

	/**
	 * Returns null if there is no translation for this term or it has no name.
	 */
	public Integer translate2Index(final Term term) {
		return mNameOfConstraint2Index.get(getName(term));
	}

	public int translate2Index(final NamedAtom atom) {
		return mNameOfConstraint2Index.get(getName(atom));
	}

	/**
	 * Translates the arrays of Terms to the corresponding BitSet.
	 */
	public BitSet translateToBitSet(final Term[] constraints) {
		final BitSet constraintsAsBits = new BitSet(getNumberOfConstraints());
		Integer translation;
		for (int i = 0; i < constraints.length; i++) {
			translation = translate2Index(constraints[i]);
			if (translate2Index(constraints[i]) == null) {
				continue;
			}
			constraintsAsBits.set(translation);
		}
		return constraintsAsBits;
	}

	/**
	 * Translates the given BitSet to the corresponding array of Terms. The array does only contain constraints that
	 * have been set in the BitSet (i.e. it does not contain placeholders for clear Bits at the corresponding index)
	 */
	public Term[] translateToTerms(final BitSet constraints) {
		final Term[] constraintsAsTerms = new Term[constraints.cardinality()];
		int i = 0;
		for (int j = constraints.nextSetBit(0); j >= 0; j = constraints.nextSetBit(j + 1)) {
			constraintsAsTerms[i] = translate2Constraint(j);
			i++;
		}
		return constraintsAsTerms;
	}

	public int getNumberOfConstraints() {
		return  mIndex2AtomOfConstraint.size();
	}

	public ArrayList<NamedAtom> getIndex2AtomOfConstraint() {
		return mIndex2AtomOfConstraint;
	}

	private Term getTerm(final NamedAtom atom) {
		return atom.getSMTFormula(null);
	}

	private String getName(final NamedAtom atom) {
		return getName(atom.getSMTFormula(null));
	}

	/**
	 * Returns null, if the name was not found.
	 */
	public static String getName(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName();
		} else if (term instanceof AnnotatedTerm) {
			return getName(((AnnotatedTerm) term).getAnnotations());
		} else {
			throw new SMTLIBException("Unknown type of term.");
		}
	}

	private static String getName(final Annotation... annotation) throws SMTLIBException {
		String name = null;
		for (int i = 0; i < annotation.length; i++) {
			if (annotation[i].getKey().equals(":named")) {
				name = (String) annotation[i].getValue();
			}
		}
		if (name == null) {
			throw new SMTLIBException("No name for the constraint has been found.");
		}
		return name;
	}
}
