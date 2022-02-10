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

import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A container made to keep minimal unsatisfiable subsets and their corresponding proof of unsatisfiability. The MUS is
 * represented as a BitSet, where the Bit at index i signals whether constraint number i is contained in the MUS. To
 * translate it into the corresponding constraints, {@link CritAdministratorSolver} must be used.
 *
 * @author LeonardFichtner
 *
 */
public class MusContainer {

	BitSet mMus;
	Term mProof;


	public MusContainer(final BitSet mus, final Term proof) {
		mMus = mus;
		mProof = proof;
	}

	public BitSet getMus() {
		return mMus;
	}

	public Term getProof() {
		return mProof;
	}

	@Override
	public String toString() {
		return mMus.toString();
	}
}
