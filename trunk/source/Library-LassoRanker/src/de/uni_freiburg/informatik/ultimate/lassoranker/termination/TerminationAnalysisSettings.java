/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;

/**
 * Various (local) settings for termination analysis
 *
 * A new TerminationAnalysisSettings object can be used for each template
 *
 * This class functions much like a struct and is implemented like one.
 *
 * @author Jan Leike
 */
public class TerminationAnalysisSettings implements Serializable, ITerminationAnalysisSettings {
	private static final long serialVersionUID = 9183092457990345360L;

	private final AnalysisType mAnalysis;
	private final int mNumStrictInvariants;
	private final int mNumNonStrictInvariants;
	private final boolean mNonDecreasingInvariants;
	private final boolean mSimplifyTerminationArgument;
	private final boolean mSimplifySupportingInvariants;
	private final boolean mOverapproximateStem;

	/**
	 * Copy constructor copies everything
	 */
	public TerminationAnalysisSettings(final ITerminationAnalysisSettings other) {
		mAnalysis = other.getAnalysis();
		mNumStrictInvariants = other.getNumStrictInvariants();
		mNumNonStrictInvariants = other.getNumNonStrictInvariants();
		mNonDecreasingInvariants = other.isNonDecreasingInvariants();
		mSimplifyTerminationArgument = other.isSimplifyTerminationArgument();
		mSimplifySupportingInvariants = other.isSimplifySupportingInvariants();
		mOverapproximateStem = other.isOverapproximateStem();
		assert checkSanity();
	}

	/**
	 * Verify that the settings are self-consistent and sane. Only makes assertion calls.
	 */
	private boolean checkSanity() {
		return mNumStrictInvariants >= 0 && mNumNonStrictInvariants >= 0;
	}

	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Termination analysis: ");
		sb.append(mAnalysis);
		sb.append("\nNumber of strict supporting invariants: ");
		sb.append(mNumStrictInvariants);
		sb.append("\nNumber of non-strict supporting invariants: ");
		sb.append(mNumNonStrictInvariants);
		sb.append("\nConsider only non-deceasing supporting invariants: ");
		sb.append(mNonDecreasingInvariants);
		sb.append("\nSimplify termination arguments: ");
		sb.append(mSimplifyTerminationArgument);
		sb.append("\nSimplify supporting invariants: ");
		sb.append(mSimplifySupportingInvariants);
		sb.append("Overapproximate stem: ");
		sb.append(mOverapproximateStem);
		return sb.toString();
	}

	@Override
	public AnalysisType getAnalysis() {
		return mAnalysis;
	}

	@Override
	public int getNumStrictInvariants() {
		return mNumStrictInvariants;
	}

	@Override
	public int getNumNonStrictInvariants() {
		return mNumNonStrictInvariants;
	}

	@Override
	public boolean isNonDecreasingInvariants() {
		return mNonDecreasingInvariants;
	}

	@Override
	public boolean isSimplifyTerminationArgument() {
		return mSimplifyTerminationArgument;
	}

	@Override
	public boolean isSimplifySupportingInvariants() {
		return mSimplifySupportingInvariants;
	}

	@Override
	public boolean isOverapproximateStem() {
		return mOverapproximateStem;
	}
}
