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
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;

/**
 * Various (local) settings for nontermination analysis
 *
 * A new NonTerminationAnalysisSettings object can be used for each nontermination analysis
 *
 * This class functions much like a struct and is implemented like one.
 *
 * @author Jan Leike
 */
public class NonTerminationAnalysisSettings implements Serializable, INonTerminationAnalysisSettings {
	private static final long serialVersionUID = 4249624228131593458L;

	private final AnalysisType mAnalysis;

	private final boolean mAllowBounded;

	private final int mNumberOfGevs;

	private final boolean mNilpotentComponents;

	/**
	 * Use this constructor together with {@link DefaultNonTerminationAnalysisSettings} to create custom settings.
	 */
	public NonTerminationAnalysisSettings(final INonTerminationAnalysisSettings other) {
		mAnalysis = other.getAnalysis();
		mAllowBounded = other.isAllowBounded();
		mNumberOfGevs = other.getNumberOfGevs();
		mNilpotentComponents = other.isNilpotentComponents();
	}

	/**
	 * Verify that the settings are self-consistent and sane. Only makes assertion calls.
	 */
	public void checkSanity() {
		assert mNumberOfGevs >= 0;
	}

	/**
	 * Build a string description of the current preferences
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Nontermination analysis: ");
		sb.append(mAnalysis);
		sb.append(" Allow bounded executions: ");
		sb.append(mAllowBounded);
		sb.append(" Number of generalized eigenvectors: ");
		sb.append(mNumberOfGevs);
		sb.append(" Nilpotent components: ");
		sb.append(mNilpotentComponents);
		return sb.toString();
	}

	@Override
	public AnalysisType getAnalysis() {
		return mAnalysis;
	}

	@Override
	public boolean isAllowBounded() {
		return mAllowBounded;
	}

	@Override
	public int getNumberOfGevs() {
		return mNumberOfGevs;
	}

	@Override
	public boolean isNilpotentComponents() {
		return mNilpotentComponents;
	}
}
