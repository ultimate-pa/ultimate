/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Termination Argument consisting of a ranking function given as a list of lexicographically ordered Boogie
 * expressions.
 *
 * @author Matthias Heizmann
 * @author Jan Leike
 * @param <P>
 *            program position class
 */
public class TerminationArgumentResult<P extends IElement, E> extends AbstractResultAtElement<P> {
	private final String mRankingFunctionDescription;
	private final E[] mRankingFunction;
	private final E[] mSupportingInvariants;
	private final Class<E> mExprClazz;

	/**
	 * Construct a termination argument result
	 *
	 * @param position
	 *            program position
	 * @param plugin
	 *            the generating plugin's name
	 * @param ranking_function
	 *            a ranking function as an implicitly lexicographically ordered list of Boogie expressions
	 * @param rankingFunctionDescription
	 *            short name of the ranking function
	 * @param supporting_invariants
	 *            list of supporting invariants in form of Boogie expressions
	 * @param translatorSequence
	 *            the toolchain's translator sequence
	 */
	public TerminationArgumentResult(final P position, final String plugin, final E[] ranking_function,
			final String rankingFunctionDescription, final E[] supporting_invariants,
			final IBacktranslationService translatorSequence, final Class<E> exprClazz) {
		super(position, plugin, translatorSequence);
		mRankingFunction = ranking_function;
		mRankingFunctionDescription = rankingFunctionDescription;
		mSupportingInvariants = supporting_invariants;
		mExprClazz = exprClazz;
	}

	@Override
	public String getShortDescription() {
		return "Found " + mRankingFunctionDescription + " ranking function";
	}

	@Override
	public String getLongDescription() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Found a termination argument consisting of the ");
		sb.append(mRankingFunctionDescription);
		sb.append(" ranking function");
		sb.append(": [");
		boolean needsComma = false;
		for (final E e : mRankingFunction) {
			if (needsComma) {
				sb.append(", ");
			} else {
				// this was the first iteration, from now on we need a comma.
				needsComma = true;
			}
			sb.append(mTranslatorSequence.translateExpressionToString(e, mExprClazz));
		}
		sb.append("]");
		if (mSupportingInvariants.length > 0) {
			sb.append(" and the following supporting invariants: ");
			for (final E e : mSupportingInvariants) {
				sb.append(mTranslatorSequence.translateExpressionToString(e, mExprClazz));
			}
		} else {
			sb.append(" for which no supporting invariant is required.");
		}
		return sb.toString();
	}

	public String getRankingFunctionDescription() {
		return mRankingFunctionDescription;
	}

	public E[] getRankingFunction() {
		return mRankingFunction;
	}

	public E[] getSupportingInvariants() {
		return mSupportingInvariants;
	}
}
