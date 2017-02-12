/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

import java.util.EnumSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExternalWitnessValidationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExternalWitnessValidationResult.WitnessVerificationStatus;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Evaluate the overall result of a safety checker.
 *
 * First, we iterate through all IResults returned by Ultimate and put them into categories (which IResult is a witness
 * for which overall result). Afterwards we iterate through all categories in the order of their significance. The first
 * non-empty category is our overall result.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class SafetyCheckerOverallResultEvaluator implements IOverallResultEvaluator<SafetyCheckerOverallResult> {

	private final HashRelation<SafetyCheckerOverallResult, IResult> mCategory2Results = new HashRelation<>();
	private SafetyCheckerOverallResult mOverallResult;
	private Set<IResult> mMostSignificantResults;

	@Override
	public void evaluateOverallResult(final IResultService resultService) {
		for (final Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			for (final IResult result : entry.getValue()) {
				final SafetyCheckerOverallResult category = detectResultCategory(result);
				mCategory2Results.addPair(category, result);
			}
		}
		//@formatter:off
		//categories are ordered by priority, with the first being the lowest
		final SafetyCheckerOverallResult[] categoriesOrderedBySignificance = new SafetyCheckerOverallResult[] {
				SafetyCheckerOverallResult.SAFE,
				SafetyCheckerOverallResult.TIMEOUT,
				SafetyCheckerOverallResult.UNKNOWN,
				SafetyCheckerOverallResult.UNSAFE,
				SafetyCheckerOverallResult.UNSAFE_MEMTRACK,
				SafetyCheckerOverallResult.UNSAFE_FREE,
				SafetyCheckerOverallResult.UNSAFE_DEREF,
				SafetyCheckerOverallResult.UNSAFE_OVERAPPROXIMATED,
				SafetyCheckerOverallResult.UNSUPPORTED_SYNTAX,
				SafetyCheckerOverallResult.SYNTAX_ERROR,
				SafetyCheckerOverallResult.EXCEPTION_OR_ERROR,
		};
		//@formatter:on

		for (final SafetyCheckerOverallResult category : categoriesOrderedBySignificance) {
			if (mCategory2Results.getDomain().contains(category)) {
				mOverallResult = category;
			}
		}

		if (mOverallResult == null) {
			mOverallResult = SafetyCheckerOverallResult.NO_RESULT;
		} else {
			mMostSignificantResults = mCategory2Results.getImage(mOverallResult);
		}
	}

	protected SafetyCheckerOverallResult detectResultCategory(final IResult result) {
		if (result instanceof AllSpecificationsHoldResult) {
			return SafetyCheckerOverallResult.SAFE;
		} else if (result instanceof CounterExampleResult) {
			final CounterExampleResult<?, ?, ?> cer = (CounterExampleResult<?, ?, ?>) result;

			// TODO: This should change to take into account multiple specs
			final EnumSet<Spec> spec = cer.getCheckedSpecification().getSpec();
			if (spec.contains(Spec.ARRAY_INDEX) || spec.contains(Spec.MEMORY_DEREFERENCE)) {
				return SafetyCheckerOverallResult.UNSAFE_DEREF;
			} else if (spec.contains(Spec.MEMORY_FREE)) {
				return SafetyCheckerOverallResult.UNSAFE_FREE;
			} else if (spec.contains(Spec.MEMORY_LEAK)) {
				return SafetyCheckerOverallResult.UNSAFE_MEMTRACK;
			} else {
				return SafetyCheckerOverallResult.UNSAFE;
			}
		} else if (result instanceof UnprovableResult) {
			return SafetyCheckerOverallResult.UNKNOWN;
		} else if (result instanceof TypeErrorResult) {
			return SafetyCheckerOverallResult.SYNTAX_ERROR;
		} else if (result instanceof SyntaxErrorResult) {
			return SafetyCheckerOverallResult.SYNTAX_ERROR;
		} else if (result instanceof ITimeoutResult) {
			return SafetyCheckerOverallResult.TIMEOUT;
		} else if (result instanceof UnsupportedSyntaxResult) {
			return SafetyCheckerOverallResult.UNSUPPORTED_SYNTAX;
		} else if (result instanceof ExceptionOrErrorResult) {
			return SafetyCheckerOverallResult.EXCEPTION_OR_ERROR;
		} else if (result instanceof ExternalWitnessValidationResult) {
			// if there is a witness result it has to be verified, else it is an
			// error
			final ExternalWitnessValidationResult wit = (ExternalWitnessValidationResult) result;
			if (wit.getVerificationStatus() != WitnessVerificationStatus.VERIFIED) {
				return SafetyCheckerOverallResult.EXCEPTION_OR_ERROR;
			}
			return null;
		} else {
			return null;
		}
	}

	@Override
	public SafetyCheckerOverallResult getOverallResult() {
		return mOverallResult;
	}

	@Override
	public String generateOverallResultMessage() {
		switch (getOverallResult()) {
		case EXCEPTION_OR_ERROR:
			return getMostSignificantResults().toString();
		case NO_RESULT:
			return getOverallResult().toString();
		case SAFE:
			return getMostSignificantResults().toString();
		case SYNTAX_ERROR:
			return getMostSignificantResults().toString();
		case TIMEOUT:
			return getMostSignificantResults().toString();
		case UNKNOWN:
			return concatenateShortDescriptions(getMostSignificantResults());
		case UNSAFE:
		case UNSAFE_DEREF:
		case UNSAFE_FREE:
		case UNSAFE_MEMTRACK:
		case UNSAFE_OVERAPPROXIMATED:
			return concatenateShortDescriptions(getMostSignificantResults());
		case UNSUPPORTED_SYNTAX:
			return getMostSignificantResults().toString();
		default:
			throw new AssertionError("unknown overall result");
		}
	}

	@Override
	public Set<IResult> getMostSignificantResults() {
		return mMostSignificantResults;
	}

	private String concatenateShortDescriptions(final Set<IResult> iresults) {
		final StringBuilder sb = new StringBuilder();
		for (final IResult iResult : iresults) {
			sb.append(iResult.getShortDescription());
			sb.append(" ");
			if (iResult instanceof UnprovableResult) {
				sb.append(((UnprovableResult<?, ?, ?>) iResult).getReasons());
				sb.append(" ");
			}
		}
		return sb.toString();
	}

}
