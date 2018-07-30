/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * @author Matthias Heizmann
 * @author Jan Leike
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class ResultUtil {

	private ResultUtil() {
		// do not instantiate utility class
	}

	public static <TE extends IElement, E> List<ILocation> getLocationSequence(final IProgramExecution<TE, E> pe) {
		final List<ILocation> result = new ArrayList<>();
		for (int i = 0; i < pe.getLength(); i++) {
			final AtomicTraceElement<TE> te = pe.getTraceElement(i);
			result.add(ILocation.getAnnotation(te.getTraceElement()));
		}
		return result;
	}

	/**
	 * Returns new Collections that contains all IResults from ultimateIResults that are subclasses of the class
	 * resClass.
	 */
	public static <E extends IResult> Collection<E> filterResults(final Map<String, List<IResult>> results,
			final Class<E> resClass) {
		final List<E> filteredList = new ArrayList<>();
		for (final Entry<String, List<IResult>> entry : results.entrySet()) {
			filteredList.addAll(filterResults(entry.getValue(), resClass));
		}
		return filteredList;
	}

	/**
	 * Returns new Collections that contains all IResults from ultimateIResults that are subclasses of the class
	 * resClass.
	 */
	public static Collection<IResult> filterResults(final Map<String, List<IResult>> results,
			final Predicate<IResult> pred) {
		final List<IResult> filteredList = new ArrayList<>();
		for (final Entry<String, List<IResult>> entry : results.entrySet()) {
			filteredList.addAll(filterResults(entry.getValue(), pred));
		}
		return filteredList;
	}

	public static <E extends IResult> Collection<E> filterResults(final List<IResult> results,
			final Class<E> resClass) {
		final List<E> filteredList = new ArrayList<>();
		for (final IResult result : results) {
			if (resClass.isAssignableFrom(result.getClass())) {
				@SuppressWarnings("unchecked")
				final E benchmarkResult = (E) result;
				filteredList.add(benchmarkResult);
			}
		}
		return filteredList;
	}

	public static Collection<IResult> filterResults(final List<IResult> results, final Predicate<IResult> pred) {
		return results.stream().filter(pred).collect(Collectors.toList());
	}

	public static boolean anyMatch(final Map<String, List<IResult>> results, final Predicate<IResult> pred) {
		return results.entrySet().stream().flatMap(a -> a.getValue().stream()).anyMatch(pred);
	}

	public static <SE> String translateExpressionToString(final IBacktranslationService translator,
			final Class<SE> clazz, final SE[] expression) {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i < expression.length; ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(translator.translateExpressionToString(expression[i], clazz));
		}
		return sb.toString();
	}

	/**
	 * Return the checked specification that is checked at the error location.
	 */
	public static <ELEM extends IElement> Check getCheckedSpecification(final ELEM element) {
		final Check check = Check.getAnnotation(element);
		if (check != null) {
			return check;
		}
		final ILocation loc = ILocation.getAnnotation(element);
		if (loc == null) {
			return null;
		}
		final IAnnotations checkCand = loc.getCheck();
		if (checkCand instanceof Check) {
			return (Check) checkCand;
		}
		return null;
	}

	/**
	 * Write all results contained in the {@link IResultService} instance to a logger instance.
	 *
	 * @param logger
	 *            The {@link ILogger} instance to which the results should be written.
	 * @param resultService
	 *            The {@link IResultService} instance from which the results should be fetched.
	 * @param appendCompleteLongDescription
	 *            true if the complete long descriptions of the results should be written, false if only the first line
	 *            of the long description should be written.
	 */
	public static void logResults(final ILogger logger, final IResultService resultService,
			final boolean appendCompleteLongDescription) {
		if (logger == null || resultService == null) {
			throw new IllegalArgumentException("logger or resultService is null");
		}
		logger.info(" --- Results ---");
		for (final Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			logger.info(String.format(" * Results from %s:", entry.getKey()));

			for (final IResult result : entry.getValue()) {
				logResult(logger, result, appendCompleteLongDescription);
			}
		}
	}

	private static void logResult(final ILogger logger, final IResult result,
			final boolean appendCompleteLongDescription) {
		final StringBuilder sb = new StringBuilder();

		sb.append("  - ");
		sb.append(result.getClass().getSimpleName());
		if (result instanceof IResultWithLocation) {
			final ILocation loc = ((IResultWithLocation) result).getLocation();
			if (loc.getStartLine() != 0) {
				sb.append(" [Line: ");
				sb.append(loc.getStartLine()).append("]");
			} else {
				sb.append(" [UNKNOWN] ");
			}
		}
		sb.append(": ");
		sb.append(result.getShortDescription());
		logger.info(sb.toString());

		final String[] s = result.getLongDescription().split("\n");
		if (appendCompleteLongDescription) {
			logger.info(String.format("    %s", result.getLongDescription()));
		} else {
			logger.info(String.format("    %s", s[0].replaceAll("\\n|\\r", "")));
			if (s.length > 1) {
				logger.info("    [...]");
			}
		}
	}

	/**
	 * Returns all ICsvProviderProvider of class benchmarkClass that are stored in the BenchmarkResults of
	 * ultimateIResults.
	 */
	@SuppressWarnings("rawtypes")
	public static <E extends ICsvProviderProvider<?>> Collection<E> getCsvProviderProviderFromUltimateResults(
			final Map<String, List<IResult>> ultimateIResults, final Class<E> benchmarkClass) {
		final Collection<StatisticsResult> benchmarks = filterResults(ultimateIResults, StatisticsResult.class);
		final List<E> filteredList = new ArrayList<>();
		for (final StatisticsResult<?> benchmarkResult : benchmarks) {
			@SuppressWarnings("unchecked")
			final E benchmark = (E) benchmarkResult.getStatistics();
			if (benchmark.getClass().isAssignableFrom(benchmarkClass)) {
				filteredList.add(benchmark);
			}
		}
		return filteredList;
	}
}
