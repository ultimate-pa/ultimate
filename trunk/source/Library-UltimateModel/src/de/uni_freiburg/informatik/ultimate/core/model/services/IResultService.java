/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.services;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

/**
 * {@link IResultService} allows tools to report results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IResultService {

	/**
	 * @return A map containing all results of a toolchain up to now.
	 */
	Map<String, List<IResult>> getResults();

	/**
	 * Report a result to the Ultimate result service. The result must not be {@code null} and must not contain
	 * {@code null} values (i.e., at least {@link IResult#getShortDescription()} and
	 * {@link IResult#getLongDescription()} must not be {@code null}).
	 *
	 * @param pluginId
	 *            The plugin ID of the tool which generated the result.
	 * @param result
	 *            The result itself.
	 */
	void reportResult(String pluginId, IResult result);

	/**
	 * Register a transformer function that is applied to <b>all</b> results during
	 * {@link #reportResult(String, IResult)}. If the transformer returns null for a result, this result is dropped.
	 *
	 * If multiple transformers are registered, they are executed in their registration order.
	 *
	 * Currently, you cannot unregister transformers.
	 *
	 * @param name
	 *            the name of the transformer; useful for debugging
	 * @param resultTransformer
	 *            the transformer function.
	 */
	void registerTransformer(final String name, final Function<IResult, IResult> resultTransformer);
}
