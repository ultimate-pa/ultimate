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
package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class ResultService implements IStorable, IResultService {

	private final Map<String, List<IResult>> mResults;
	private final Map<String, Function<IResult, IResult>> mTransformers;
	private static final String KEY = "ResultService";

	private ResultService() {
		mResults = new HashMap<>();
		mTransformers = new LinkedHashMap<>();
	}

	@Override
	public void destroy() {
		mResults.clear();
		mTransformers.clear();
	}

	@Override
	public Map<String, List<IResult>> getResults() {
		return mResults;
	}

	@Override
	public void reportResult(final String id, final IResult origResult) {
		final IResult transformedResult = applyTransformers(origResult);
		if (transformedResult == null) {
			return;
		}
		if (transformedResult instanceof IResultWithLocation) {
			if (((IResultWithLocation) transformedResult).getLocation() == null) {
				throw new IllegalArgumentException("Location is null");
			}
		}
		if (transformedResult.getShortDescription() == null) {
			throw new IllegalArgumentException("ShortDescription is null");
		}
		if (transformedResult.getLongDescription() == null) {
			throw new IllegalArgumentException("LongDescription is null");
		}
		List<IResult> list = mResults.get(id);
		if (list == null) {
			list = new ArrayList<>();
		}
		list.add(transformedResult);
		mResults.put(id, list);
	}

	private IResult applyTransformers(final IResult origResult) {
		if (mTransformers.isEmpty()) {
			return origResult;
		}

		final Iterator<Entry<String, Function<IResult, IResult>>> iter = mTransformers.entrySet().iterator();
		IResult current = origResult;
		while (current != null && iter.hasNext()) {
			final Entry<String, Function<IResult, IResult>> currentTransformer = iter.next();
			if (currentTransformer.getValue() == null) {
				continue;
			}
			current = currentTransformer.getValue().apply(current);
		}
		return current;
	}

	static IResultService getService(final IToolchainStorage storage) {
		assert storage != null;
		IStorable rtr = storage.getStorable(KEY);
		if (rtr == null) {
			rtr = new ResultService();
			storage.putStorable(KEY, rtr);
		}
		return (IResultService) rtr;
	}

	@Override
	public String toString() {
		if (mResults.isEmpty()) {
			return "No Results";
		}
		return mResults.toString();
	}

	@Override
	public void registerTransformer(final String name, final Function<IResult, IResult> resultTransformer) {
		mTransformers.put(name, resultTransformer);
	}

}
