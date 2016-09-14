/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.List;

/**
 * Combines several {@link ICsvProviderTransformer}s.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderTransformerCombinator<T> implements ICsvProviderTransformer<T> {
	private final List<ICsvProviderTransformer<T>> mTransformers;
	
	/**
	 * Constructor.
	 * 
	 * @param transformers
	 *            transformers
	 */
	public CsvProviderTransformerCombinator(final List<ICsvProviderTransformer<T>> transformers) {
		mTransformers = transformers;
	}
	
	@Override
	public ICsvProvider<T> transform(final ICsvProvider<T> csvProvider) {
		ICsvProvider<T> result = csvProvider;
		for (final ICsvProviderTransformer<T> transformer : mTransformers) {
			result = transformer.transform(result);
		}
		return result;
	}
}
