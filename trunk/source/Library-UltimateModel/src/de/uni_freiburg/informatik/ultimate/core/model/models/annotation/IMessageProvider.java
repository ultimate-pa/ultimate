/*
 * Copyright (C) 2023 Manuel Bentele
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

package de.uni_freiburg.informatik.ultimate.core.model.models.annotation;

import java.util.function.Supplier;

/**
 * Message provider interface returning messages for {@link ISpec.Type}s.
 * 
 * @author Manuel Bentele
 */
public interface IMessageProvider {

	/**
	 * Returns a positive default message for a given {@link ISpec.Type}.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return positive default message for the given {@code spec}.
	 */
	public default String getDefaultPositiveMessage(final ISpec.Type spec) {
		return spec.getDefaultPositiveMessage();
	}

	/**
	 * Returns a negative default message for a given {@link ISpec.Type}.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return negative default message for the given {@code spec}.
	 */
	public default String getDefaultNegativeMessage(final ISpec.Type spec) {
		return spec.getDefaultNegativeMessage();
	}

	/**
	 * Register a custom positive message supplier for a given {@link ISpec.Type}.
	 * 
	 * @param spec
	 *            a specification that is checked and whose message is overwritten.
	 * @param msgProviderFunc
	 *            {@link Supplier} returning the customized positive message for {@code spec}.
	 */
	public void registerPositiveMessageOverride(final ISpec.Type spec, final Supplier<String> msgProviderFunc);

	/**
	 * Register a custom negative message supplier for a given {@link ISpec.Type} specification.
	 * 
	 * @param spec
	 *            a specification that is checked and whose message is overwritten.
	 * @param msgProviderFunc
	 *            {@link Supplier} returning the customized negative message for {@code spec}.
	 */
	public void registerNegativeMessageOverride(final ISpec.Type spec, final Supplier<String> msgProviderFunc);

	/**
	 * Returns a positive message for a given {@link ISpec.Type} specification.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return positive message for the given {@code spec}.
	 * 
	 * @implNote This function considers messages after post-processing, i.e. custom message overwrites for specific
	 *           {@link ISpec.Type}s through {@link #registerPositiveMessageOverride(ISpec.Type, Supplier)} are
	 *           considered as well as positive default messages. Default messages can be obtained by
	 *           {@link #getDefaultPositiveMessage(ISpec.Type)}.
	 */
	public String getPositiveMessage(final ISpec.Type spec);

	/**
	 * Returns a negative message for a given {@link ISpec.Type} specification.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return negative message for the given {@code spec}.
	 * 
	 * @implNote This function considers messages after post-processing, i.e. custom message overwrites for specific
	 *           {@link ISpec.Type}s through {@link #registerNegativeMessageOverride(ISpec.Type, Supplier)} are
	 *           considered as well as negative default messages. Default messages can be obtained by
	 *           {@link #getDefaultNegativeMessage(ISpec.Type)}.
	 */
	public String getNegativeMessage(final ISpec.Type spec);
}
