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

package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;

/**
 * Generic message provider for {@link Check} specifications that are checked.
 * 
 * @author Manuel Bentele
 */
public abstract class CheckMessageProvider {
	/**
	 * Mapping of {@link Supplier}s returning customized check messages for specified {@link Check.Spec}s.
	 */
	private final Map<Spec, Supplier<String>> mMsgProviderOverrideFuncs;

	/**
	 * Creates a new generic message provider for {@link Check} specifications that are checked.
	 */
	public CheckMessageProvider() {
		mMsgProviderOverrideFuncs = new HashMap<Spec, Supplier<String>>();
	}

	/**
	 * Returns a default message for a given {@link Check.Spec}.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return default message for the given {@code spec}.
	 */
	public abstract String getDefaultMessage(final Spec spec);

	/**
	 * Register a custom check message for a given {@link Check.Spec}.
	 * 
	 * @param spec
	 *            a specification that is checked and whose message is overwritten.
	 * @param msgProviderFunc
	 *            {@link Supplier} returning the customized check message for {@code spec}.
	 */
	public void registerMessageOverride(final Spec spec, final Supplier<String> msgProviderFunc) {

		mMsgProviderOverrideFuncs.put(spec, msgProviderFunc);
	}

	/**
	 * Returns a check message for a given {@link Check.Spec}.
	 * 
	 * @param spec
	 *            a specification that is checked.
	 * 
	 * @return message for the given {@code spec}.
	 */
	public String getMessage(final Spec spec) {
		final Supplier<String> msgProviderFunc = mMsgProviderOverrideFuncs.get(spec);

		if (msgProviderFunc != null) {
			return msgProviderFunc.get();
		} else {
			return getDefaultMessage(spec);
		}
	}
}
