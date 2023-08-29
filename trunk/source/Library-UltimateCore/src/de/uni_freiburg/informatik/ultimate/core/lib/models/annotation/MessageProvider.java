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

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IMessageProvider;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.ISpec;

/**
 * Generic message provider for {@link ISpec.Type} specifications that are checked.
 * 
 * @author Manuel Bentele
 */
public abstract class MessageProvider implements IMessageProvider {

	/**
	 * Mapping of {@link Supplier}s returning customized positive messages for specified {@link ISpec.Type}s.
	 */
	private final Map<ISpec.Type, Supplier<String>> mPosMsgProviderOverrideFuncs;

	/**
	 * Mapping of {@link Supplier}s returning customized negative messages for specified {@link ISpec.Type}s.
	 */
	private final Map<ISpec.Type, Supplier<String>> mNegMsgProviderOverrideFuncs;

	/**
	 * Specification groups for which a specialized message provider delivers specification messages.
	 */
	private final Set<ISpec.Type.Group> mSpecGroups;

	/**
	 * Creates a generic message provider for {@link ISpec.Type.Group} labeled specifications that are checked.
	 */
	public MessageProvider(final ISpec.Type.Group group) {
		this(EnumSet.of(group));
	}

	/**
	 * Creates a generic message provider for {@link ISpec.Type.Group} labeled specifications that are checked.
	 */
	public MessageProvider(final Set<ISpec.Type.Group> groups) {
		mPosMsgProviderOverrideFuncs = new HashMap<ISpec.Type, Supplier<String>>();
		mNegMsgProviderOverrideFuncs = new HashMap<ISpec.Type, Supplier<String>>();
		mSpecGroups = groups;
	}

	/**
	 * Checks if messages for given specification type are supported by this message provider.
	 * 
	 * @param spec
	 *            specification type whose group should be checked.
	 * 
	 * @throws IllegalArgumentException
	 *             exception is thrown if specification group of specification type does not match the groups supported
	 *             by this message provider.
	 */
	private void checkSpecificationGroups(final ISpec.Type spec) throws IllegalArgumentException {
		if (!spec.isInGroups(mSpecGroups)) {
			throw new IllegalArgumentException(String.format(
					"Messages for specification type '%s' are not handled by this message provider for '%s'!", spec,
					mSpecGroups));
		}
	}

	@Override
	public void registerPositiveMessageOverride(final ISpec.Type spec, final Supplier<String> msgProviderFunc) {
		mPosMsgProviderOverrideFuncs.put(spec, msgProviderFunc);
	}

	@Override
	public void registerNegativeMessageOverride(final ISpec.Type spec, final Supplier<String> msgProviderFunc) {
		mNegMsgProviderOverrideFuncs.put(spec, msgProviderFunc);
	}

	@Override
	public String getPositiveMessage(final ISpec.Type spec) {
		final Supplier<String> posMsgProviderFunc = mPosMsgProviderOverrideFuncs.get(spec);

		checkSpecificationGroups(spec);

		if (posMsgProviderFunc != null) {
			return posMsgProviderFunc.get();
		} else {
			return getDefaultPositiveMessage(spec);
		}
	}

	@Override
	public String getNegativeMessage(final ISpec.Type spec) {
		final Supplier<String> negMsgProviderFunc = mNegMsgProviderOverrideFuncs.get(spec);

		checkSpecificationGroups(spec);

		if (negMsgProviderFunc != null) {
			return negMsgProviderFunc.get();
		} else {
			return getDefaultNegativeMessage(spec);
		}
	}
}
