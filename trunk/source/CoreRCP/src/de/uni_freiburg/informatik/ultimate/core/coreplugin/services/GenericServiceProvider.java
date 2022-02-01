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

import de.uni_freiburg.informatik.ultimate.core.coreplugin.IServiceFactoryFactory;
import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class GenericServiceProvider implements IStorable {

	private static final String KEY = "GenericServiceProvider";
	private final IServiceFactoryFactory mFactory;

	public GenericServiceProvider(final IServiceFactoryFactory factory) {
		mFactory = factory;
	}

	@SuppressWarnings("unchecked")
	static <T extends IService, K extends IServiceFactory<T>> T
			getServiceInstance(final ToolchainStorage toolchainStorage, final Class<K> serviceType) {
		assert toolchainStorage != null;

		// first, check if this instance already exists in storage
		final IStorable storable = toolchainStorage.getStorable(serviceType.getName());
		if (storable != null) {
			return (T) storable;
		}

		// no it doesnt, we need to create a new one
		final GenericServiceProvider instance = (GenericServiceProvider) toolchainStorage.getStorable(KEY);
		final T rtrValue = instance.mFactory.createService(serviceType, toolchainStorage, toolchainStorage);
		if (rtrValue != null) {
			toolchainStorage.putStorable(serviceType.getName(), rtrValue);
		}
		return rtrValue;
	}

	public static String getServiceKey() {
		return KEY;
	}

	@Override
	public void destroy() {
		// doesnt need destruction, the actual services destroy themselves
	}

}
