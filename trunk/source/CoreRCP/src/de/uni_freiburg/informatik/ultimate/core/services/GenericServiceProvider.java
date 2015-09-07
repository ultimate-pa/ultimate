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
package de.uni_freiburg.informatik.ultimate.core.services;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.IServiceFactoryFactory;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IServiceFactory;

public class GenericServiceProvider implements IStorable {

	private static final String sKey = "GenericServiceProvider";
	private final IServiceFactoryFactory mFactory;

	public GenericServiceProvider(IServiceFactoryFactory factory) {
		mFactory = factory;
	}

	@SuppressWarnings("unchecked")
	static <T extends IService,K extends IServiceFactory<T>> T getServiceInstance(
			ToolchainStorage toolchainStorage,
			Class<K> serviceType) {
		assert toolchainStorage != null;

		// first, check if this instance already exists in storage
		IStorable storable = toolchainStorage
				.getStorable(serviceType.getName());
		if (storable != null) {
			return (T) storable;
		}

		// no it doesnt, we need to create a new one
		GenericServiceProvider instance = (GenericServiceProvider) toolchainStorage
				.getStorable(sKey);
		T rtrValue = instance.mFactory.createService(serviceType,
				toolchainStorage, toolchainStorage);
		toolchainStorage.putStorable(serviceType.getName(), rtrValue);
		return rtrValue;
	}

	public static String getServiceKey() {
		return sKey;
	}

	@Override
	public void destroy() {
		// doesnt need destruction, the actual services destroy themselves 
	}

}
