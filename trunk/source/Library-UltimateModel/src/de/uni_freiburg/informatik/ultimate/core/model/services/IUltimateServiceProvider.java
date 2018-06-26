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

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;

/**
 * {@link IUltimateServiceProvider} is a facade for all services provided by UlimateCore.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IUltimateServiceProvider {

	IBacktranslationService getBacktranslationService();

	ILoggingService getLoggingService();

	IResultService getResultService();

	IProgressMonitorService getProgressMonitorService();

	<T extends IService, K extends IServiceFactory<T>> T getServiceInstance(Class<K> serviceType);

	IPreferenceProvider getPreferenceProvider(String pluginId);

	/**
	 * Create a new {@link IUltimateServiceProvider} that contains a layer over the preferences of the specified tools.
	 * You can then use the {@link IPreferenceProvider#put(String, String)} message to override settings for the
	 * specified tools without worrying that it may impact other {@link IUltimateServiceProvider} instances.
	 *
	 * Note that this method will generate a preference layer over the current settings of Ultimate, i.e., if you rely
	 * on default settings you should set them explicitly or use
	 * {@link #registerDefaultPreferenceLayer(Class, String...)}.
	 *
	 * @param creator
	 *            The class that creates the new layer (for debugging purposes)
	 * @param pluginIds
	 *            The plugin ids for which you want to create layers.
	 * @return A new {@link IUltimateServiceProvider} instance with layered preferences for the specified plugins.
	 */
	IUltimateServiceProvider registerPreferenceLayer(Class<?> creator, String... pluginIds);

	/**
	 * Similar to {@link #registerPreferenceLayer(Class, String...)} except that all preferences are assumed to be
	 * default.
	 */
	IUltimateServiceProvider registerDefaultPreferenceLayer(Class<?> creator, String... pluginIds);
}
