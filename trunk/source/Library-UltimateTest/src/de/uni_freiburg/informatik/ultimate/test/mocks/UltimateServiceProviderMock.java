/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE JUnit Helper Library.
 *
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.mocks;

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateServiceProviderMock implements IUltimateServiceProvider {

	private final LogLevel mDefaultLevel;

	UltimateServiceProviderMock(final LogLevel defaultLevel) {
		mDefaultLevel = defaultLevel;
	}

	@Override
	public IBacktranslationService getBacktranslationService() {
		return new BacktranslationServiceMock();
	}

	@Override
	public ILoggingService getLoggingService() {
		return new LoggingServiceMock(mDefaultLevel);
	}

	@Override
	public IResultService getResultService() {
		return new ResultServiceMock();
	}

	@Override
	public IProgressMonitorService getProgressMonitorService() {
		return new ProgressMonitorServiceMock();
	}

	@Override
	public <T extends IService, K extends IServiceFactory<T>> T getServiceInstance(final Class<K> serviceType) {
		// never find the matching service
		return null;
	}

	@Override
	public IPreferenceProvider getPreferenceProvider(final String pluginId) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public IUltimateServiceProvider registerPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public IUltimateServiceProvider registerDefaultPreferenceLayer(final Class<?> creator, final String... pluginIds) {
		throw new UnsupportedOperationException("Not yet supported");
	}
}
