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

import java.util.Objects;
import java.util.concurrent.CountDownLatch;

import de.uni_freiburg.informatik.ultimate.core.model.IServiceFactory;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ProgressMonitorService implements IStorable, IProgressMonitorService, IProgressAwareTimer {

	private static final String STORAGE_KEY = "CancelNotificationService";

	private final IToolchainProgressMonitor mMonitor;
	private final ILogger mLogger;
	private final IToolchainCancel mToolchainCancel;

	private IProgressAwareTimer mTimer;
	private boolean mCancelRequest;

	public ProgressMonitorService(final IToolchainProgressMonitor monitor, final ILogger logger,
			final IToolchainCancel cancel) {
		mMonitor = Objects.requireNonNull(monitor, "monitor may not be null");
		mLogger = Objects.requireNonNull(logger, "logger may not be null");
		mToolchainCancel = Objects.requireNonNull(cancel, "cancel may not be null");
		mCancelRequest = false;
	}

	@Override
	public boolean continueProcessing() {
		final boolean cancel = mMonitor.isCanceled() || mCancelRequest || isTimeout();
		if (cancel && mLogger.isDebugEnabled()) {
			mLogger.debug("Do not continue processing!");
		}
		return !cancel;
	}

	private boolean isTimeout() {
		return mTimer != null && !mTimer.continueProcessing();
	}

	@Override
	public void setSubtask(final String task) {
		mMonitor.subTask(task);
	}

	@Override
	public void setDeadline(long deadline) {
		if (System.currentTimeMillis() >= deadline) {
			mLogger.warn(
					String.format("Deadline was set to a date in the past, " + "effectively stopping the toolchain. "
							+ "Is this what you intended? Value of date was %,d", deadline));
			deadline = -1;
		}
		if (mTimer != null) {
			mLogger.warn("Replacing all timers with new deadline!");
		}
		mTimer = ProgressAwareTimer.createWithDeadline(null, deadline);
	}

	static ProgressMonitorService getService(final IToolchainStorage storage) {
		assert storage != null;
		return (ProgressMonitorService) storage.getStorable(STORAGE_KEY);
	}

	public static String getServiceKey() {
		return STORAGE_KEY;
	}

	@Override
	public void destroy() {
		mMonitor.done();
	}

	@Override
	public CountDownLatch cancelToolchain() {
		mCancelRequest = true;
		return mToolchainCancel.cancelToolchain();
	}

	@Override
	public IProgressAwareTimer getTimer(final long timeout) {
		return ProgressAwareTimer.createWithTimeout(null, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final long timeout) {
		return ProgressAwareTimer.createWithTimeout(this, timeout);
	}

	@Override
	public IProgressAwareTimer getChildTimer(final double percentage) {
		return ProgressAwareTimer.createWithPercentage(this, percentage);
	}

	@Override
	public long getDeadline() {
		if (mTimer == null) {
			return -1;
		}
		return mTimer.getDeadline();
	}

	@Override
	public IProgressAwareTimer getParent() {
		if (mTimer == null) {
			return null;
		}
		return mTimer.getParent();
	}

	@Override
	public IUltimateServiceProvider registerChildTimer(final IUltimateServiceProvider services,
			final IProgressAwareTimer timer) {
		return registerChildTimer(this, services, timer);
	}

	@Override
	public long remainingTime() {
		if (mTimer == null) {
			return -1;
		}
		return mTimer.remainingTime();
	}

	private static IUltimateServiceProvider registerChildTimer(final IProgressMonitorService parent,
			final IUltimateServiceProvider services, final IProgressAwareTimer timer) {
		if (timer == null) {
			throw new IllegalArgumentException("Cannot add null timer");
		}
		if (services == null) {
			throw new IllegalArgumentException("services is null");
		}
		if (checkParents(parent, timer)) {
			throw new IllegalArgumentException(
					"This timer would create a timer cycle, because itself, its parent or its grandparents are this object");
		}
		return new UltimateServiceProviderLayer(services, new ProgressMonitorLayer(parent, timer));
	}

	/**
	 * @return true if the timer or one of its parents are this, thus creating a timer cycle
	 */
	private static boolean checkParents(final IProgressMonitorService parent, final IProgressAwareTimer timer) {
		IProgressAwareTimer current = timer;
		while (current != null) {
			if (current == parent) {
				return true;
			}
			current = current.getParent();
		}
		return false;
	}

	private static final class ProgressMonitorLayer implements IProgressMonitorService {

		private final IProgressMonitorService mParent;
		private final IProgressAwareTimer mTimer;

		public ProgressMonitorLayer(final IProgressMonitorService parent, final IProgressAwareTimer timer) {
			mParent = Objects.requireNonNull(parent);
			mTimer = Objects.requireNonNull(timer);

		}

		@Override
		public CountDownLatch cancelToolchain() {
			return mParent.cancelToolchain();
		}

		@Override
		public long remainingTime() {
			return mTimer.remainingTime();
		}

		@Override
		public IProgressAwareTimer getTimer(final long timeout) {
			return ProgressAwareTimer.createWithTimeout(null, timeout);
		}

		@Override
		public IProgressAwareTimer getChildTimer(final long timeout) {
			return ProgressAwareTimer.createWithTimeout(this, timeout);
		}

		@Override
		public IProgressAwareTimer getChildTimer(final double percentage) {
			return ProgressAwareTimer.createWithPercentage(this, percentage);
		}

		@Override
		public IProgressAwareTimer getParent() {
			return mTimer.getParent();
		}

		@Override
		public long getDeadline() {
			return mTimer.getDeadline();
		}

		@Override
		public boolean continueProcessing() {
			return mParent.continueProcessing() && mTimer.continueProcessing();
		}

		@Override
		public void setSubtask(final String task) {
			mParent.setSubtask(task);
		}

		@Override
		public void setDeadline(final long date) {
			mParent.setDeadline(date);
		}

		@Override
		public IUltimateServiceProvider registerChildTimer(final IUltimateServiceProvider services,
				final IProgressAwareTimer timer) {
			return ProgressMonitorService.registerChildTimer(this, services, timer);
		}
	}

	private static final class UltimateServiceProviderLayer implements IUltimateServiceProvider {

		private final IUltimateServiceProvider mParent;
		private final IProgressMonitorService mProgressMonitorService;

		public UltimateServiceProviderLayer(final IUltimateServiceProvider services,
				final IProgressMonitorService progressMonitorService) {
			mParent = Objects.requireNonNull(services);
			mProgressMonitorService = Objects.requireNonNull(progressMonitorService);
		}

		@Override
		public IUltimateServiceProvider registerPreferenceLayer(final Class<?> creator, final String... pluginIds) {
			final IUltimateServiceProvider newLayer = mParent.registerPreferenceLayer(creator, pluginIds);
			return new UltimateServiceProviderLayer(newLayer, mProgressMonitorService);
		}

		@Override
		public IUltimateServiceProvider registerDefaultPreferenceLayer(final Class<?> creator,
				final String... pluginIds) {
			final IUltimateServiceProvider newLayer = mParent.registerDefaultPreferenceLayer(creator, pluginIds);
			return new UltimateServiceProviderLayer(newLayer, mProgressMonitorService);
		}

		@Override
		public IToolchainStorage getStorage() {
			return mParent.getStorage();
		}

		@Override
		public <T extends IService, K extends IServiceFactory<T>> T getServiceInstance(final Class<K> serviceType) {
			return mParent.getServiceInstance(serviceType);
		}

		@Override
		public IResultService getResultService() {
			return mParent.getResultService();
		}

		@Override
		public IProgressMonitorService getProgressMonitorService() {
			return mProgressMonitorService;
		}

		@Override
		public IPreferenceProvider getPreferenceProvider(final String pluginId) {
			return mParent.getPreferenceProvider(pluginId);
		}

		@Override
		public ILoggingService getLoggingService() {
			return mParent.getLoggingService();
		}

		@Override
		public IBacktranslationService getBacktranslationService() {
			return mParent.getBacktranslationService();
		}
	}
}
