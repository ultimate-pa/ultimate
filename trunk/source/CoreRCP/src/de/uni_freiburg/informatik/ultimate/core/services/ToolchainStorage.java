package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.HashMap;
import java.util.Map;

/**
 * Simple implementation of {@link IToolchainStorage} and {@link IUltimateServiceProvider}
 * 
 * @author dietsch
 * 
 */
public class ToolchainStorage implements IToolchainStorage, IUltimateServiceProvider {

	private final Map<String, IStorable> mToolchainStorage;

	public ToolchainStorage() {
		mToolchainStorage = new HashMap<String, IStorable>();
	}

	@Override
	public IStorable getStorable(String key) {
		return mToolchainStorage.get(key);
	}

	@Override
	public IStorable putStorable(String key, IStorable value) {
		return mToolchainStorage.put(key, value);
	}

	@Override
	public IStorable removeStorable(String key) {
		return mToolchainStorage.remove(key);
	}

	@Override
	public void clear() {
		for (IStorable storable : this.mToolchainStorage.values()) {
			storable.destroy();
		}
		mToolchainStorage.clear();
	}

	@Override
	public void destroyStorable(String key) {
		IStorable storable = mToolchainStorage.remove(key);
		if (storable != null) {
			storable.destroy();
		}
	}

	@Override
	public String toString() {
		return mToolchainStorage.toString();
	}

	@Override
	public IBacktranslationService getBacktranslationService() {
		return BacktranslationService.getService(this);
	}

	@Override
	public ILoggingService getLoggingService() {
		return LoggingService.getService(this);
	}

	@Override
	public IResultService getResultService() {
		return ResultService.getService(this);
	}

	@Override
	public IProgressMonitorService getProgressMonitorService() {
		return ProgressMonitorService.getService(this);
	}
}
