package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;

public class InteractiveLive {
	private final IInteractive<Object> mInteractiveInterface;
	/**
	 * This variable was merely introduced to avoid frequent null checks on mInteractive for better readability.
	 */
	private final boolean mInteractiveMode;
	private Preferences mPreferences;
	private CompletableFuture<Void> mContinue;
	private final ILogger mLogger;

	public static class Preferences {

		private final boolean mCEXS;

		public boolean ismCEXS() {
			return mCEXS;
		}

		public boolean isIPS() {
			return mIPS;
		}

		public boolean isRSS() {
			return mRSS;
		}

		public boolean isPaused() {
			return mPaused;
		}

		private final boolean mIPS;
		private final boolean mRSS;
		private final boolean mPaused;

		public Preferences(boolean cexs, boolean ips, boolean rss, boolean paused) {
			mCEXS = cexs;
			mIPS = ips;
			mRSS = rss;
			mPaused = paused;
		}
	}

	public InteractiveLive(final IUltimateServiceProvider services, final ILogger logger) {
		mPreferences = new Preferences(false, false, false, true);
		mInteractiveInterface = services.getServiceInstance(TAConverterFactory.class);
		mLogger = logger;

		mInteractiveMode = mInteractiveInterface != null;
		if (mInteractiveMode)
			registerHandlers();
	}

	private void registerHandlers() {
		mInteractiveInterface.register(Preferences.class, this::setPreferences);
	}

	public IInteractive<Object> getInterface() {
		return mInteractiveInterface;
	}

	public boolean isInteractiveMode() {
		return mInteractiveMode;
	}

	public void send(final Object data) {
		mInteractiveInterface.send(data);
	}

	private synchronized void setPreferences(Preferences preferences) {
		mLogger.info("Received Live Preferences");
		mPreferences = preferences;
		if (!mPreferences.mPaused && mContinue != null && !mContinue.isDone()) {
			mContinue.complete(null);
		}
	}

	public Preferences getPreferences() {
		return mPreferences;
	}
	
	private boolean isPaused() {
		return isInteractiveMode() && mPreferences.isPaused();
	}

	public void waitIfPaused() {
		final boolean paused;
		synchronized (this) {
			paused = isInteractiveMode() && mPreferences.isPaused();
			if (paused) mContinue = new CompletableFuture<Void>();
		}
		if (paused) {
			mLogger.info("Client has paused Trace Abstraction - waiting for resume");
			try {
				mContinue.get();
			} catch (InterruptedException | ExecutionException e) {
				mLogger.error("Failed to get user automaton", e);
				getInterface().common().send(e);
				throw new ToolchainCanceledException(InteractiveLive.class);
			}
		}
	}
}
