package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.jobs.Job;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;

public abstract class BasicToolchainJob extends Job {

	/**
	 * How do you want the toolchain to be processed? RUN_TOOLCHAIN: Everything
	 * new from the scratch. RERUN_TOOLCHAIN: run old toolchain on old input
	 * files RUN_OLDTOOLCHAIN: run old toolchain on new input files
	 * RUN_NEWTOOLCHAIN: run new toolchain on old input files
	 * 
	 */
	public static enum ChainMode {
		RUN_TOOLCHAIN, 
		RUN_NEWTOOLCHAIN, 
		RERUN_TOOLCHAIN, 
		@Deprecated
		RUN_OLDTOOLCHAIN
	}

	protected ChainMode mJobMode;
	protected ICore mCore;
	protected IController mController;
	protected Logger mLogger;
	protected ToolchainData mChain;
	protected PreludeProvider mPreludeFile;
	protected IUltimateServiceProvider mServices;
	private long mDeadline;

	public BasicToolchainJob(String name, ICore core, IController controller, ChainMode mode, Logger logger) {
		super(name);
		assert logger != null;
		mCore = core;
		mController = controller;
		mJobMode = mode;
		mLogger = logger;
		mDeadline = -1;

	}

	/**
	 * Write all IResults produced by the toolchain to the logger.
	 */
	protected void logResults() {
		if(mServices == null){
			return;
		}
		mLogger.info(" --- Results ---");
		for (Entry<String, List<IResult>> entry : mServices.getResultService().getResults().entrySet()) {
			mLogger.info(String.format(" * Results from %s:", entry.getKey()));

			for (IResult result : entry.getValue()) {
				StringBuilder sb = new StringBuilder();

				sb.append("  - ");
				sb.append(result.getClass().getSimpleName());
				if (result instanceof IResultWithLocation) {
					sb.append(" [Line: ");
					ILocation loc = ((IResultWithLocation) result).getLocation();
					sb.append(loc.getStartLine()).append("]");
				}
				sb.append(": ");
				sb.append(result.getShortDescription());
				mLogger.info(sb.toString());

				boolean appendCompleteLongDescription = new UltimatePreferenceStore(Activator.s_PLUGIN_ID)
						.getBoolean(CorePreferenceInitializer.LABEL_LONG_RESULT);
				String[] s = result.getLongDescription().split("\n");
				if (appendCompleteLongDescription) {
					mLogger.info(String.format("    %s", result.getLongDescription()));
				} else {
					mLogger.info(String.format("    %s", s[0].replaceAll("\\n|\\r", "")));
					if (s.length > 1) {
						mLogger.info("    [...]");
					}
				}

			}
		}
	}

	private void setTimeout() {
		long realDeadline = 0;

		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		int preferencesDeadline = ups.getInt(CorePreferenceInitializer.LABEL_TIMEOUT);

		// first , check if we have a deadline set by the executor
		if (mDeadline != -1) {
			// mDeadline is in ms
			realDeadline = mDeadline;
		} else {
			// preferenceDeadline is in s
			realDeadline = preferencesDeadline * 1000L;
		}

		if (realDeadline > 0) {
			// only set a timeout if there is a non-zero positive value
			mServices.getProgressMonitorService().setDeadline(
					System.currentTimeMillis() + realDeadline);
		}
	}

	protected void setServices(IUltimateServiceProvider services) {
		mServices = services;
		setTimeout();
	}

	/**
	 * Set a deadline in ms after which the toolchain should stop. All values smaller than
	 * 0 will be ignored. 0 disables all timeouts.
	 * 
	 * @param deadline
	 *            The deadline in ms
	 */
	public void setDeadline(long deadline) {
		if (deadline >= 0) {
			mDeadline = deadline;
		}
	}

}