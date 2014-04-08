package de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain;

import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.jobs.Job;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
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
		RUN_TOOLCHAIN, RUN_NEWTOOLCHAIN, RERUN_TOOLCHAIN, RUN_OLDTOOLCHAIN
	}

	protected ChainMode mJobMode;
	protected ICore mCore;
	protected IController mController;
	protected Logger mLogger;
	protected Toolchain mChain;
	protected PreludeProvider mPreludeFile;

	public BasicToolchainJob(String name, ICore core, IController controller, ChainMode mode) {
		super(name);
		mCore = core;
		mController = controller;
		mJobMode = mode;
		mLogger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	}

	/**
	 * Write all IResults produced by the toolchain to the logger.
	 */
	protected void logResults() {
		mLogger.info(" --- Results ---");
		for (Entry<String, List<IResult>> entry : UltimateServices.getInstance().getResultMap().entrySet()) {
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

	/**
	 * Use the timeout specified in the preferences of CoreRCP to set a deadline
	 * for the toolchain execution. Note that the ultimate core does not check
	 * that the toolchain execution complies with the deadline. Plugins should
	 * check if the deadline is overdue and abort. A timeout of 0 means that we
	 * do not set any deadline.
	 */
	public void setTimeout() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		int timeoutInPreferences = ups.getInt(CorePreferenceInitializer.LABEL_TIMEOUT);
		if (timeoutInPreferences == 0) {
			// do not set any timout
		} else {
			long timoutMilliseconds = timeoutInPreferences * 1000L;
			UltimateServices.getInstance().setDeadline(System.currentTimeMillis() + timoutMilliseconds);
		}
	}

}