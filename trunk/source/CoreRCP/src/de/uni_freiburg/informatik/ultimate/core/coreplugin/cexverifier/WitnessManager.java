package de.uni_freiburg.informatik.ultimate.core.coreplugin.cexverifier;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.commons.lang3.StringUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.util.MonitoredProcess.MonitoredProcessState;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.WitnessResult;

/**
 * The poorly named WitnessManager "handles" witnesses as specified by the
 * Ultimate Core settings.
 * 
 * E.g. it may create witness files from counter example results and may call
 * another verifier with this witness as input.
 * 
 * The actual witness generation is done by the corresponding plugin (i.e. via
 * {@link IProgramExecution#getSVCOMPWitnessString()}).
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @see IProgramExecution
 * 
 */
public class WitnessManager {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	public WitnessManager(Logger logger, IUltimateServiceProvider services, IToolchainStorage storage) {
		mLogger = logger;
		mServices = services;
		mStorage = storage;
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public void run() throws IOException, InterruptedException {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		final Collection<CounterExampleResult> cexResults = CoreUtil.filterResults(mServices.getResultService()
				.getResults(), CounterExampleResult.class);

		final IBacktranslationService backtrans = mServices.getBacktranslationService();

		int cexNo = 0;
		String suffix = null;
		for (final CounterExampleResult cex : cexResults) {
			final IProgramExecution cexProgramExecution = backtrans
					.translateProgramExecution(cex.getProgramExecution());
			final String svcompWitness = cexProgramExecution.getSVCOMPWitnessString();

			final boolean writeInWorkingDir = ups.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_WRITE_WORKINGDIR);
			final boolean writeBesideInputFile = ups.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_WRITE);
			final List<String> filenamesToDelete = new ArrayList<>();

			if (!writeBesideInputFile && !writeInWorkingDir) {
				continue;
			}
			String filename = null;
			if (writeInWorkingDir && svcompWitness != null) {
				filename = writeWitness(svcompWitness, null, suffix);
				filenamesToDelete.add(filename);
			}

			if (writeBesideInputFile && svcompWitness != null) {
				filename = writeWitness(svcompWitness, cex.getLocation().getFileName(), suffix);
				filenamesToDelete.add(filename);
			}

			if (ups.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_VERIFY)) {
				if (svcompWitness == null) {
					reportWitnessResult(null, cex, false);
				} else {
					checkWitness(filename, cex, svcompWitness);
				}
			} else if (ups.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_LOG)) {
				reportWitnessResult(svcompWitness, cex, false);
			}

			if (ups.getBoolean(CorePreferenceInitializer.LABEL_WITNESS_DELETE_GRAPHML)) {
				for (String fi : filenamesToDelete) {
					deleteFile(fi);
				}
			}
			cexNo++;
			suffix = String.valueOf(cexNo);
		}
	}

	private void deleteFile(String filename) {
		if (filename == null) {
			return;
		}
		File file = new File(filename);
		if (!file.delete()) {
			mLogger.warn("File " + filename + " could not be deleted");
		}
	}

	private String writeWitness(String svcompWitness, String origInputFile, String additionalSuffix) {
		final String suffix = "witness";
		final String fileending = ".graphml";
		final String separator = "-";

		StringBuilder filename = new StringBuilder();
		if (origInputFile != null) {
			filename.append(origInputFile).append(separator).append(suffix);
		} else {
			filename.append(suffix);
		}

		if (additionalSuffix != null) {
			filename.append(separator).append(additionalSuffix);
		}
		filename.append(fileending);

		try {
			File file = CoreUtil.writeFile(filename.toString(), svcompWitness);
			mLogger.info("Wrote witness to " + file.getAbsolutePath());
		} catch (IOException e) {
			mLogger.fatal("Something went wrong during writing of a witness", e);
			return null;
		}
		return filename.toString();
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	private void reportWitnessResult(String svcompWitness, CounterExampleResult cex, boolean isVerified) {
		mServices.getResultService().reportResult(cex.getPlugin(), new WitnessResult<>(cex, svcompWitness, isVerified));
	}

	@SuppressWarnings("rawtypes")
	private boolean checkWitness(String svcompWitnessFile, CounterExampleResult cex, String svcompWitness)
			throws IOException, InterruptedException {
		mLogger.info("Verifying witness for CEX: " + cex.getShortDescription());
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		final CorePreferenceInitializer.WitnessVerifierType type = ups.getEnum(
				CorePreferenceInitializer.LABEL_WITNESS_VERIFIER, CorePreferenceInitializer.WitnessVerifierType.class);
		final String command = ups.getString(CorePreferenceInitializer.LABEL_WITNESS_VERIFIER_COMMAND);

		switch (type) {
		case CPACHECKER:
			return checkWitnessWithCPAChecker(svcompWitnessFile, cex, command, svcompWitness);
		default:
			throw new UnsupportedOperationException("Witness verifier " + type + " unknown");
		}
	}

	@SuppressWarnings("rawtypes")
	private boolean checkWitnessWithCPAChecker(String svcompWitnessFile, CounterExampleResult cex, String command,
			String svcompWitness) throws IOException, InterruptedException {
		final String cpaCheckerHome = System.getenv().get("CPACHECKER_HOME");
		if (cpaCheckerHome == null) {
			mLogger.error("CPACHECKER_HOME not set, cannot use CPACHECKER as witness verifier");
			reportWitnessResult(svcompWitness, cex, false);
			return false;
		}
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		int timeoutInS = ups.getInt(CorePreferenceInitializer.LABEL_WITNESS_VERIFIER_TIMEOUT);

		final String originalFile = cex.getLocation().getFileName();
		final String[] cmdArray = makeCPACheckerCommand(command, svcompWitnessFile,
				ups.getString(CorePreferenceInitializer.LABEL_WITNESS_CPACHECKER_PROPERTY), originalFile,
				cpaCheckerHome, timeoutInS);
		timeoutInS++;
		mLogger.info(StringUtils.join(cmdArray, " "));
		MonitoredProcess cpaCheckerProcess = MonitoredProcess.exec(cmdArray, cpaCheckerHome, null, mServices, mStorage);
		final BufferedInputStream errorStream = new BufferedInputStream(cpaCheckerProcess.getErrorStream());
		final BufferedInputStream outputStream = new BufferedInputStream(cpaCheckerProcess.getInputStream());

		final String error = convertStreamToString(errorStream);
		final String output = convertStreamToString(outputStream);

		// wait for timeoutInS seconds for the witness checker, then kill it
		// forcefully
		mLogger.info("Waiting for " + timeoutInS + "s for CPA Checker...");
		MonitoredProcessState cpaCheckerState = cpaCheckerProcess.impatientWaitUntilTime(timeoutInS * 1000L);
		mLogger.info("Return code was " + cpaCheckerState.getReturnCode());

		// TODO: interpret error and output

		if (checkOutputForSuccess(output)) {
			mLogger.info("Witness for CEX was verified successfully");
			reportWitnessResult(svcompWitness, cex, true);
			return true;
		} else {
			final StringBuilder logMessage = new StringBuilder().append("Witness for CEX did not verify");
			if (cpaCheckerState.isKilled()) {
				logMessage.append(" due to timeout of ").append(timeoutInS).append("s");
			}
			logMessage.append("! CPAChecker said:").append(CoreUtil.getPlatformLineSeparator()).append("STDERR:")
					.append(CoreUtil.getPlatformLineSeparator()).append(error)
					.append(CoreUtil.getPlatformLineSeparator()).append("STDOUT:")
					.append(CoreUtil.getPlatformLineSeparator()).append(output);
			mLogger.error(logMessage.toString());
			reportWitnessResult(svcompWitness, cex, false);
			return false;
		}
	}

	private boolean checkOutputForSuccess(String output) {
		for (String line : output.split(CoreUtil.getPlatformLineSeparator())) {
			if (line.startsWith("Verification result: FALSE.")) {
				return true;
			}
		}
		return false;
	}

	private String[] makeCPACheckerCommand(String command, String svcompWitnessFile, String cpaCheckerProp,
			String originalFile, String workingDir, int timeoutInS) {
		final List<String> cmdArgs = new ArrayList<>();
		final String[] args = command.split(" ");
		final File file = new File(workingDir + File.separator + args[0]);
		cmdArgs.add(file.getAbsolutePath());
		for (int i = 1; i < args.length; ++i) {
			cmdArgs.add(args[i]);
		}
		cmdArgs.add("-timelimit");
		cmdArgs.add(String.valueOf(timeoutInS));
		cmdArgs.add("-spec");
		cmdArgs.add(escape(svcompWitnessFile));
		cmdArgs.add("-spec");
		cmdArgs.add(escape(cpaCheckerProp));
		cmdArgs.add(escape(originalFile));
		return cmdArgs.toArray(new String[cmdArgs.size()]);
	}

	private String escape(String str) {
		return str;
	}

	private static String convertStreamToString(InputStream input) {
		final BufferedReader reader = new BufferedReader(new InputStreamReader(input));
		final StringBuilder out = new StringBuilder();
		String line;
		try {
			while ((line = reader.readLine()) != null) {
				out.append(line).append(CoreUtil.getPlatformLineSeparator());
			}
			reader.close();
		} catch (IOException e) {
			// supress all exceptions
		}
		return out.toString();
	}
}
