/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CLI plug-in.
 *
 * The ULTIMATE CLI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CLI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CLI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CLI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CLI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.controller.eliminator;

import java.io.File;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.RcpProgressMonitorWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.RcpUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ExceptionThrowingSMTLIB2Parser;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.UltimateEliminator;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib.SMTLIBParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * The {@link UltimateEliminatorController} class provides a user interface for command lines based on the
 * {@link IController} interface.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class UltimateEliminatorController implements IController<RunDefinition> {

	private ILogger mLogger;
	private IToolchainData<RunDefinition> mToolchain;

	@Override
	public int init(final ICore<RunDefinition> core) {
		if (core == null) {
			return -1;
		}

		mLogger = core.getCoreLoggingService().getControllerLogger();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Initializing CommandlineController...");
			mLogger.debug("Data directory is " + Platform.getLocation());
			mLogger.debug("Working directory is " + Platform.getInstallLocation().getURL());
			mLogger.debug("user.dir is " + System.getProperty("user.dir"));
			mLogger.debug("CLI Controller version is " + RcpUtils.getVersion(Activator.PLUGIN_ID));
		}

		final String[] param = Platform.getCommandLineArgs();

		// start parse arguments
		final SmtInterpolLogProxyWrapper smtinterpolLogger = new SmtInterpolLogProxyWrapper(mLogger);
		final OptionMap options = new OptionMap(smtinterpolLogger, true);
		options.set(":continue-on-error", false);
		IParser parser = new ExceptionThrowingSMTLIB2Parser();

		int paramctr = 0;
		String settingsFile = null;
		String externalSolverCommand = null;
		while (paramctr < param.length && param[paramctr].startsWith("-")) {
			if (param[paramctr].equals("--")) {
				paramctr++;
				break;
			} else if (param[paramctr].equals("-no-success")) {
				options.set(":print-success", false);
			} else if (param[paramctr].equals("-v")) {
				options.set(":verbosity", LogProxy.LOGLEVEL_DEBUG);
			} else if (param[paramctr].equals("-w")) {
				options.set(":verbosity", LogProxy.LOGLEVEL_WARN);
			} else if (param[paramctr].equals("-q")) {
				options.set(":verbosity", LogProxy.LOGLEVEL_ERROR);
			} else if (param[paramctr].equals("-t") && ++paramctr < param.length) {
				options.set(":timeout", param[paramctr]);
			} else if (param[paramctr].equals("-r") && ++paramctr < param.length) {
				options.set(":random-seed", param[paramctr]);
			} else if (param[paramctr].equals("-s") && ++paramctr < param.length) {
				settingsFile = param[paramctr];
			} else if (param[paramctr].equals("-external-solver") && ++paramctr < param.length) {
				externalSolverCommand = param[paramctr];
			} else if (param[paramctr].equals("-o") && paramctr + 1 < param.length) {
				paramctr++;
				final String opt = param[paramctr];
				final int eq = opt.indexOf('=');
				String name;
				Object value;
				if (eq == -1) {
					name = opt;
					value = Boolean.TRUE;
				} else {
					name = opt.substring(0, eq);
					value = opt.substring(eq + 1);
				}
				try {
					options.set(":" + name, value);
				} catch (final UnsupportedOperationException ex) {
					System.err.println("Unknown option :" + name + ".");
					return -1;
				} catch (final SMTLIBException ex) {
					System.err.println(ex.getMessage());
					return -1;
				}
			} else if (param[paramctr].equals("-smt2")) {
				parser = new SMTLIB2Parser();
			} else if (param[paramctr].equals("-smt")) {
				parser = new SMTLIBParser();
			} else if (param[paramctr].equals("-trace")) {
				options.set(":verbosity", LogProxy.LOGLEVEL_TRACE);
			} else if (param[paramctr].equals("-version")) {
				printVersion(core);
				return IApplication.EXIT_OK;
			} else if (param[paramctr].equals("-product")) {
				// ignore and skip argument, is RCP specific
				++paramctr;
			} else if (param[paramctr].equals("--launcher.suppressErrors")) {
				// ignore and skip argument, is RCP specific
			} else {
				mLogger.info("Unknown option: " + param[paramctr]);
				printArgs(param);
				usage();
				return -1;
			}
			++paramctr;
		}

		String filename = null;
		if (paramctr < param.length) {
			filename = param[paramctr++];
		}
		if (paramctr != param.length) {
			usage();
			return -1;
		}
		options.started();

		try {
			mToolchain = core.createToolchainData();
			setCoreLoggerToError();
			core.resetPreferences(true);
			setCoreLoggerToError();
			if (settingsFile != null) {
				core.loadPreferences(settingsFile, true);
			}
			mToolchain = core.createToolchainData();
			setCoreLoggerToError();

			// from now on, use the shutdown hook that disables the toolchain if the user presses CTRL+C (hopefully)
			Runtime.getRuntime().addShutdownHook(new Thread(new SigIntTrap(mToolchain, mLogger), "SigIntTrap"));

			final IToolchain<RunDefinition> tc = core.requestToolchain(new File[0]);
			final NullProgressMonitor pm = new NullProgressMonitor();
			final IToolchainProgressMonitor rcpPm = RcpProgressMonitorWrapper.create(pm);
			tc.init(rcpPm);
			final IToolchainData<RunDefinition> tcData = tc.makeToolSelection(rcpPm);
			assert tcData == mToolchain;

			// actual start of eliminator
			final IUltimateServiceProvider services = tcData.getServices();

			final Script solver;
			if (externalSolverCommand == null) {
				solver = new SMTInterpol(null, options);
			} else {
				solver = new Scriptor(externalSolverCommand, mLogger, services, "External Solver");
			}
			final Script eliminator = new UltimateEliminator(services, mLogger, solver);
			final int exitCode = parser.run(eliminator, filename, options);
			core.releaseToolchain(tc);
			return exitCode;
		} catch (final Throwable ex) {
			mLogger.fatal(ex);
			mLogger.fatal(CoreUtil.getStackTrace("\t", ex));
			return -1;
		}
	}

	private void setCoreLoggerToError() {
		final IPreferenceProvider provider =
				mToolchain.getServices().getPreferenceProvider("de.uni_freiburg.informatik.ultimate.core");
		provider.put("Log level for core plugin", "ERROR");
	}

	private void usage() {
		mLogger.info("If no INPUTFILE is given, stdin is used.");
		mLogger.info("  -no-success                   Don't print success messages.");// NOCHECKSTYLE
		mLogger.info("  -o <opt>=<value>              Set option :opt to value. The default value is true.");// NOCHECKSTYLE
		mLogger.info("  -q                            Only print error messages.");// NOCHECKSTYLE
		mLogger.info("  -w                            Don't print statistics and models.");// NOCHECKSTYLE
		mLogger.info("  -v                            Print debugging messages.");
		mLogger.info("  -t <num>                      Set the timeout per check-sat call to <num> milliseconds.");// NOCHECKSTYLE
		mLogger.info("  -r <num>                      Use a different random seed.");// NOCHECKSTYLE
		mLogger.info("  -s <file>                     Use Ultimate settings file <file>");// NOCHECKSTYLE
		mLogger.info("  -smt2                         Parse input as SMTLIB 2 script.");// NOCHECKSTYLE
		mLogger.info("  -version                      Print version and exit.");
		mLogger.info("  -external-solver \"<cmd>\"    Use external solver with command <cmd> as underlying SMT solver");
	}

	private void printVersion(final ICore<RunDefinition> core) {
		mLogger.info("This is Ultimate " + core.getUltimateVersionString());
		// DD: note that the next line is used in benchexec
		mLogger.info("Version is " + RcpUtils.getVersion(Activator.PLUGIN_ID));
		mLogger.info("Maximal heap size is set to "
				+ CoreUtil.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true));
		final String[] sysProps = new String[] { "java.version", "java.specification.name", "java.specification.vendor",
				"java.specification.version", "java.runtime.version", "java.vm.name", "java.vm.vendor",
				"java.vm.version", };

		for (final String sysProp : sysProps) {
			String value = System.getProperty(sysProp);
			if (value == null) {
				value = "unknown";
			}
			mLogger.info("Value of " + sysProp + " is " + value);
		}

	}

	private void printArgs(final String[] args) {
		mLogger.error("Arguments were \"" + String.join(" ", args) + "\"");
	}

	@Override
	public ISource selectParser(final Collection<ISource> parser) {
		throw new UnsupportedOperationException("Interactively selecting parsers is not supported in CLI mode");
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IToolchainData<RunDefinition> selectTools(final List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		throw new UnsupportedOperationException("Interactively selecting models is not supported in CLI mode");
	}

	@Override
	public void displayToolchainResults(final IToolchainData<RunDefinition> toolchain,
			final Map<String, List<IResult>> results) {
		final ResultSummarizer summarizer = new ResultSummarizer(results);
		switch (summarizer.getResultSummary()) {
		case CORRECT:
			mLogger.info("RESULT: Ultimate proved your program to be correct!");
			break;
		case INCORRECT:
			mLogger.info("RESULT: Ultimate proved your program to be incorrect!");
			break;
		default:
			mLogger.info("RESULT: Ultimate could not prove your program: " + summarizer.getResultDescription());
			break;
		}
	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		mLogger.fatal("RESULT: An exception occured during the execution of Ultimate: " + description, ex);
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void prerun(final IToolchainData<RunDefinition> tcData) {
		// not needed
	}

	private static final class SigIntTrap implements Runnable {

		private static final int SHUTDOWN_GRACE_PERIOD_SECONDS = 5;
		private final IToolchainData<RunDefinition> mCurrentToolchain;
		private final ILogger mLogger;

		public SigIntTrap(final IToolchainData<RunDefinition> currentToolchain, final ILogger logger) {
			mCurrentToolchain = currentToolchain;
			mLogger = logger;
		}

		@Override
		public void run() {
			final IUltimateServiceProvider services = mCurrentToolchain.getServices();
			if (services == null) {
				return;
			}
			final IProgressMonitorService progressMonitor = services.getProgressMonitorService();
			if (progressMonitor == null) {
				return;
			}

			final CountDownLatch cdl = progressMonitor.cancelToolchain();
			try {
				if (!cdl.await(SHUTDOWN_GRACE_PERIOD_SECONDS, TimeUnit.SECONDS)) {
					mLogger.fatal("Cannot interrupt operation gracefully because timeout expired. Forcing shutdown");
				}
			} catch (@SuppressWarnings("squid:S2142") final InterruptedException e) {
				mLogger.fatal("Received interrupt while waiting for graceful shutdown: " + e.getMessage());
				return;
			}
		}
	}

}
