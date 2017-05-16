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
package de.uni_freiburg.informatik.ultimate.servercontroller;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CancellationException;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractiveQueue;
import de.uni_freiburg.informatik.ultimate.interactive.common.Converter;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.ChoiceRequest;
import de.uni_freiburg.informatik.ultimate.interactive.commondata.RootPath;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.AbstractConverter;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientQuittedException;
import de.uni_freiburg.informatik.ultimate.server.Client;
import de.uni_freiburg.informatik.ultimate.server.IInteractiveServer;
import de.uni_freiburg.informatik.ultimate.servercontroller.converter.ControllerConverter;
import de.uni_freiburg.informatik.ultimate.servercontroller.protoserver.ProtoServer;
import de.uni_freiburg.informatik.ultimate.servercontroller.util.CommandLineArgs;
import de.uni_freiburg.informatik.ultimate.servercontroller.util.RcpUtils;

/**
 * The {@link ServerController} class provides a user interface for Clients that can connect via TCP.
 *
 * @author Julian Jarecki
 */
public class ServerController implements IController<RunDefinition> {

	private ILogger mLogger;
	private IInteractiveServer<GeneratedMessageV3> mServer;
	private IToolchainData<RunDefinition> mToolchain;

	private IInteractive<Object> mInternalInterface;
	private IInteractive<GeneratedMessageV3> mProtoInterface;
	private IInteractive<Object> mCommonInterface;

	private CommandLineArgs mCla;

	private AbstractConverter.Initializer<GeneratedMessageV3> mConverterInitializer;
	private int mListenTimeout;

	@Override
	public int init(final ICore<RunDefinition> core) {
		if (core == null) {
			return -1;
		}

		mLogger = core.getCoreLoggingService().getControllerLogger();

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Initializing ServerController...");
			mLogger.debug("Data directory is " + Platform.getLocation());
			mLogger.debug("Working directory is " + Platform.getInstallLocation().getURL());
			mLogger.debug("user.dir is " + System.getProperty("user.dir"));
			mLogger.debug("ServerController version is " + RcpUtils.getVersion(Activator.PLUGIN_ID));
		}

		final String[] args = Platform.getCommandLineArgs();

		try {
			mCla = CommandLineArgs.parse(args);
		} catch (final org.apache.commons.cli.ParseException e) {
			mLogger.error(e.getMessage());
			mLogger.error("Arguments were \"" + String.join(" ", args) + "\"");
			mLogger.error("--");
			return -1;
		}

		mServer = new ProtoServer(mLogger, mCla.getPort());

		// final File workingDir = RcpUtils.getWorkingDirectory();
		final Map<File, IToolchainData<RunDefinition>> availableToolchains =
				getAvailableToolchains(core, mCla.getToolchainDirPath());

		// final File[] availableSettingsFiles = getAvailableSettingsFiles();

		// final File[] availableInputFiles = getAvailableInputFiles();

		if (availableToolchains.isEmpty()) {
			mLogger.fatal("No toolchains found in " + mCla.getToolchainDirPath());
			return -1;
		}

		mListenTimeout = mCla.getTimeout();

		mLogger.debug("Starting Server on Port " + mCla.getPort());
		mServer.start();

		int result = IApplication.EXIT_OK;
		int connectionNumber = 0;

		try {
			while (true) {
				try {
					mServer.setHelloMessage("Connection " + connectionNumber++);
					initWrapper(core, availableToolchains);

					if (false)
						break; // TODO: add settings that limit the server to a single (or fixed numer or time) run
				} catch (final CancellationException e) {
					mLogger.error("Cancelled some Future", e);
				} catch (final ExecutionException e) {
					// throw e.getCause()
					if (e.getCause() instanceof IOException) {
						mLogger.error("It seems like the Connection has been Lost. Reinitializing controller.", e);
						result = IApplication.EXIT_RELAUNCH; // What does/should that do?
					} else if (e.getCause() instanceof ClientQuittedException) {
						mLogger.error("Client quitted. Reinitializing controller.", e);
						result = IApplication.EXIT_RELAUNCH; // What does/should that do?
					} else {
						mLogger.fatal(e);
						mLogger.error(e);
						result = -1;
						break;
					}
				} finally {
					Thread.sleep(200); // wait a little bit before handling the next client.
				}
			}
		} catch (InterruptedException | TimeoutException e) {
			mLogger.fatal(e);
			e.printStackTrace();
			result = -1;
		} catch (final Throwable e) {
			mLogger.fatal(e);
			e.printStackTrace();
			result = -1;
		} finally {
			mLogger.info("Interactive Controller terminated - shutting down Server.");
			mServer.stop();
		}
		return result;
	}

	/*
	 * private File[] getAvailableSettingsFiles() { final File[] result = mCla.getSettingsFilePath().listFiles((file,
	 * name) -> name.endsWith(".epf")); if (result.length == 0) { mLogger.error("No Settings files found in " +
	 * mCla.getSettingsFilePath().getAbsolutePath()); return null; } return result; }
	 * 
	 * private File[] getAvailableInputFiles() { final File[] result = mCla.getInputDirPath().listFiles(f ->
	 * f.isFile()); if (result.length == 0) { mLogger.error("No Input files found in " +
	 * mCla.getInputDirPath().getAbsolutePath()); return null; } return result; }
	 */

	private void initWrapper(final ICore<RunDefinition> core,
			final Map<File, IToolchainData<RunDefinition>> availableToolchains)
			throws InterruptedException, ExecutionException, TimeoutException {
		mLogger.info("Waiting for connection...");

		final Client<GeneratedMessageV3> client = mServer.waitForConnection(mListenTimeout, TimeUnit.SECONDS);
		final CompletableFuture<IInteractiveQueue<Object>> commonFuture =
				new CompletableFuture<IInteractiveQueue<Object>>();
		mProtoInterface = client.createInteractiveInterface(commonFuture);

		mConverterInitializer = new AbstractConverter.Initializer<>(mProtoInterface, mServer.getTypeRegistry());

		// TODO: register ControllerConverter with service provider and fined out, if services can be accessed
		final ControllerConverter converter = ControllerConverter.get(null);
		mInternalInterface = mConverterInitializer.getConvertedInteractiveInterface(converter);
		// TODO: fined out, if services can be accessed
		// services.getServiceInstance(TAConverterFactory.class);
		final Converter commonConverter = new Converter(mLogger);
		mCommonInterface = mConverterInitializer.getConvertedInteractiveInterface(commonConverter);

		commonFuture.complete(mCommonInterface);

		final List<File> tcFiles = new ArrayList<>(availableToolchains.keySet());

		while (true) {
			requestAndLoadSettings(core);
			requestAndLoadToolchain(core, tcFiles);

			final File[] inputFiles = requestInput();

			if (!mCommonInterface.request(Boolean.class).get())
				continue;

			execToolchain(core, inputFiles);
			if (client.hasIOExceptionOccurred()) {
				mLogger.info("Lost client connection before Toolchain was completed. Reinitializing.");
				return;
			}
			if (client.waitForQuit().isDone()) {
				mLogger.info("Client has quitted before Toolchain was completed. Reinitializing.");
				return;
			}
			mLogger.info("Toolchain finished");
			if (!mCommonInterface.request(Boolean.class).get())
				break;
		}

		mLogger.info("waiting for Client to Quit.");
		client.waitForQuit().get();
	}

	private void requestAndLoadToolchain(final ICore<RunDefinition> core, final List<File> tcFiles)
			throws InterruptedException, ExecutionException {
		final File tcFile = ChoiceRequest.get(tcFiles, File::getName).setLogger(mLogger).setTitle("Pick a Toolchain")
				.request(mCommonInterface);
		try {
			mToolchain = core.createToolchainData(tcFile.getAbsolutePath());
		} catch (final FileNotFoundException e1) {
			throw new IllegalStateException("Toolchain file not found at path: " + tcFile.getAbsolutePath());
		} catch (final SAXException | JAXBException e1) {
			throw new IllegalStateException(
					"Toolchain file at path " + tcFile.getAbsolutePath() + " was malformed: " + e1.getMessage());
		}
	}

	private void requestAndLoadSettings(final ICore<RunDefinition> core)
			throws InterruptedException, ExecutionException {
		// TODO: allow custom settings for plugins chosen from toolchain (see cli controller)
		final Path settingsFile = mCommonInterface
				.request(Path.class, RootPath.newInstance(mCla.getSettingsFilePath().toPath(), "Settings", ".epf"))
				.get();
		try {
			core.resetPreferences();
			core.loadPreferences(settingsFile.toFile().getAbsolutePath());
		} catch (final Exception e) {
			throw new IllegalStateException("could not load settings", e);
		}
	}

	private File[] requestInput() throws InterruptedException, ExecutionException {
		// final File inputFile = requestChoice(getAvailableInputFiles(), File::getName, "Pick an Input File");
		final File inputFile = requestFile(mCla.getInputDirPath().toPath(), "Input");

		mCommonInterface.send(inputFile);

		return new File[] { inputFile };
	}

	private File requestFile(final Path basePath, final String tag) throws InterruptedException, ExecutionException {
		final Path inputFile = mCommonInterface.request(Path.class, RootPath.newInstance(basePath, tag)).get();
		return inputFile.toFile();
	}

	private void execToolchain(final ICore<RunDefinition> core, final File[] inputFiles)
			throws InterruptedException, ExecutionException {
		final BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this, mLogger, inputFiles);
		tcj.schedule();
		tcj.join();
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
		// final ResultSummarizer summarizer = new ResultSummarizer(results);
		final ResultsWrapper wrapper = new ResultsWrapper();
		wrapper.results = results;

		mInternalInterface.send(wrapper);
	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// mLogger.fatal("RESULT: An exception occured during the execution of
		// Ultimate: " + description, ex);
		mLogger.fatal("RESULT: An exception occured during the execution of Ultimate: " + description);
		ex.printStackTrace();
		mCommonInterface.send(ex);
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	private Predicate<String> getPluginFilter(final ICore<RunDefinition> core, final File toolchainFileOrDir) {
		final ToolchainLocator locator = new ToolchainLocator(toolchainFileOrDir, core, mLogger);

		final Set<String> allowedIds = new HashSet<>();
		// all plugins in the toolchain are allowed
		allowedIds.addAll(locator.createFilterForAvailableTools());
		// the the core is allowed
		allowedIds.add(de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator.PLUGIN_ID);
		// the current controller (aka, we) are allowed
		allowedIds.add(getPluginID());
		// parser are allowed
		Arrays.stream(core.getRegisteredUltimatePlugins()).filter(a -> a instanceof ISource).map(a -> a.getPluginID())
				.forEach(allowedIds::add);

		// convert to lower case and build matching predicate
		final Set<String> lowerCaseIds = allowedIds.stream().map(a -> a.toLowerCase()).collect(Collectors.toSet());
		return a -> lowerCaseIds.contains(a.toLowerCase());
	}

	private Map<File, IToolchainData<RunDefinition>> getAvailableToolchains(final ICore<RunDefinition> core,
			final File workingDir) {
		final ToolchainLocator locator = new ToolchainLocator(workingDir, core, mLogger);

		final Map<File, IToolchainData<RunDefinition>> result = locator.locateToolchains();
		if (result.isEmpty()) {
			mLogger.fatal("There are no toolchains in directory" + workingDir);
		}
		return result;
	}

	@Override
	public void prerun(final IToolchainData<RunDefinition> tcData) {
		final IToolchainStorage storage = mToolchain.getStorage();

		mConverterInitializer.store(GeneratedMessageV3.class, storage);
	}

	public static class ResultsWrapper {
		public Map<String, List<IResult>> results;
	}
}
