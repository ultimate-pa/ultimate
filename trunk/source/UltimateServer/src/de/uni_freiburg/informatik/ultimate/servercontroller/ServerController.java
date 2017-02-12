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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultSummarizer;
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
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientCrazyException;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.TAConverter;
import de.uni_freiburg.informatik.ultimate.server.Client;
import de.uni_freiburg.informatik.ultimate.server.IInteractiveServer;
import de.uni_freiburg.informatik.ultimate.servercontroller.converter.ControllerConverter;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.Choice;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Controller.File.Request;
import de.uni_freiburg.informatik.ultimate.servercontroller.protoserver.ProtoServer;
import de.uni_freiburg.informatik.ultimate.servercontroller.util.CommandLineArgs;
import de.uni_freiburg.informatik.ultimate.servercontroller.util.RcpUtils;

/**
 * The {@link ServerController} class provides a user interface for Clients that
 * can connect via TCP.
 *
 * @author Julian Jarecki
 */
public class ServerController implements IController<RunDefinition> {

	private ILogger mLogger;
	private IInteractiveServer<GeneratedMessageV3> mServer;
	private IToolchainData<RunDefinition> mToolchain;

	private IInteractive<Object> mInternalInterface;
	private IInteractive<GeneratedMessageV3> mProtoInterface;

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

		final CommandLineArgs cla;
		try {
			cla = CommandLineArgs.parse(args);
		} catch (org.apache.commons.cli.ParseException e) {
			mLogger.error(e.getMessage());
			mLogger.error("Arguments were \"" + String.join(" ", args) + "\"");
			mLogger.error("--");
			return -1;
		}

		mServer = new ProtoServer(mLogger, cla.getPort());

		// final File workingDir = RcpUtils.getWorkingDirectory();
		final Map<File, IToolchainData<RunDefinition>> availableToolchains = getAvailableToolchains(core,
				cla.getToolchainDirPath());
		if (availableToolchains.isEmpty()) {
			return -1;
		}

		final File[] availableSettingsFiles = cla.getSettingsFilePath()
				.listFiles((file, name) -> name.endsWith(".epf"));
		if (availableSettingsFiles.length == 0) {
			mLogger.error("No Settings files found in " + cla.getSettingsFilePath().getAbsolutePath());
			return -1;
		}

		final File[] availableInputFiles = cla.getInputDirPath().listFiles(f -> f.isFile());
		if (availableInputFiles.length == 0) {
			mLogger.error("No Input files found in " + cla.getInputDirPath().getAbsolutePath());
			return -1;
		}

		mLogger.debug("Starting Server on Port " + cla.getPort());
		mServer.start();

		try {
			initWrapper(core, availableToolchains, availableSettingsFiles, availableInputFiles);
		} catch (InterruptedException | ExecutionException | TimeoutException e) {
			mLogger.fatal(e);
			return -1;
		} finally {
			mLogger.info("Interactive Controller terminated - shutting down Server.");
			mServer.stop();
		}

		return IApplication.EXIT_OK;
	}

	private void initWrapper(final ICore<RunDefinition> core,
			Map<File, IToolchainData<RunDefinition>> availableToolchains, final File[] availableSettingsFiles,
			final File[] availableInputFiles) throws InterruptedException, ExecutionException, TimeoutException {
		mLogger.debug("Waiting for connection...");

		final Client<GeneratedMessageV3> client = mServer.waitForConnection();
		mProtoInterface = client.createInteractiveInterface();

		ControllerConverter converter = ControllerConverter.get();
		converter.initInterface(mProtoInterface, mServer.getTypeRegistry());
		mInternalInterface = converter.getInterface();

		// If we wanted files directly - but thats not supported by Ultimate
		// Core :(
		// mServer.getTypeRegistry().register(Controller.File.class);
		// mServer.getTypeRegistry().register(Controller.File.Request.class);

		// mInternalInterface.send(new IllegalStateException("Funny test
		// exception! :D"));

		final List<File> tcFiles = new ArrayList<>(availableToolchains.keySet());

		mServer.getTypeRegistry().register(Controller.Choice.Request.class);
		mServer.getTypeRegistry().register(Controller.Choice.class);

		final File settingsFile = requestChoice(availableSettingsFiles, File::getName);
		try {
			core.loadPreferences(settingsFile.getAbsolutePath());
		} catch (Exception e) {
			throw new IllegalStateException("could not load settings", e);
		}
		// TODO: allow custom settings for plugins chosen from toolchain (see
		// cli controller)

		final File tcFile = requestChoice(tcFiles, File::getName);
		try {
			mToolchain = core.createToolchainData(tcFile.getAbsolutePath());
		} catch (final FileNotFoundException e1) {
			throw new IllegalStateException("Toolchain file not found at path: " + tcFile.getAbsolutePath());
		} catch (final SAXException | JAXBException e1) {
			throw new IllegalStateException(
					"Toolchain file at path " + tcFile.getAbsolutePath() + " was malformed: " + e1.getMessage());
		}

		final IToolchainStorage storage = mToolchain.getStorage();

		TAConverter taConverter = new TAConverter(storage);
		converter.initInterface(mProtoInterface, mServer.getTypeRegistry());

		final File inputFile = requestChoice(availableInputFiles, File::getName);

		final File[] inputFiles = new File[] { inputFile };

		final BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this, mLogger, inputFiles);
		tcj.schedule();
		tcj.join();
	}

	private <T> T requestChoice(T[] choices, Function<T, String> toString)
			throws InterruptedException, ExecutionException {
		return requestChoice(Arrays.asList(choices), toString);
	}

	private <T> T requestChoice(List<T> choices, Function<T, String> toString)
			throws InterruptedException, ExecutionException {
		Controller.Choice.Request.Builder tcBuilder = Controller.Choice.Request.newBuilder();
		choices.stream().map(toString).forEach(tcBuilder::addChoice);
		CompletableFuture<Choice> choice = mProtoInterface.request(Controller.Choice.class, tcBuilder.build());

		int choiceid = -1;

		choiceid = choice.get().getIndex();
		if (choiceid < 0 || choiceid > choices.size()) {
			throw new ClientCrazyException(String.format("Choice index from Client not within bounds: %1$d", choiceid));
		}
		final T result = choices.get(choiceid);
		mLogger.info("Client has chosen " + toString.apply(result));
		return result;
	}

	/**
	 * Request File contents form Client
	 * 
	 * @param ext
	 *            hint file extension to client.
	 * @return file content as String.
	 */
	private String requestFileContent(final String ext) throws InterruptedException, ExecutionException {
		Request tcRequest = Controller.File.Request.newBuilder().setExt(ext).build();
		CompletableFuture<Controller.File> tcFuture = mProtoInterface.request(Controller.File.class, tcRequest);

		return tcFuture.get().getContent();
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

		mInternalInterface.send(summarizer);
	}

	@Override
	public void displayException(final IToolchainData<RunDefinition> toolchain, final String description,
			final Throwable ex) {
		// mLogger.fatal("RESULT: An exception occured during the execution of
		// Ultimate: " + description, ex);
		mLogger.fatal("RESULT: An exception occured during the execution of Ultimate: " + description);
		mInternalInterface.send(ex);
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

		Map<File, IToolchainData<RunDefinition>> result = locator.locateToolchains();
		if (result.isEmpty()) {
			mLogger.fatal("There are no toolchains in directory" + workingDir);
		}
		return result;
	}

	public class FatalControllerException extends Exception {
	}
}
