/*
 * Copyright (C) 2015 Christian Ortolf
 * Copyright (C) 2015 Christian Simon
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE command line interface.
 *
 * The ULTIMATE command line interface is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE command line interface is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE command line interface. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE command line interface, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE command line interface grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cli;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import javax.xml.bind.JAXBException;

import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Implements standard fallback controller for the command-line.
 *
 * See CommandLineParser for valid command-line arguments.
 *
 * @author Christian Ortolf
 * @author Christian Simon
 */
public class CommandlineController implements IController<ToolchainListType> {

	private ILogger mLogger;
	private IToolchainData<ToolchainListType> mToolchain;

	/**
	 * parse the file with the specified toolchain
	 *
	 * @param toolFile
	 * @return Toolchain
	 * @throws FileNotFoundException
	 * @throws JAXBException
	 * @throws SAXException
	 */
	private IToolchainData<ToolchainListType> parseToolFile(final String toolFile, final ICore<ToolchainListType> core)
			throws FileNotFoundException, JAXBException, SAXException {
		if (toolFile == null || toolFile.equals("")) {
			throw new FileNotFoundException();
		}
		return core.createToolchainData(toolFile);
	}

	@Override
	public int init(final ICore<ToolchainListType> core) {
		if (core == null) {
			return -1;
		}

		mLogger = core.getCoreLoggingService().getLogger(Activator.PLUGIN_ID);
		mLogger.info("Initializing CommandlineController...");

		// parse command line parameters and select ultimate mode
		final CommandLineParser cmdParser = new CommandLineParser();
		cmdParser.parse(Platform.getCommandLineArgs());

		// determine Ultimate's mode
		if (cmdParser.getExitSwitch()) {
			cmdParser.printUsage();
			return IApplication.EXIT_OK;
		}

		final String settingsfile = cmdParser.getSettings();
		if (settingsfile != null) {
			core.loadPreferences(settingsfile);
		} else {
			mLogger.info("No settings file supplied");
		}

		try {
			mToolchain = parseToolFile(cmdParser.getToolFile(), core);
		} catch (final FileNotFoundException e1) {
			mLogger.fatal("Toolchain file not found. Path was: " + cmdParser.getToolFile());
			return -1;
		} catch (final JAXBException e1) {
			mLogger.fatal("Toolchain file maformed. Path was: " + cmdParser.getToolFile());
			mLogger.fatal(e1);
			return -1;
		} catch (final SAXException e1) {
			mLogger.fatal("Toolchain file maformed. Path was: " + cmdParser.getToolFile());
			mLogger.fatal(e1);
			return -1;
		}
		final ArrayList<File> inputFiles = new ArrayList<>();
		for (final String inputfilePath : cmdParser.getInputFile()) {
			final File inputFile = new File(inputfilePath);
			if (!inputFile.exists() || !inputFile.canRead()) {
				mLogger.fatal("Input file not found. Paths were: " + String.join(",", cmdParser.getInputFile()));
				return -1;
			}
			inputFiles.add(inputFile);
		}

		try {
			final BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this, mLogger,
					inputFiles.toArray(new File[0]));
			tcj.schedule();
			// in non-GUI mode, we must wait until job has finished!
			tcj.join();

		} catch (final InterruptedException e) {
			mLogger.error("Exception in Toolchain", e);
			return -1;
		}

		return IApplication.EXIT_OK;
	}

	@Override
	public ISource selectParser(final Collection<ISource> parser) {
		final Object[] parsers = parser.toArray();

		System.out.println("Index\tParser ID");

		for (int i = 0; i < parsers.length; i++) {
			System.out.println(String.valueOf(i) + "\t" + ((ISource) parsers[i]).getPluginID());
		}

		System.out.println("Please choose a parser manually:");
		final InputStreamReader inp = new InputStreamReader(System.in);
		final BufferedReader br = new BufferedReader(inp);

		while (true) {
			try {
				final String str = br.readLine();
				final int selection = Integer.valueOf(str);
				if (selection < parsers.length) {
					return ((ISource) parsers[selection]);
				} else {
					System.err.println("Please make a valid selection.");
				}
			} catch (final NumberFormatException e) {
				System.err.println("Please make a valid selection.");
			} catch (final IOException e) {
				System.err.println("There was problem opening your console.");
			}
		}
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
	public IToolchainData<ToolchainListType> selectTools(final List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(final List<String> modelNames) {
		final ArrayList<String> return_list = new ArrayList<String>();

		System.out.println("Index\tModel ID");

		for (int i = 0; i < modelNames.size(); i++) {
			System.out.println(String.valueOf(i) + "\t" + modelNames.get(i));
		}

		final InputStreamReader inp = new InputStreamReader(System.in);
		final BufferedReader br = new BufferedReader(inp);

		while (true) {

			try {
				final String str = br.readLine();
				final String[] tokens = str.trim().split(" ");

				for (final String s : tokens) {
					final int foo = Integer.valueOf(s);
					if (foo > modelNames.size()) {
						System.err.println("Please make a valid selection!");
						continue;
					} else {
						return_list.add(modelNames.get(foo));
					}
				}
			} catch (final NumberFormatException e) {
				System.err.println("Please make a valid selection.");
			} catch (final IOException e) {
				System.err.println("Console couldn't be openend.");
			}
		}
	}

	@Override
	public void displayToolchainResults(final IToolchainData<ToolchainListType> toolchain,
			final Map<String, List<IResult>> results) {
		// TODO Auto-generated method stub

	}

	@Override
	public void displayException(final IToolchainData<ToolchainListType> toolchain, final String description,
			final Throwable ex) {
		// TODO Auto-generated method stub

	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

}
