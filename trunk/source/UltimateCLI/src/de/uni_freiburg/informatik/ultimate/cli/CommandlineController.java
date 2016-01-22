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

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.CommandLineParser;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.model.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Implements standard fallback controller for the command-line.
 * 
 * See CommandLineParser for valid command-line arguments.
 * 
 * @author Christian Ortolf
 * @author Christian Simon
 */
public class CommandlineController implements IController {

	static {
		sPLUGIN_ID = Activator.PLUGIN_ID;
		sPLUGIN_NAME = Activator.PLUGIN_NAME;
	}

	private Logger mLogger;
	private ToolchainData mToolchain;

	private static final String sPLUGIN_ID;
	private static final String sPLUGIN_NAME;

	/**
	 * parse the file with the specified toolchain
	 * 
	 * @param toolFile
	 * @return Toolchain
	 * @throws FileNotFoundException
	 * @throws JAXBException
	 * @throws SAXException
	 */
	private ToolchainData parseToolFile(String toolFile) throws FileNotFoundException, JAXBException, SAXException {
		if (toolFile == null || toolFile.equals(""))
			throw new FileNotFoundException();
		return new ToolchainData(toolFile);
	}

	public int init(ICore core, ILoggingService loggingService) {
		if (core == null) {
			return -1;
		}

		mLogger = loggingService.getLogger(sPLUGIN_ID);
		mLogger.info("Initializing CommandlineController...");

		CommandLineParser p = core.getCommandLineArguments();
		try {
			mToolchain = parseToolFile(p.getToolFile());
		} catch (FileNotFoundException e1) {
			mLogger.fatal("Toolchain file not found. Path was: " + p.getToolFile());
			return -1;
		} catch (JAXBException e1) {
			mLogger.fatal("Toolchain file maformed. Path was: " + p.getToolFile());
			mLogger.fatal(e1);
			return -1;
		} catch (SAXException e1) {
			mLogger.fatal("Toolchain file maformed. Path was: " + p.getToolFile());
			mLogger.fatal(e1);
			return -1;
		}
		ArrayList<File> inputFiles = new ArrayList<>();
		for (String inputfilePath : p.getInputFile()) {
			File inputFile = new File(inputfilePath);
			if (!inputFile.exists() || !inputFile.canRead()) {
				mLogger.fatal("Input file not found. Paths were: " + String.join(",", p.getInputFile()));
				return -1;
			}
			inputFiles.add(inputFile);
		}

		// handle prelude file
		PreludeProvider preludeFile = new PreludeProvider(p.getPreludeFile(), mLogger);

		try {
			BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this, mLogger,
					inputFiles.toArray(new File[0]), preludeFile);
			tcj.schedule();
			// in non-GUI mode, we must wait until job has finished!
			tcj.join();

		} catch (InterruptedException e) {
			mLogger.error("Exception in Toolchain", e);
			return -1;
		}

		return IApplication.EXIT_OK;
	}

	public ISource selectParser(Collection<ISource> parser) {
		Object[] parsers = parser.toArray();

		System.out.println("Index\tParser ID");

		for (int i = 0; i < parsers.length; i++) {
			System.out.println(String.valueOf(i) + "\t" + ((ISource) parsers[i]).getPluginID());
		}

		System.out.println("Please choose a parser manually:");
		InputStreamReader inp = new InputStreamReader(System.in);
		BufferedReader br = new BufferedReader(inp);

		while (true) {
			try {
				String str = br.readLine();
				int selection = Integer.valueOf(str);
				if (selection < parsers.length) {
					return ((ISource) parsers[selection]);
				} else {
					System.err.println("Please make a valid selection.");
				}
			} catch (NumberFormatException e) {
				System.err.println("Please make a valid selection.");
			} catch (IOException e) {
				System.err.println("There was problem opening your console.");
			}
		}
	}

	public String getPluginName() {
		return sPLUGIN_NAME;
	}

	public String getPluginID() {
		return sPLUGIN_ID;
	}

	@Override
	public ToolchainData selectTools(List<ITool> tools) {
		return mToolchain;
	}

	@Override
	public List<String> selectModel(List<String> modelNames) {
		ArrayList<String> return_list = new ArrayList<String>();

		System.out.println("Index\tModel ID");

		for (int i = 0; i < modelNames.size(); i++) {
			System.out.println(String.valueOf(i) + "\t" + modelNames.get(i));
		}

		InputStreamReader inp = new InputStreamReader(System.in);
		BufferedReader br = new BufferedReader(inp);

		while (true) {

			try {
				String str = br.readLine();
				String[] tokens = str.trim().split(" ");

				for (String s : tokens) {
					int foo = Integer.valueOf(s);
					if (foo > modelNames.size()) {
						System.err.println("Please make a valid selection!");
						continue;
					} else {
						return_list.add(modelNames.get(foo));
					}
				}
			} catch (NumberFormatException e) {
				System.err.println("Please make a valid selection.");
			} catch (IOException e) {
				System.err.println("Console couldn't be openend.");
			}
		}
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {
		System.out.println("RESULT: Ultimate proved your program to be incorrect!");
	}

	@Override
	public void displayToolchainResultProgramCorrect() {
		System.out.println("RESULT: Ultimate proved your program to be correct!");
	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {
		System.out.println("RESULT: Ultimate could not prove your program: " + description);
	}

	@Override
	public void displayException(String description, Throwable ex) {

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}
}
