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
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Implements standard fallback controller for the command-line.
 * 
 * See CommandLineParser for valid command-line arguments.
 * 
 * @author Christian Ortolf, Christian Simon
 */
public class CommandlineController implements IController {

	static {
		sPLUGIN_ID = Activator.s_PLUGIN_ID;
		sPLUGIN_NAME = Activator.s_PLUGIN_NAME;
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
		File bplFile = new File(p.getBoogieFile());
		if (!bplFile.exists() || !bplFile.canRead()) {
			mLogger.fatal("Input file not found. Path was: " + p.getBoogieFile());
			return -1;
		}

		// handle prelude file
		PreludeProvider preludeFile = new PreludeProvider(p.getPreludeFile(), mLogger);

		try {
			BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", core, this,
					BasicToolchainJob.ChainMode.RUN_TOOLCHAIN, bplFile, preludeFile, mLogger);
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
