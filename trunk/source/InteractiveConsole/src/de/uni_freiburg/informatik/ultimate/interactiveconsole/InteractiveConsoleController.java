package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import java_cup.runtime.ComplexSymbolFactory;

import org.apache.log4j.Logger;
import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.ILoggingService;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchain;

/**
 * Controller for the interactive console mode of Ultimate which is started when
 * calling Ultimate with "--console" argument.
 * 
 * @author Christian Simon
 * 
 */
public class InteractiveConsoleController implements IController {

	public static final String s_PLUGIN_ID = "de.uni_freiburg.informatik.ultimate.InteractiveConsoleController";
	public static final String s_PLUGIN_NAME = "Interactive Console";

	public boolean m_CancelRequest = false;

	private IToolchain m_Core;
	private ToolchainData m_Chain = null;
	private PreludeProvider m_PreludeFile;
	private Logger mLogger;

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

	@Override
	public ToolchainData selectTools(List<ITool> tools) {
		return this.m_Chain;
	}

	@Override
	public String getPluginName() {
		return InteractiveConsoleController.s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return InteractiveConsoleController.s_PLUGIN_ID;
	}

	@Override
	public int init(ICore core, ILoggingService loggingService) {
		if (core == null) {
			return -1;
		}

		mLogger = loggingService.getControllerLogger();

		System.err.println("Welcome to Ultimate's Interactive Console.");
		System.err.println("Type 'help' for further assistance.");
		try {
			interactiveConsole();
		} catch (IOException e) {
			System.err.println("Couldn't open the console.");
		}

		core.getRegisteredUltimatePlugins();

		return IApplication.EXIT_OK;

	}

	/**
	 * actual main function opening std.in, parsing commands, and executing them
	 * 
	 * @throws IOException
	 */
	private void interactiveConsole() throws IOException {
		InputStreamReader inp = new InputStreamReader(System.in);
		BufferedReader br = new BufferedReader(inp);

		while (true) {
			System.out.println("Enter your Ultimate command : ");

			String str = br.readLine();

			ConsoleLexer lexer = new ConsoleLexer(new StringReader(str));
			lexer.setSymbolFactory(new ComplexSymbolFactory());
			ConsoleParser parser = new ConsoleParser(lexer);
			Stmt s = null;
			try {
				s = (Stmt) parser.parse().value;
			} catch (SyntaxException e) {
				System.err.println("Parse error! Check the syntax of your commands");
			} catch (RuntimeException e) {
				throw e;
			} catch (Exception e) {
				throw new RuntimeException(e);
			}
			if (s != null) {
				s.setController(this);
				s.execute();
			}

			if (this.m_CancelRequest) {
				break;
			}
		}
	}

	public void setToolchain(ToolchainData tc) {
		this.m_Chain = tc;
	}

	public void setPrelude(PreludeProvider pp) {
		this.m_PreludeFile = pp;
	}

	public PreludeProvider getPrelude() {
		return this.m_PreludeFile;
	}

	public IToolchain getCore() {
		return this.m_Core;
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public void displayToolchainResultProgramCorrect() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public void displayException(String description, Throwable ex) {
		// TODO Auto-generated method stub

	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

	public Logger getLogger() {
		return mLogger;
	}

}
