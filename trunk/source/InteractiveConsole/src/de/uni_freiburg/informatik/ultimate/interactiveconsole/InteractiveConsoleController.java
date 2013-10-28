package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import java_cup.runtime.ComplexSymbolFactory;

import org.eclipse.equinox.app.IApplication;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Controller for the interactive console mode of Ultimate 
 * which is started when calling Ultimate with "--console" argument.
 * 
 * @author Christian Simon
 *
 */
public class InteractiveConsoleController implements IController {

	public static final String s_PLUGIN_ID = "de.uni_freiburg.informatik.ultimate.InteractiveConsoleController";
	public static final String s_PLUGIN_NAME = "Interactive Console";
	
	public boolean m_CancelRequest = false;
	
	private ICore m_Core;
	private List<ITool> m_Tools;
	private List<String> m_Models;
	private Toolchain m_Chain = null;
	private PreludeProvider m_PreludeFile;
	private String m_Filename;
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectModel(java.util.List)
	 */
	@Override
	public List<String> selectModel(List<String> modelNames) {
		ArrayList<String> return_list = new ArrayList<String>();
		
		System.out.println("Index\tModel ID");

		for (int i=0; i<modelNames.size(); i++) {
			System.out.println(String.valueOf(i)+"\t"+modelNames.get(i));
		}
		
		InputStreamReader  inp = new InputStreamReader(System.in);
		BufferedReader br = new BufferedReader(inp);

		while (true) {
		
			try {
				String str = br.readLine();
				String [] tokens = str.trim().split(" ");
				
				for (String s: tokens) {
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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectParser(java.util.Collection)
	 */
	@Override
	public ISource selectParser(Collection<ISource> parser) {
		Object[] parsers = parser.toArray();
		
		System.out.println("Index\tParser ID");

		for (int i=0; i<parsers.length; i++) {
			System.out.println(String.valueOf(i)+"\t"+((ISource) parsers[i]).getPluginID());
		}
		
		System.out.println("Please choose a parser manually:");
		InputStreamReader  inp = new InputStreamReader(System.in);
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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectTools(java.util.List)
	 */
	@Override
	public Toolchain selectTools(List<ITool> tools) {
		return this.m_Chain;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return InteractiveConsoleController.s_PLUGIN_NAME;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID()
	 */
	@Override
	public String getPluginID() {
		return InteractiveConsoleController.s_PLUGIN_ID;
	}
	

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	@Override
	public int init(Object controlledCore) {
		
		if (!(controlledCore instanceof ICore)) {
			return -1;
		} else {
			this.m_Core = (ICore) controlledCore;
		}
		
		this.m_Tools = UltimateServices.getInstance().getActiveTools();
		
		// this is subject to change during the run of a toolchain
		// so, don't forget to update it frequently!
		this.m_Models = UltimateServices.getInstance().getAllModels();

		
		System.err.println("Welcome to Ultimate's Interactive Console.");
		System.err.println("Type 'help' for further assistance.");
		try {
			interactiveConsole();
		} catch (IOException e) {
			System.err.println("Couldn't open the console.");
		}
		
		return IApplication.EXIT_OK;

	}
	
	/**
	 * actual main function opening std.in, parsing commands, and executing them
	 * 
	 * @throws IOException
	 */
	private void interactiveConsole() throws IOException {
		InputStreamReader  inp = new InputStreamReader(System.in);
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

	public List<ITool> getTools() {
		return m_Tools;
	}

	public List<String> getModelList() {
		return this.m_Models;
	}

	public void updateModelList() {
		this.m_Models = UltimateServices.getInstance().getAllModels();
	}
	
	public void setToolchain(Toolchain tc) {
		this.m_Chain = tc;
	}
	
	public void setPrelude(PreludeProvider pp) {
		this.m_PreludeFile = pp;
	}

	public PreludeProvider getPrelude() {
		return this.m_PreludeFile;
	}
	
	public ICore getCore() {
		return this.m_Core;
	}

	@Override
	public String getLoadPrefName() {
		return m_Filename;
	}

	@Override
	public String getSavePrefName() {
		// TODO Auto-generated method stub
		return null;
	}

	public void setPrefFile(String filename) {
		m_Filename = filename;
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

	
}
