package de.uni_freiburg.informatik.ultimate.core.coreplugin;

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

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
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
		s_PLUGIN_ID = Activator.s_PLUGIN_ID;
		s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
		s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	}

	private static final Logger s_Logger;
	private File m_Boogie;
	private Toolchain m_Toolchain;
	private PreludeProvider m_PreludeFile;
	private String m_Settings;

	private static final String s_PLUGIN_ID; 
	private static final String s_PLUGIN_NAME;

	/**
	 * Standard Constructor based on command-line parser providing the configuration
	 * 
	 * @param p instance of CommandLineParser 
	 * 
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 * @throws SAXException 
	 */
	public CommandlineController(CommandLineParser p)
			throws FileNotFoundException, JAXBException, SAXException {

		
		this.m_Toolchain = parseToolFile(p.getToolFile());
		this.m_Boogie = new File(p.getBoogieFile());
		if (!this.m_Boogie.exists() || !this.m_Boogie.canRead()) 
			throw new FileNotFoundException(p.getBoogieFile());
		
		// handle prelude file
		this.m_PreludeFile = new PreludeProvider(p.getPreludeFile());
		
	}

	/**
	 * parse the file with the specified toolchain
	 * 
	 * @param toolFile
	 * @return Toolchain
	 * @throws FileNotFoundException
	 * @throws JAXBException
	 * @throws SAXException 
	 */
	private Toolchain parseToolFile(String toolFile)
			throws FileNotFoundException, JAXBException, SAXException {
		if (toolFile == null || toolFile.equals("")) 
			throw new FileNotFoundException();
		return new Toolchain(toolFile);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java.lang.Object)
	 */
	public int init(Object param) {
		ICore core;
		if (!(param instanceof ICore)) {
			return -1;
		} else {
			core = (ICore) param;
		}
		
		try {
			ToolchainJob tcj = new ToolchainJob("Processing Toolchain", core, this, 
					this.m_Boogie, ToolchainJob.Chain_Mode.RUN_TOOLCHAIN, this.m_PreludeFile);
			tcj.schedule();
			// in non-GUI mode, we must wait until job has finished!
			tcj.join();
			
		} catch (InterruptedException e) {
			s_Logger.error("Exception in Toolchain", e);
			return -1;
		}		
		
		return IApplication.EXIT_OK;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectParser(java.util.Collection)
	 */
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


	public String getName() {
		return s_PLUGIN_NAME;
	}

	public String getPluginID() {
		return s_PLUGIN_ID;
	}


	@Override
	public Toolchain selectTools(List<ITool> tools) {
		return this.m_Toolchain;
	}

	
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

	@Override
	public String getLoadPrefName() {
		return m_Settings;
	}

	@Override
	public String getSavePrefName() {
		return null;
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
		System.out.println("RESULT: Ultimate could not prove your program: " 
				+ description);
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

}
