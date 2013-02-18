package local.stalin.core.coreplugin;

/**
 * A rudimentary parser for the Stalin command-line.
 * 
 * @author Christian Simon
 *
 */
public class CommandLineParser {
	
	private boolean interactive_mode = false;
	private boolean console_mode = false;
	private boolean exit_app = false;
	private String prelude_file = null;
	private String tool_file;
	private String boogie_file;
	private String m_Settings;
	
	private static final String s_PLUGIN_NAME="Command Line Parser";
	private static final String s_PLUGIN_ID="local.stalin.core.coreplugin.CommandLineParser";
	
	public CommandLineParser() {
				
	}
	
	public void printUsage() {
		System.err.println("Stalin Command Line Usage:");
		System.err.println("./Stalin --help | --console [<toolchain file> <boogie file> [--prelude <file>] [--settings <file>]] ");
		System.err.println("No argument will run Stalin in GUI mode.");
		System.err.println("Only the --console argument will run Stalin in interactive command-line mode.");
		System.err.println("Your parsed arguments were:");
		System.err.println("Prelude File:"+ prelude_file);
		System.err.println("Tool File:" + tool_file);
		System.err.println("Boogie File:" + boogie_file);
		System.err.println("Settings file:" + m_Settings);
		System.err.println("Console mode:" + String.valueOf(console_mode));
		System.err.println("Interactive mode:" + String.valueOf(interactive_mode));
		System.err.println("Exit Switch:" + String.valueOf(exit_app));
	}
	
	
	public void parse(String[] args) {
		int argc = args.length;
		
		// iterate over command lines
		for (int i=0; i<argc; i++) {
			
			if (args[i].compareTo("--help")==0) {
				exit_app = true;
				return;
			}
			
			if (args[i].compareTo("--console")==0) {
				console_mode = true;
				interactive_mode = true;
				continue;
			}
			
			if (console_mode == true && tool_file == null && prelude_file == null) {
				interactive_mode = false;
				// Now get the two remaining files
				try {
					tool_file = new String(args[i]);
					boogie_file = new String(args[++i]);
					continue;
				} catch (Exception e) {
					exit_app = true;
					return;
				}
			}
			// parse the optional prelude file
			if (console_mode == true && tool_file != null && boogie_file != null) {

			if (args[i].compareTo("--prelude")==0) {
				try {
					prelude_file = args[++i];	
					return;
				} catch (Exception e) {
					exit_app = true;
					return;
				}
			}
			if (args[i].compareTo("--settings")==0) {
				try {
					m_Settings = args[++i];
				} catch (Exception e) {
					exit_app = true;
					return;
				}
			}
			}
			
		}
		
	}
	
	public String getToolFile() {
		return tool_file;
	}
	
	public String getBoogieFile() {
		return boogie_file;
	}
	
	public String getPreludeFile() {
		return prelude_file;
	}
	
	public boolean getExitSwitch() {
		return exit_app;
	}
	
	public boolean getConsoleSwitch() {
		return console_mode;
	}
	
	public boolean getInteractiveSwitch() {
		return interactive_mode;
	}
	
	public String getName() {
		return s_PLUGIN_NAME;
	}

	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	public String getSettings() {
		return m_Settings;
	}
	
}
