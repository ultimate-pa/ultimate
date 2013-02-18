package local.stalin.SMTInterface.preferences;

import java.util.HashMap;

public class PreferenceCommandLineOptions {
	
	private String m_Parameters;
	private String m_Customparameters;
	private String m_OptionPrefix;
	private HashMap<String,CommandLineOption> m_TheOptions;
	
	public PreferenceCommandLineOptions()
	{
		this.m_TheOptions = new HashMap<String,CommandLineOption>();
		this.m_Customparameters = "";
	}
	
	protected void addOption(String optionName, CommandLineOption newoption)
	{
		this.m_TheOptions.put(optionName,newoption);
	}
	
	public HashMap<String,CommandLineOption> getAllOptions()
	{
		return this.m_TheOptions;		
	}
	
	public CommandLineOption getOptionByName(String name)
	{
		return this.m_TheOptions.get(name);
	}
	
	private void values2String()
	{
		StringBuilder sb = new StringBuilder();
		String delim = "";
		for (String optionName : this.m_TheOptions.keySet())
		{	
			CommandLineOption theOption = this.m_TheOptions.get(optionName);
			String optionString = theOption.toString(); 
			if (!optionString.equals("")) 
			{
				sb.append(delim).append(m_OptionPrefix).append(optionString);
				delim = " ";
			}
		}
		m_Parameters = sb.toString();
	}
	
	public String getParameters()
	{
		values2String();
		return this.m_Customparameters + " " + this.m_Parameters;
	}
	
	public static PreferenceCommandLineOptions getZ3Options()
	{
		PreferenceCommandLineOptions z3options = new PreferenceCommandLineOptions();
		z3options.addOption("z3dimacs",z3options.new BoolCLO("d","use dimacs parser",false));
		z3options.addOption("simplifyin",z3options.new BoolCLO("s","Simplify input Format",false));
		z3options.addOption("smtin",z3options.new BoolCLO("smt","SMT input format",false));
		z3options.addOption("z3natin",z3options.new BoolCLO("z3","Z3 native input format",false));
		z3options.addOption("stdin",z3options.new BoolCLO("in","standard input",false));
		z3options.addOption("simplinterac",z3options.new BoolCLO("si","interactive mode, Simplify input",false));
		
		z3options.addOption("z3help",z3options.new BoolCLO("h","print help page",false));
		z3options.addOption("z3version",z3options.new BoolCLO("version","prints Z3 Version",false));
		z3options.addOption("z3verbosity",z3options.new IntCLO("v:","Verbosity Level",0));
		z3options.addOption("warning",z3options.new BoolCLO("nw","disable warning messages",false));
		z3options.addOption("conf",z3options.new BoolCLO("ini:","config file",false));
		z3options.addOption("dispini",z3options.new BoolCLO("ini?","display all INI file params",false));
		
		z3options.addOption("z3timeout",z3options.new IntCLO("T:","set timeout in seconds",0));
		z3options.addOption("softimeout",z3options.new IntCLO("t:","set soft timeout in seconds",0));
		z3options.addOption("vmemlimit",z3options.new IntCLO("memory:","set limit for virtual memory",0));
		
		z3options.addOption("z3stats",z3options.new BoolCLO("st","display statistics",false));
		z3options.addOption("model",z3options.new BoolCLO("m","display model",false));
		
		//z3options.addOption("counterex",z3options.new IntCLO("/cex:","set max number of counterexamples when using Simplify",0));
		z3options.addOption("counterex",z3options.new IntCLO("cex:","max # counterex",0));
		z3options.addOption("atlabels",z3options.new BoolCLO("@","only use '@' labels",false));
		//z3options.addOption("atlabels",z3options.new BoolCLO("@","only use label with '@' when building mult. counterexamples",false));
		
		
		z3options.addOption("relevancy",z3options.new IntCLO("r:","level of relevancy heuristics",3));
		z3options.addOption("looppat",z3options.new BoolCLO("lp","do not block loop patterns",false));
		z3options.addOption("splitfreq",z3options.new IntCLO("rd:","random case-split frequency",2));
		z3options.addOption("z3randomseed",z3options.new IntCLO("rs:","random seed",0));
				
		return z3options;
	}
	
	public static PreferenceCommandLineOptions getYicesOptions()
	{
		PreferenceCommandLineOptions yicesoptions = new PreferenceCommandLineOptions();
		yicesoptions.addOption("help",yicesoptions.new BoolCLO("?","print help message",false));
		
		yicesoptions.addOption("conservative",yicesoptions.new BoolCLO("c","disable some optimizations",false));
		yicesoptions.addOption("evidence",yicesoptions.new BoolCLO("e","display the model if satisfiable",false));
		yicesoptions.addOption("ystats",yicesoptions.new BoolCLO("st","display statistics",false));
		yicesoptions.addOption("typecheck",yicesoptions.new BoolCLO("tc","Enable type checker",false));
		
		yicesoptions.addOption("maxsat",yicesoptions.new BoolCLO("ms","compute maximal satisfying assignment",false));
		yicesoptions.addOption("maxweight",yicesoptions.new IntCLO("mw ","max-weight of dimacs file with MaxWalkSat",1000000));
		
		yicesoptions.addOption("ydimacs",yicesoptions.new BoolCLO("d","use dimacs parser",false));
		yicesoptions.addOption("yinteractive",yicesoptions.new BoolCLO("i","Enable interactive mode",false));
		yicesoptions.addOption("yrandomseed",yicesoptions.new IntCLO("rds ","random seed",0));
		yicesoptions.addOption("smtlib",yicesoptions.new BoolCLO("smt","use SMT-LIB parser",false));
		yicesoptions.addOption("tickfreq",yicesoptions.new IntCLO("tf ","Set tick frequency",0));
		yicesoptions.addOption("ytimeout",yicesoptions.new IntCLO("tm ","Set timeout in seconds",0));
		yicesoptions.addOption("yverbosity",yicesoptions.new IntCLO("v ","Set verbosity level",0));
		yicesoptions.addOption("yversion",yicesoptions.new BoolCLO("V","Display version number",false));
		
		yicesoptions.addOption("maxinstances",yicesoptions.new IntCLO("mi ","max # of quantifier instantiations",50000));
		yicesoptions.addOption("maxpatterns",yicesoptions.new IntCLO("mp ","max # of patterns per quantifiers",10));
		yicesoptions.addOption("noquantelem",yicesoptions.new BoolCLO("nqe","Disable quantifier elemination",false));
		yicesoptions.addOption("patterncreation",yicesoptions.new IntCLO("pc ","How conservative the pattern/trigger generation heuristic should be",1));
		yicesoptions.addOption("quantelem",yicesoptions.new BoolCLO("qe","Enable quantifier elemination",true));
		
		return yicesoptions;
	}
	
	protected void setCustomparameters(String customparameters) {
		this.m_Customparameters = customparameters;
	}

	protected void setOptionPrefix(String optionPrefix) {
		this.m_OptionPrefix = optionPrefix;
	}


	abstract class CommandLineOption
	{
		protected String m_String;	
		protected String m_Label;
		
		protected CommandLineOption(String theString, String label)
		{
			this.m_String = theString;
			this.m_Label = label;
		}
		
		public String getLabel()
		{
			return this.m_Label;
		}
		
		public String toString()
		{
			return this.m_String;
		}
	}
	
	class BoolCLO extends CommandLineOption
	{
		private boolean m_Active;
		protected BoolCLO(String theString, String label, boolean defaultvalue)
		{
			super(theString,label);
			this.m_Active = defaultvalue;
		}
		
		public String toString()
		{
			if (this.m_Active)
			{
				return this.m_String;
			}			
			return "";			
		}
		
		public boolean getDefaultValue()
		{
			return this.m_Active;
		}
		
		
		public void setCurrentValue(boolean newState)
		{
			this.m_Active = newState;
		}
	}
	
	class IntCLO extends CommandLineOption
	{
		private int m_Value;
		private int m_DefaultValue;
		protected IntCLO(String theString, String label, int defaultvalue)
		{
			super(theString,label);
			this.m_DefaultValue = defaultvalue;
			this.m_Value = defaultvalue;
		}
		
		public String toString()
		{
			if (this.m_Value != this.m_DefaultValue)
			{
				return this.m_String + this.m_Value;
			}			
			return "";			
		}
		
		public int getDefaultValue()
		{
			return this.m_Value;
		}
				
		public void setCurrentValue(int newVal)
		{
			this.m_Value = newVal;
		}
	}
}
