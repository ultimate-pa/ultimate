/**
 * 
 */
package local.stalin.SMTInterface.preferences;

import java.io.File;

import local.stalin.SMTInterface.Activator;

import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * This class saves identifier, labels, default values and in some cases
 * (RadioGroupFieldEditor) choosable values for the preference page of this
 * plugin
 * 
 * @author dietsch
 * @version 0.0.3 
 * $LastChangedDate: 2008-02-09 23:14:39 +0100 (Sat, 09 Feb 2008) $
 * $LastChangedBy: dietsch 
 * $LastChangedRevision: 473 $
 */
public class PreferenceValues {

	
	public static ScopedPreferenceStore Preference = new ScopedPreferenceStore(new ConfigurationScope(),Activator.PLUGIN_ID);
	
	/*
	 * Names for the different preferences
	 */
	public static final String NAME_SAVESMTLIBFILES = "SAVESMTLIBFiles";
	public static final String NAME_SMTEXECUTABLE = "SMTExecutable";
	public static final String NAME_SMTPARAMETER = "SMTParameter";
	public static final String NAME_TEMPPATH = "tempPath";
	public static final String NAME_CUSTOMPARMS = "customParameters";
	
	public static final String NAME_SOLVERSELECTION = "solverSelection";
	
	public static final String NAME_Z3EXECUTABLE = "Z3Executable";
	public static final String NAME_YICESEXECUTABLE = "YicesExecutable";
	public static final String NAME_OPTION_PREFIX = "OptionPrefix";
	
	// z3
	public static final String NAME_Z3_DIMACS = "Dimacs";

	// yices
	public static final String NAME_YICES_CONSERVATIVE = "Conservative";
	
	/*
	 * (visible gui) labels for the different preferencess
	 */
	public static final String LABEL_SAVESMTLIBFILES = "Save SMTLIB files";
	public static final String LABEL_SOLVERSELECTION = "Choose a SMT Solver";
	public static final String LABEL_Z3 = "Microsoft Z3";
	public static final String LABEL_YICES = "Yices";
	public static final String LABEL_SMTEXECUTABLE = "Locate the SMT Executable";
	public static final String LABEL_SMTPARAMETER = "Generated Command Line";
	public static final String LABEL_TEMPPATH = "Store temporary files in ...";
	public static final String LABEL_CUSTOMPARMS = "Custom parameters";
	public static final String LABEL_OPTION_PREFIX = "Prefix for options";
	
	// z3
	//public static String LABEL_Z3_DIMACS = "use dimacs parser";
	
	// yices
	//public static String LABEL_YICES_CONSERVATIVE = "disable some optimizations";
	
	/*
	 * the actual parameter strings for the command line
	 */
	
	// z3
	
	//public static String PARAM_Z3_DIMACS = "/d";
	
	// yices
	//public static String PARAM_YICES_CONSERVATIVE = "-c";
	
	/*
	 * default values for the different preferences
	 */
	public static final boolean VALUE_SAVESMTLIBFILES = false;
	public static final String VALUE_SOLVERSELECTION_DEFAULT = "z3";
	public static final String VALUE_SMTEXECUTABLE_DEFAULT = "C:\\Program Files\\Microsoft Research\\Z3-2.9\\bin\\z3.exe";
	public static final String VALUE_SMTPARAMETER_DEFAULT = "";
	public static final String VALUE_TEMPPATH_DEFAULT = System
			.getProperty("java.io.tmpdir");
	public static final String VALUE_CUSTOMPARMS_DEFAULT = "";
	public static final String VALUE_OPTION_PREFIX_DEFAULT = File.separatorChar != '/' ? "/" : "-";
	
	// z3
	public static final boolean VALUE_Z3_DIMACS_DEFAULT = false;
	
	// yices
	public static final boolean VALUE_YICES_CONSERVATIVE_DEFAULT = false;

	/*
	 * usable Values
	 * 
	 */
	public static final String VALUE_OUTPUTTYPE_INTERNAL = "";

}
