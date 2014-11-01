package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_ExtSolverFlag,
						DEF_ExtSolverFlag, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_ExtSolverCommand,
						DEF_ExtSolverCommand, PreferenceType.String),
				new UltimatePreferenceItem<CodeBlockSize>(LABEL_CodeBlockSize,
						DEF_CodeBlockSize, PreferenceType.Combo, CodeBlockSize.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_RemoveGotoEdges,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_Simplify,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_CNF,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_DumpToFile,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_Path,
						DEF_Path, PreferenceType.Directory),
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "RCFG Builder";
	}
	
	
	/*
	 * new preferences that belong to the RCFG Builder 
	 */
	public static final String LABEL_ExtSolverFlag = "Use external solver instead of SMTInterpol";
	public static final boolean DEF_ExtSolverFlag = true;
	public static final String LABEL_ExtSolverCommand = "Command for external solver";
	public static final String DEF_ExtSolverCommand = "z3 SMTLIB2_COMPLIANT=true -memory:1024 -smt2 -in -t:12000";
	public static final String LABEL_CodeBlockSize = "Size of a code block";
	public enum CodeBlockSize { SingleStatement, SequenceOfStatements, LoopFreeBlock };
	public static final CodeBlockSize DEF_CodeBlockSize = CodeBlockSize.LoopFreeBlock;
	public static final String LABEL_Simplify = "Simplify code blocks";
	public static final String LABEL_CNF = "Convert code blocks to CNF";
	public static final String LABEL_RemoveGotoEdges = "Remove goto edges from RCFG";
	public static final String LABEL_DumpToFile = "Dump SMT script to file";
	public static final String LABEL_Path = "To the following directory";
	public static final String DEF_Path = "";
	
}