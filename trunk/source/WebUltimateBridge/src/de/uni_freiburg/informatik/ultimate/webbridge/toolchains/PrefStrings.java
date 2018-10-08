package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

/**
 * Class to store the Strings used by the web interface to build the correct .epf files. There Strings are exactly those
 * which occur in the UltimatePreferenceInitializer file, but where the blank space is quoted with backslash. In the
 * current architecture we do not want that the web interface depends on all plugins therefore we have to copy all these
 * strings.
 *
 * @author Matthias Heizmann
 *
 */
public class PrefStrings {

	/** Names of tools **/

	public static final String SYNTAXCHECKER = "de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker";
	public static final String CACSL2BOOGIETRANSLATOR =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator";
	public static final String BOOGIE_PREPROCESSOR = "de.uni_freiburg.informatik.ultimate.boogie.preprocessor";
	public static final String BOOGIE_PROCEDURE_INLINER = "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner";
	public static final String RCFGBUILDER = "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder";
	public static final String BUCHIAUTOMIZER =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer";
	public static final String AUTOMATASCRIPTINTERPRETER =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter";
	public static final String BLOCKENCODING = "de.uni_freiburg.informatik.ultimate.plugins.blockencoding";
	public static final String TRACE_ABSTRACTION_CONCURRENT =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent";
	public static final String LASSO_RANKER = "de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker";
	public static final String TRACE_ABSTRACTION =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction";
	public static final String LTL2AUT = "de.uni_freiburg.informatik.ultimate.ltl2aut";
	public static final String BUCHIPROGRAMPRODUCT = "de.uni_freiburg.informatik.ultimate.buchiprogramproduct";
	public static final String CODECHECK = "de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck";

	/** Settings strings **/

	public static final String CACSL_LABEL_StartFunction =
			CACSL2BOOGIETRANSLATOR + "/Checked\\ method.\\ Library\\ mode\\ if\\ empty.";
	public static final String CACSL_LABEL_TRANSLATIONMODE = CACSL2BOOGIETRANSLATOR + "/Translation\\ Mode\\:";
	public static final String CACSL_VALUE_BASE = "BASE";
	public static final String CACSL_VALUE_SVCOMP = "SV_COMP14";
	public static final String CACSL_LABEL_MEMORY_LEAK = CACSL2BOOGIETRANSLATOR
			+ "/Check\\ for\\ the\\ main\\ procedure\\ if\\ all\\ allocated\\ memory\\ was\\ freed";
	public static final String CACSL_LABEL_SIGNED_INTEGER_OVERFLOW =
			CACSL2BOOGIETRANSLATOR + "/Check\\ absence\\ of\\ signed\\ integer\\ overflows";

	public static final String RCFG_LABEL_BLOCKSIZE = RCFGBUILDER + "/Size\\ of\\ a\\ code\\ block";
	public static final String RCFG_VALUE_SINGLE = "SingleStatement";
	public static final String RCFG_VALUE_SEQ = "SequenceOfStatements";
	public static final String RCFG_VALUE_BLOCK = "LoopFreeBlock";

	public static final String TA_LABEL_HOARE = TRACE_ABSTRACTION
			+ "/Compute\\ Hoare\\ Annotation\\ of\\ negated\\ interpolant\\ automaton,\\ abstraction\\ and\\ CFG";

	public static final String BE_LABEL_STRATEGY = BLOCKENCODING + "/Strategy\\ for\\ the\\ edge\\ rating";
	public static final String BE_VALUE_LARGE_BLOCK = "LARGE_BLOCK";
	public static final String BE_VALUE_DISJUNCTIVE_RATING = "DISJUNCTIVE_RATING";

	/** Webinterface settings **/
	public static final String INTERFACE_LAYOUT_FONTSIZE_DEFAULT = "100";
	public static final String INTERFACE_LAYOUT_ORIENTATION_DEFAULT = "horizontal";
	public static final String INTERFACE_LAYOUT_TRANSITION_DEFAULT = "true";

}
