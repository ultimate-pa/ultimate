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

	public static final String s_syntaxchecker = "de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker";
	public static final String s_cacsl2boogietranslator =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator";
	public static final String s_boogiePreprocessor = "de.uni_freiburg.informatik.ultimate.boogie.preprocessor";
	public static final String s_rcfgBuilder = "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder";
	public static final String s_buchiautomizer =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer";
	public static final String s_automatascriptinterpreter =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter";
	public static final String s_blockencoding = "de.uni_freiburg.informatik.ultimate.plugins.blockencoding";
	public static final String s_traceAbstractionConcurrent =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent";
	public static final String s_lassoRanker = "de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker";
	public static final String s_traceAbstraction =
			"de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction";
	public static final String s_ltl2aut = "de.uni_freiburg.informatik.ultimate.ltl2aut";
	public static final String s_buchiProgramProduct = "de.uni_freiburg.informatik.ultimate.buchiprogramproduct";
	public static final String s_codecheck = "de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck";

	/** Settings strings **/

	public static final String s_CACSL_LABEL_StartFunction =
			s_cacsl2boogietranslator + "/Checked\\ method.\\ Library\\ mode\\ if\\ empty.";
	public static final String s_CACSL_LABEL_TranslationMode = s_cacsl2boogietranslator + "/Translation\\ Mode\\:";
	public static final String s_CACSL_VALUE_Base = "BASE";
	public static final String s_CACSL_VALUE_Svcomp = "SV_COMP14";
	public static final String s_CACSL_LABEL_MemoryLeak = s_cacsl2boogietranslator
			+ "/Check\\ for\\ the\\ main\\ procedure\\ if\\ all\\ allocated\\ memory\\ was\\ freed";
	public static final String s_CACSL_LABEL_SignedIntegerOverflow =
			s_cacsl2boogietranslator + "/Check\\ absence\\ of\\ signed\\ integer\\ overflows";

	public static final String s_RCFG_LABEL_BlockSize = s_rcfgBuilder + "/Size\\ of\\ a\\ code\\ block";
	public static final String s_RCFG_VALUE_Single = "SingleStatement";
	public static final String s_RCFG_VALUE_Seq = "SequenceOfStatements";
	public static final String s_RCFG_VALUE_Block = "LoopFreeBlock";

	public static final String s_TA_LABEL_Hoare = s_traceAbstraction
			+ "/Compute\\ Hoare\\ Annotation\\ of\\ negated\\ interpolant\\ automaton,\\ abstraction\\ and\\ CFG";

	public static final String s_BE_LABEL_STRATEGY = s_blockencoding + "/Strategy\\ for\\ the\\ edge\\ rating";
	public static final String s_BE_VALUE_LargeBlock = "LARGE_BLOCK";
	public static final String s_BE_VALUE_DisjunctiveRating = "DISJUNCTIVE_RATING";

	/** Webinterface settings **/
	public static final String s_InterfaceLayoutFontsizeDefault = "100";
	public static final String s_InterfaceLayoutOrientationDefault = "horizontal";
	public static final String s_InterfaceLayoutTransitionDefault = "true";

}
