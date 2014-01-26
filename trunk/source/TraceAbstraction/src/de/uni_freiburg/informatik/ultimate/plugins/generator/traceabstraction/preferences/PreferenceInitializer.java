package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Determinization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomaton;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_INTERPROCEDUTAL,
						DEF_INTERPROCEDUTAL, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_AllErrorsAtOnce,
						DEF_AllErrorsAtOnce, PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(LABEL_TIMEOUT, DEF_TIMEOUT,
						PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 1000000)),
				new UltimatePreferenceItem<Integer>(LABEL_ITERATIONS,
						DEF_ITERATIONS, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 1000000)),
				new UltimatePreferenceItem<Artifact>(LABEL_ARTIFACT,
						Artifact.RCFG, PreferenceType.Combo, Artifact.values()),
				new UltimatePreferenceItem<Integer>(LABEL_WATCHITERATION,
						DEF_WATCHITERATION, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 10000000)),
				new UltimatePreferenceItem<Boolean>(LABEL_HOARE, DEF_HOARE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<INTERPOLATION>(
						LABEL_INTERPOLATED_LOCS, DEF_INTERPOLANTS,
						PreferenceType.Combo, INTERPOLATION.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_EDGES2TRUE,
						DEF_EDGES2TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<InterpolantAutomaton>(
						LABEL_InterpolantAutomaton,
						InterpolantAutomaton.CANONICAL, PreferenceType.Combo,
						InterpolantAutomaton.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_DUMPAUTOMATA,
						DEF_DUMPAUTOMATA, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_DUMPPATH,
						DEF_DUMPPATH, PreferenceType.Directory),
				new UltimatePreferenceItem<Determinization>(
						LABEL_DETERMINIZATION, Determinization.STRONGESTPOST,
						PreferenceType.Combo, Determinization.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_DIFFERENCE_SENWA,
						DEF_DIFFERENCE_SENWA, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_MINIMIZE,
						DEF_MINIMIZE, PreferenceType.Boolean),
				new UltimatePreferenceItem<Concurrency>(LABEL_CONCURRENCY,
						Concurrency.PETRI_NET, PreferenceType.Combo,
						Concurrency.values()),
				new UltimatePreferenceItem<String>(LABEL_Order, DEF_Order,
						PreferenceType.Combo, new String[] { VALUE_KMM,
								VALUE_EVR, VALUE_EVRMark }),
				new UltimatePreferenceItem<Boolean>(LABEL_cutOff, DEF_cutOff,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_unfolding2Net,
						DEF_unfolding2Net, PreferenceType.Boolean),

		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Automizer (Trace Abstraction)";
	}
	
	
	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_INTERPROCEDUTAL = "Interprocedural analysis (Nested Interpolants)";
	public static final String LABEL_AllErrorsAtOnce = "Check all specifiacations at once";
	public static final String LABEL_TIMEOUT = "Timeout in seconds";
	public static final String LABEL_ITERATIONS = "Iterations until the model checker surrenders";
	public static final String LABEL_ARTIFACT = "Kind of artifact that is visualized";
	public static final String LABEL_WATCHITERATION = "Number of iteration whose artifact is visualized";
	public static final String LABEL_HOARE = "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG";
	public static final String LABEL_INTERPOLATED_LOCS = "Compute Interpolants along a Counterexample";
	public static final String LABEL_EDGES2TRUE = "Add backedges from every state to initial state";
	public static final String LABEL_InterpolantAutomaton = "Interpolant automaton";
	public static final String LABEL_DUMPAUTOMATA = "Dump automata to files";
	public static final String LABEL_DUMPPATH = "Dump formulas of problems in the following path";
	public static final String LABEL_DETERMINIZATION = "Determinization algorithm";
	public static final String LABEL_DIFFERENCE_SENWA = "DifferenceSenwa operation instead classical Difference";
	public static final String LABEL_MINIMIZE = "Minimize abstraction";
	public static final String LABEL_CONCURRENCY = "Automaton type used in concurrency analysis";
	public static final String LABEL_Order = "Order in Petri net unfolding";
	public static final String LABEL_cutOff = "cut-off requires same transition";
	public static final String LABEL_unfolding2Net = "use unfolding as abstraction";

	public static final String VALUE_ABSTRACTION = "Abstraction";
	public static final String VALUE_RCFG = "RecursiveControlFlowGraph";
	public static final String VALUE_INTERPOLANT_AUTOMATON = "InterpolantAutomaton";
	public static final String VALUE_NEG_INTERPOLANT_AUTOMATON = "NegatedInterpolantAutomaton";
	public static final String VALUE_ITP_WP = "StrongestPostcondition&WeakestPrecondition";
	public static final String VALUE_ITP_GUESS = "Guess Interpolants";
	public static final String VALUE_InterpolantAutomaton_SingleTrace = "SingleTrace";
	public static final String VALUE_InterpolantAutomaton_TwoTrack = "TwoTrack";
	public static final String VALUE_InterpolantAutomaton_Canonical = "With backedges to repeated locations (Canonial)";
	public static final String VALUE_InterpolantAutomaton_TotalInterpolation = "Total interpolation (Jan)";

	public static final String VALUE_FINITE_AUTOMATON = "Finite Automata";
	public static final String VALUE_PETRI_NET = "Petri Net";
	public static final String VALUE_KMM = "Ken McMillan";
	public static final String VALUE_EVR = "Esparza Römer Vogler";
	public static final String VALUE_EVRMark = "ERV with equal markings";

	/*
	 * default values for the different preferences
	 */
	public static final boolean DEF_INTERPROCEDUTAL = true;
	public static final int DEF_ITERATIONS = 10000;
	public static final int DEF_TIMEOUT = 0;
	public static final String DEF_ARTIFACT = VALUE_RCFG;
	public static final int DEF_WATCHITERATION = 1000;
	public static final boolean DEF_HOARE = false;
	public static final INTERPOLATION DEF_INTERPOLANTS = INTERPOLATION.ForwardPredicates;
	public static final boolean DEF_EDGES2TRUE = false;
	public static final String DEF_ADDITIONAL_EDGES = VALUE_InterpolantAutomaton_Canonical;
	public static final boolean DEF_DUMPAUTOMATA = false;
	public static final String DEF_DUMPPATH = ".";
	public static final boolean DEF_DIFFERENCE_SENWA = false;
	public static final boolean DEF_MINIMIZE = true;
	public static final String DEF_CONCURRENCY = VALUE_FINITE_AUTOMATON;
	public static final boolean DEF_AllErrorsAtOnce = true;

	public static final boolean DEF_cutOff = true;
	public static final boolean DEF_unfolding2Net = false;
	public static final String DEF_Order = VALUE_EVR;
	public static final boolean DEF_simplifyCodeBlocks = false;
	public static final boolean DEF_PreserveGotoEdges = false;

	public enum INTERPOLATION {
		Craig_NestedInterpolation, Craig_TreeInterpolation, ForwardPredicates, BackwardPredicates, FPandBP
	}
	

}