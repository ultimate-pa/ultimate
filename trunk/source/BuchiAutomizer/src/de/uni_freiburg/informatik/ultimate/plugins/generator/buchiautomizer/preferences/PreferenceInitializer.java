package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.Activator;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<Boolean>(LABEL_IgnoreDownStates,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_DeterminizationOnDemand,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<BInterpolantAutomaton>(
						LABEL_BuchiInterpolantAutomaton,
						BInterpolantAutomaton.ScroogeNondeterminism, PreferenceType.Combo,
						BInterpolantAutomaton.values()),
				new UltimatePreferenceItem<Boolean>(LABEL_BouncerStem,
						true, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_BouncerLoop,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_CannibalizeLoop,
						false, PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(LABEL_LoopUnwindings, 2,
						PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(
								0, 1000000))
		};
	}

	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return "Buchi Automizer (Termination Analysis)";
	}
	
	public static final String LABEL_IgnoreDownStates = "Ignore down states";
	public static final String LABEL_DeterminizationOnDemand = "Determinization on demand";
	public static final String LABEL_BuchiInterpolantAutomaton = "Buchi interpolant automaton";
	public static final String LABEL_BouncerStem = "Bouncer stem";
	public static final String LABEL_BouncerLoop = "Bouncer loop";
	public static final String LABEL_CannibalizeLoop = "Cannibalize loop";
	public static final String LABEL_LoopUnwindings = "Max number of loop unwindings";
	
	public enum BInterpolantAutomaton { LassoAutomaton, EagerNondeterminism, ScroogeNondeterminism, Deterministic };
	
}