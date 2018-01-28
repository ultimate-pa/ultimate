package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VPDomainPreferences {

	public static final String LABEL_USE_WEQ_IN_PROJECT = "Weq Fattening";
	public static final String LABEL_FLATTEN_BEFORE_FATTEN = "Flatten before fatten";
	public static final String LABEL_DEACTIVATE_WEAK_EQUIVALENCES = "Deactivate Weak Equivalences";
	public static final String LABEL_PRECISE_COMPARISON_OPERATOR = "Precise comparison operator";

	public static final boolean DEF_USE_WEQ_IN_PROJECT = false;
	public static final boolean DEF_DEACTIVATE_WEAK_EQUIVALENCES = false;
	public static final boolean DEF_FLATTEN_BEFORE_FATTEN = false;
	public static final boolean DEF_PRECISE_COMPARISON_OPERATOR = false;

	private static final String DESC_USE_WEQ_IN_PROJECT = "Fatten using full WeqCc ground truth before projectAway, "
			+ "if false only the ground Cc is used for fattening there. (more precise but costly, only makes a "
			+ "difference if weak equivalences are not deactivated)";
	private static final String DESC_DEACTIVATE_WEAK_EQUIVALENCES = "Don't use any weak equivalences, perform the "
			+ "analysis based on congruence closure only";
	public static final String DESC_FLATTEN_BEFORE_FATTEN = "Before doing a fattening weq fattening, of one weq edge, "
			+ " flatten all disjunctions on the weq graph to be fattened with. (only makes a difference when "
			+ " WeqFattening and weak equivalences are active";
	public static final String DESC_PRECISE_COMPARISON_OPERATOR = "Our comparison on (Weq)CongruenceClosure objects"
			+ " is imprecise, if this flag is set, we use the SMT solver instead, make precise comparisons";

	public static List<BaseUltimatePreferenceItem> getPreferences() {
		final UltimatePreferenceItemContainer container =
				new UltimatePreferenceItemContainer("VP Domain (map equality domain)");

		container.addItem(new UltimatePreferenceItem<>(LABEL_USE_WEQ_IN_PROJECT, DEF_USE_WEQ_IN_PROJECT,
				DESC_USE_WEQ_IN_PROJECT, PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_DEACTIVATE_WEAK_EQUIVALENCES,
				DEF_DEACTIVATE_WEAK_EQUIVALENCES, DESC_DEACTIVATE_WEAK_EQUIVALENCES, PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_FLATTEN_BEFORE_FATTEN,
				DEF_FLATTEN_BEFORE_FATTEN, DESC_FLATTEN_BEFORE_FATTEN, PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_PRECISE_COMPARISON_OPERATOR,
				DEF_PRECISE_COMPARISON_OPERATOR, DESC_PRECISE_COMPARISON_OPERATOR, PreferenceType.Boolean));

		return Collections.singletonList(container);
	}
}
