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

	public static final String LABEL_USE_WEQ_IN_PROJECT = "Fatten using full WeqCc ground truth before projectAway, "
			+ "if false only the ground Cc is used for fattening there.";
	public static final String LABEL_DEACTIVATE_WEAK_EQUIVALENCES = "Don't use any weak equivalences, perform the "
			+ "analysis based on congruence closure only";

	public static final boolean DEF_USE_WEQ_IN_PROJECT = false;
	public static final boolean DEF_DEACTIVATE_WEAK_EQUIVALENCES = false;

	public static List<BaseUltimatePreferenceItem> getPreferences() {
//		final List<BaseUltimatePreferenceItem> returnList = new ArrayList<>();

		final UltimatePreferenceItemContainer container =
				new UltimatePreferenceItemContainer("VP Domain (map equality domain)");

		container.addItem(new UltimatePreferenceItem<>(LABEL_USE_WEQ_IN_PROJECT, DEF_USE_WEQ_IN_PROJECT,
				PreferenceType.Boolean));
		container.addItem(new UltimatePreferenceItem<>(LABEL_DEACTIVATE_WEAK_EQUIVALENCES,
				DEF_DEACTIVATE_WEAK_EQUIVALENCES, PreferenceType.Boolean));

//		returnList.add(container);
		return Collections.singletonList(container);
	}
}
