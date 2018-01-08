package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
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

	public static final boolean DEF_USE_WEQ_IN_PROJECT = false;

	public static List<BaseUltimatePreferenceItem> getPreferences() {
		final List<BaseUltimatePreferenceItem> returnList = new ArrayList<>();

		final UltimatePreferenceItemContainer container =
				new UltimatePreferenceItemContainer("VP Domain (map equality domain)");

		container.addItem(new UltimatePreferenceItem<>(LABEL_USE_WEQ_IN_PROJECT, DEF_USE_WEQ_IN_PROJECT,
				PreferenceType.Boolean));

		returnList.add(container);
		return returnList;
	}
}
