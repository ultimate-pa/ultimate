package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences;

import org.eclipse.jface.resource.StringConverter;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool.QueryKeyword;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues.EdgeLabels;

/**
 * 
 * @author dietsch
 * 
 */
public class JungPreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_PATH,
						JungPreferenceValues.VALUE_PATH_DEFAULT, PreferenceType.Directory),
				new UltimatePreferenceItem<EdgeLabels>(JungPreferenceValues.LABEL_ANNOTATED_EDGES,
						JungPreferenceValues.VALUE_ANNOTATED_EDGES_DEFAULT, PreferenceType.Combo, EdgeLabels.values()),
				new UltimatePreferenceItem<Boolean>(JungPreferenceValues.LABEL_ANNOTATED_NODES,
						JungPreferenceValues.VALUE_ANNOTATED_NODES_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_LAYOUT,
						JungPreferenceValues.VALUE_LAYOUT_DEFAULT, PreferenceType.Combo, new String[] { "FRLayout",
								"FRLayout2", "ISOMLayout", "KKLayout", "TreeLayout" }),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_BACKGROUND,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_BACKGROUND_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_NODE,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_NODE_DEFAULT), PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_COLOR_NODE_PICKED,
						StringConverter.asString(JungPreferenceValues.VALUE_COLOR_NODE_PICKED_DEFAULT),
						PreferenceType.Color),
				new UltimatePreferenceItem<String>(JungPreferenceValues.LABEL_SHAPE_NODE,
						JungPreferenceValues.VALUE_SHAPE_NODE_DEFAULT, PreferenceType.Combo, new String[] {
								"RoundRectangle", "Rectangle", "Ellipse" }),
				new UltimatePreferenceItem<QueryKeyword>(JungPreferenceValues.LABEL_WHICH_MODEL, QueryKeyword.LAST,
						PreferenceType.Combo, QueryKeyword.values()) 
						};
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}

}
