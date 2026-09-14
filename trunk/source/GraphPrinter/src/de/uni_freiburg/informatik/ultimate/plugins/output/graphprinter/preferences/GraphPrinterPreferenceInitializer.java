/*
 * Copyright (C) 2026 Manuel Bentele
 *
 * This file is part of the ULTIMATE GraphPrinter plug-in.
 *
 * The ULTIMATE GraphPrinter plug-in is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE GraphPrinter plug-in is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE GraphPrinter
 * plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE GraphPrinter plug-in, or any
 * covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE GraphPrinter plug-in grant you
 * additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.ITool.ModelQuery;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * Preference initializer for the GraphPrinter plug-in.
 *
 * @author Manuel Bentele
 */
public class GraphPrinterPreferenceInitializer extends UltimatePreferenceInitializer {

	public GraphPrinterPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(GraphPrinterPreferenceValues.LABEL_GRAPH_DIRECTORY,
						GraphPrinterPreferenceValues.DEF_GRAPH_DIRECTORY,
						GraphPrinterPreferenceValues.DESC_GRAPH_DIRECTORY, PreferenceType.Directory),
				new UltimatePreferenceItem<>(GraphPrinterPreferenceValues.LABEL_GRAPH_FILENAME,
						GraphPrinterPreferenceValues.DEF_GRAPH_FILENAME,
						GraphPrinterPreferenceValues.DESC_GRAPH_FILENAME, PreferenceType.String),
				new UltimatePreferenceItem<>(GraphPrinterPreferenceValues.LABEL_GRAPH_BESIDES_INPUT_FILE,
						GraphPrinterPreferenceValues.DEF_GRAPH_BESIDES_INPUT_FILE,
						GraphPrinterPreferenceValues.DESC_GRAPH_BESIDES_INPUT_FILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(GraphPrinterPreferenceValues.LABEL_GRAPH_MODEL,
						GraphPrinterPreferenceValues.DEF_GRAPH_MODEL, GraphPrinterPreferenceValues.DESC_GRAPH_MODEL,
						PreferenceType.Combo, ModelQuery.values()),
				new UltimatePreferenceItem<>(GraphPrinterPreferenceValues.LABEL_GRAPH_ANNOTATION_MODE,
						GraphPrinterPreferenceValues.DEF_GRAPH_ANNOTATION_MODE,
						GraphPrinterPreferenceValues.DESC_GRAPH_ANNOTATION_MODE, PreferenceType.Combo,
						AnnotationMode.values()) };
	}

}
