/*
 * Copyright (C) 2020 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PeaExampleGenerator plug-in.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PeaExampleGenerator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PeaExampleGenerator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PeaExampleGenerator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.Activator;

/**
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class PeaExampleGeneratorPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_PYTHON_SCRIPT = "Python script";
	public static final String LABEL_OUTPUT_FILE_EXTENSION = "Output file extension";
	public static final String LABEL_OUTPUT_DIRECTORY = "Output directory";

	private final static String[] OUTPUT_FILE_EXTENSIONS = { ".ps", ".eps", ".pdf", ".pgf", ".png", ".raw", ".rgba",
			".svg", ".svgz", ".jpg", ".jpeg", ".tif", ".tiff" };

	public PeaExampleGeneratorPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_PYTHON_SCRIPT, "", PreferenceType.File),
				new UltimatePreferenceItem<>(LABEL_OUTPUT_DIRECTORY, "", PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_OUTPUT_FILE_EXTENSION, ".svg", PreferenceType.Combo,
						OUTPUT_FILE_EXTENSIONS) };
	}
}
