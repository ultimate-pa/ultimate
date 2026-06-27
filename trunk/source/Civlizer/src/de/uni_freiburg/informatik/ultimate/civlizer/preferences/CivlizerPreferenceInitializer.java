/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer.preferences;

import de.uni_freiburg.informatik.ultimate.civlizer.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.util.FilePrinterUtils;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;

public class CivlizerPreferenceInitializer extends UltimatePreferenceInitializer {
	public static final String LABEL_RUN_CIVL_ON_OUTPUT = "Run Civl on output file";
	private static final boolean DEF_RUN_CIVL_ON_OUTPUT = false;

	public static final String LABEL_CIVL_WORKING_DIRECTORY = "Working directory for Civl";
	private static final String DEF_CIVL_WORKING_DIRECTORY = "";

	public static final String LABEL_CIVL_COMMAND = "Command to run Civl";
	private static final String DEF_CIVL_COMMAND = "Source/BoogieDriver/bin/Debug/net8.0/BoogieDriver";

	public CivlizerPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new BaseUltimatePreferenceItem[] {
				// Printer settings
				new UltimatePreferenceItemGroup("Printer settings",
						FilePrinterUtils.getPrinterPreferences("civlizer.civl.bpl")),

				// Civl runner settings
				new UltimatePreferenceItemGroup("Civl runner settings",
						new UltimatePreferenceItem<>(LABEL_RUN_CIVL_ON_OUTPUT, DEF_RUN_CIVL_ON_OUTPUT,
								PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_CIVL_WORKING_DIRECTORY, DEF_CIVL_WORKING_DIRECTORY,
								PreferenceType.Directory),
						new UltimatePreferenceItem<>(LABEL_CIVL_COMMAND, DEF_CIVL_COMMAND, PreferenceType.String)),

		};
	}
}
