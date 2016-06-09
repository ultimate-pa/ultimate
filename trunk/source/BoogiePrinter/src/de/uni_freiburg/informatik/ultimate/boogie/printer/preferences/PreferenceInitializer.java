/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePrinter plug-in.
 * 
 * The ULTIMATE BoogiePrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.printer.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String SAVE_IN_SOURCE_DIRECTORY_LABEL = "Save file in source directory?";
	private static final boolean SAVE_IN_SOURCE_DIRECTORY_DEFAULT = false;

	public static final String UNIQUE_NAME_LABEL = "Use automatic naming?";
	private static final boolean UNIQUE_NAME_DEFAULT = false;

	public static final String DUMP_PATH_LABEL = "Dump path:";
	private static final String DUMP_PATH_DEFAULT = System
			.getProperty("java.io.tmpdir");

	public static final String FILE_NAME_LABEL = "File name:";
	private static final String FILE_NAME_DEFAULT = "boogiePrinter.bpl";

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		// TODO Auto-generated method stub
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(DUMP_PATH_LABEL,
						DUMP_PATH_DEFAULT, PreferenceType.Directory),
				new UltimatePreferenceItem<String>(FILE_NAME_LABEL,
						FILE_NAME_DEFAULT, PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(
						SAVE_IN_SOURCE_DIRECTORY_LABEL,
						SAVE_IN_SOURCE_DIRECTORY_DEFAULT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						UNIQUE_NAME_LABEL,
						UNIQUE_NAME_DEFAULT,
						PreferenceType.Boolean),

		};
	}
}
