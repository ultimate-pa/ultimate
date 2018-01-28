/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SyntaxChecker plug-in.
 *
 * The ULTIMATE SyntaxChecker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SyntaxChecker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SyntaxChecker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SyntaxChecker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SyntaxChecker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.syntaxchecker;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_SyntaxErrorCommand, DEF_SyntaxErrorCommand, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_DoSyntaxWarningCheck, DEF_DoSyntaxWarningCheck,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SyntaxWarningCommand, DEF_SyntaxWarningCommand,
						PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_RemoveFilename, DEF_RemoveFilename, PreferenceType.Boolean),

		};
	}

	public static final String LABEL_SyntaxErrorCommand = "Command for syntax error check";
	private static final String DEF_SyntaxErrorCommand = "gcc -std=c11 -pedantic -w -fsyntax-only";

	public static final String LABEL_DoSyntaxWarningCheck = "Do additional syntax warning check";
	private static final boolean DEF_DoSyntaxWarningCheck = true;

	public static final String LABEL_SyntaxWarningCommand = "Command for syntax warning check";
	private static final String DEF_SyntaxWarningCommand = "gcc -std=c11 -pedantic -Wsequence-point -fsyntax-only";

	public static final String LABEL_RemoveFilename = "remove filename from checker output";
	private static final boolean DEF_RemoveFilename = true;

}
