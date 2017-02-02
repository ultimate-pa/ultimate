/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DSInvariantASTTransformer plug-in.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DSInvariantASTTransformer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DSInvariantASTTransformer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE DSInvariantASTTransformer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.dsitransformer.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.dsitransformer.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

/**
 * 
 * This class loads preference default values before they are needed
 * 
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the
 * plugin.xml
 * 
 * @author Dietsch
 * 
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {
	/*
	 * labels for the different preferences
	 */

	public static final String LABEL_STRUCTURETYPE = "Structure Type";
	public static final String LABEL_PROCEDUREID = "New Procedure Identifier";
	public static final String LABEL_TRIMWRAP = "Trim after \"$wrap\"?";
	public static final String LABEL_ALLFUNCTIONS = "All methods (ignores all other options)";
	public static final String LABEL_LEAVEPROCEDURES = "Don't remove original procedure declarations?";

	/*
	 * default values for the different preferences
	 */

	public static final Boolean VALUE_TRIMWRAP_DEFAULT = Boolean.TRUE;
	public static final Boolean VALUE_ALLFUNCTIONS_DEFAULT = Boolean.FALSE;
	public static final Boolean VALUE_LEAVEPROCEDURES = Boolean.FALSE;

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, "DS Invariant AST Transformer");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<String>(LABEL_PROCEDUREID, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_ALLFUNCTIONS,
						VALUE_ALLFUNCTIONS_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_STRUCTURETYPE, "",
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_TRIMWRAP,
						VALUE_TRIMWRAP_DEFAULT, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_LEAVEPROCEDURES,
						VALUE_LEAVEPROCEDURES, PreferenceType.Boolean), };
	}
}
