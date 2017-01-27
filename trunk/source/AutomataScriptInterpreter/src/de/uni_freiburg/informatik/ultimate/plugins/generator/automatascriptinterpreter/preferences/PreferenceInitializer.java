/*
 * Copyright (C) 2013-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter.Activator;

/**
 * Class used to initialize default preference values.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {
	public static final String NAME_WRITE_TO_FILE = "Write results of print operation to file";
	public static final boolean DEFAULT_WRITE_TO_FILE = false;
	
	public static final String NAME_PATH = "Directory";
	public static final String DEFAULT_PATH = ".";
	
	public static final String NAME_EXECUTE_COMMAND_FLAG = "Ignore all commands and only execute below command";
	public static final boolean DEFAULT_EXECUTE_COMMAND_FLAG = false;
	
	public static final String NAME_EXECUTE_COMMAND_STRING = "Command";
	public static final String DEFAULT_EXECUTE_COMMAND_STRING = "print($1);";
	
	/**
	 * Constructor.
	 */
	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}
	
	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				// write automaton to file
				new UltimatePreferenceItem<>(NAME_WRITE_TO_FILE, DEFAULT_WRITE_TO_FILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(NAME_PATH, DEFAULT_PATH, PreferenceType.Directory),
				
				// execute command
				new UltimatePreferenceItem<>(NAME_EXECUTE_COMMAND_FLAG, DEFAULT_EXECUTE_COMMAND_FLAG,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(NAME_EXECUTE_COMMAND_STRING, DEFAULT_EXECUTE_COMMAND_STRING,
						PreferenceType.String)
		};
	}
}
