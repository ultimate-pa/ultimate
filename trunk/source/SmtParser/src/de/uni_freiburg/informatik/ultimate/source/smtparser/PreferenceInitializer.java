/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SmtParser plug-in.
 * 
 * The ULTIMATE SmtParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SmtParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SmtParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.source.smtparser;

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
				new UltimatePreferenceItem<Boolean>(LABEL_UseExtSolver,
						DEF_UseExtSolver, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_ExtSolverCommand,
						DEF_ExtSolverCommand, PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_WriteToFile,
						DEF_WriteToFile, PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(LABEL_Filename,
						DEF_Filename, PreferenceType.String),
				new UltimatePreferenceItem<String>(LABEL_Directory,
						DEF_Directory, PreferenceType.Directory),
				new UltimatePreferenceItem<Boolean>(LABEL_HornSolverMode,
						DEF_HornSolverMode, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_FilterUnusedDeclarationsMode,
						DEF_FilterUnusedDeclarationsMode, PreferenceType.Boolean),
		};
	}
	
	public static final String LABEL_UseExtSolver = "Use external solver";
	public static final boolean DEF_UseExtSolver = true;
	
	public static final String LABEL_ExtSolverCommand = "Command for external solver";
	public static final String DEF_ExtSolverCommand = "z3 -smt2 -in";

	public static final String LABEL_WriteToFile = "Write SMT commands to file";
	public static final boolean DEF_WriteToFile = false;
	
	public static final String LABEL_Filename = "Filename";
	public static final String DEF_Filename = "UltimateSmtCommands.smt2";
	
	public static final String LABEL_Directory = "Directory";
	public static final String DEF_Directory = "";
	
	public static final String LABEL_HornSolverMode = "Use TreeAutomizer as solver for the given file (assumes the file contains Horn clauses only).";
	public static final boolean DEF_HornSolverMode = false;
	
	
	/**
	 * Special mode in which we only read the input file. 
	 * And write a similar file in which all declarations that never occurred
	 * in any term are removed.
	 */
	public static final String LABEL_FilterUnusedDeclarationsMode = "Remove only unused declarations from SMT file (experimental)";
	public static final boolean DEF_FilterUnusedDeclarationsMode = false;
}
