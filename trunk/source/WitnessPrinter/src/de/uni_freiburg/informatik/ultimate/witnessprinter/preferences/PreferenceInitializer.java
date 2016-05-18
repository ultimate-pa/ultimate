/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 * 
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter.preferences;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.witnessprinter.Activator;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PreferenceInitializer extends RcpPreferenceInitializer {

	public enum WitnessVerifierType {
		CPACHECKER
	}

	// Witness generation
	public static final String DESC_WITNESS = "Witness generation";
	public static final String LABEL_WITNESS_GEN = "Generate witness(es)";
	public static final boolean VALUE_WITNESS_GEN = false;
	public static final String LABEL_WITNESS_LOG = "Log witness to console";
	public static final boolean VALUE_WITNESS_LOG = false;
	public static final String LABEL_WITNESS_WRITE = "Write witness as \"<inputfilename>-witness.graphml\" "
			+ "in the same directory as the input file";
	public static final boolean VALUE_WITNESS_WRITE = false;
	public static final String LABEL_WITNESS_WRITE_WORKINGDIR = "Write witness as \"witness.graphml\" "
			+ "to working directory";
	public static final boolean VALUE_WITNESS_WRITE_WORKINGDIR = false;
	public static final String LABEL_WITNESS_VERIFY = "Verify the witness and generate results";
	public static final boolean VALUE_WITNESS_VERIFY = false;
	public static final String LABEL_WITNESS_VERIFIER = "Use the following witness verifier";
	public static final WitnessVerifierType VALUE_WITNESS_VERIFIER = WitnessVerifierType.CPACHECKER;
	public static final String LABEL_WITNESS_VERIFIER_COMMAND = "Command to execute witness verifier "
			+ "(gets witness file as first and input file as second parameter)\n"
			+ "For CPA Checker: Additionally, set CPACHECKER_HOME";
	public static final String VALUE_WITNESS_VERIFIER_COMMAND = "";
	public static final String LABEL_WITNESS_CPACHECKER_PROPERTY = "For CPAChecker: Use this .prp file (may be relative to CPACHECKER_HOME)";
	public static final String VALUE_WITNESS_CPACHECKER_PROPERTY = "";
	public static final String LABEL_WITNESS_VERIFIER_TIMEOUT = "Timeout in seconds for witness verifier";
	public static final int VALUE_WITNESS_VERIFIER_TIMEOUT = 10;
	public static final String LABEL_WITNESS_DELETE_GRAPHML = "Delete the .graphml file after verification";
	public static final boolean VALUE_WITNESS_DELETE_GRAPHML = false;

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				// Witness generation
				new UltimatePreferenceItem<String>(DESC_WITNESS, null, PreferenceType.Label),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_GEN, VALUE_WITNESS_GEN, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_LOG, VALUE_WITNESS_LOG, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_WRITE, VALUE_WITNESS_WRITE, PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_WRITE_WORKINGDIR, VALUE_WITNESS_WRITE_WORKINGDIR,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_VERIFY, VALUE_WITNESS_VERIFY, PreferenceType.Boolean,
						new WitnessVerifierValidator()),
				new UltimatePreferenceItem<WitnessVerifierType>(LABEL_WITNESS_VERIFIER, VALUE_WITNESS_VERIFIER,
						PreferenceType.Combo, WitnessVerifierType.values()),
				new UltimatePreferenceItem<String>(LABEL_WITNESS_VERIFIER_COMMAND, VALUE_WITNESS_VERIFIER_COMMAND,
						PreferenceType.String),
				new UltimatePreferenceItem<Integer>(LABEL_WITNESS_VERIFIER_TIMEOUT, VALUE_WITNESS_VERIFIER_TIMEOUT,
						PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(1, 1000000)),
				new UltimatePreferenceItem<String>(LABEL_WITNESS_CPACHECKER_PROPERTY, VALUE_WITNESS_CPACHECKER_PROPERTY,
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(LABEL_WITNESS_DELETE_GRAPHML, VALUE_WITNESS_DELETE_GRAPHML,
						PreferenceType.Boolean, new WitnessVerifierValidator()), };
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}

	private class WitnessVerifierValidator implements IUltimatePreferenceItemValidator<Boolean> {

		@Override
		public boolean isValid(Boolean value) {
			if (value) {
				RcpPreferenceProvider ups = new RcpPreferenceProvider(Activator.PLUGIN_ID);
				return ups.getBoolean(LABEL_WITNESS_GEN) && ups.getBoolean(LABEL_WITNESS_WRITE);
			} else {
				return true;
			}
		}

		@Override
		public String getInvalidValueErrorMessage(Boolean value) {
			return "You must enable generation and writing of witness results before you can verify them";
		}
	}
}
