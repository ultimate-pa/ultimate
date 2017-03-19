/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;

/**
 * Objects of this class are used to report the overall result of a termination
 * analysis. Do not use this for synthesis of termination arguments.
 * (I do not know if Severity.ERROR is a good choice for NONTERMINATION and
 * UNKNOWN.)
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TerminationAnalysisResult extends AbstractResult implements
		IResultWithSeverity {
	
	private final Termination mTermination;
	private final String mLongDescription;
	
	public TerminationAnalysisResult(String plugin, Termination termination,
			String longDescription) {
		super(plugin);
		mTermination = termination;
		mLongDescription = longDescription;
	}
	

	public Termination getTermination() {
		return mTermination;
	}

	public enum Termination {
		TERMINATING,
		NONTERMINATING,
		UNKNOWN
	}

	@Override
	public String getShortDescription() {
		final String shortDescription;
		switch (mTermination) {
		case NONTERMINATING:
			shortDescription = "Nontermination possible";
			break;
		case TERMINATING:
			shortDescription = "Termination proven";
			break;
		case UNKNOWN:
			shortDescription = "Unable to decide termination";
			break;
		default:
			throw new AssertionError();
		}
		return shortDescription;
	}

	@Override
	public String getLongDescription() {
		return mLongDescription;
	}

	@Override
	public Severity getSeverity() {
		Severity severity;
		switch (mTermination) {
		case NONTERMINATING:
			severity = Severity.ERROR;
			break;
		case TERMINATING:
			severity = Severity.INFO;
			break;
		case UNKNOWN:
			severity = Severity.ERROR;
			break;
		default:
			throw new AssertionError();
		}
		return severity;
	}

}
