/*
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * This class provides for each problem found, a string to represent in 
 * the ProblemsDetailsView.
 * This view is unfortunately very limited, because it holds only a 
 * Link-Widget. Maybe we need to extend Codan here.
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

import org.eclipse.cdt.codan.ui.AbstractCodanProblemDetailsProvider;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 31.01.2012
 */
public class UltimateCCheckerHelp extends AbstractCodanProblemDetailsProvider {

	@Override
	public boolean isApplicable(String id) {
		if (CCheckerDescriptor.CE_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.IN_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.UN_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.POS_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.SYNERR_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.TIMEOUT_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.GENERIC_INFO_RESULT_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.GENERIC_WARNING_RESULT_ID.equals(id)) {
			return true;
		} else if (CCheckerDescriptor.GENERIC_ERROR_RESULT_ID.equals(id)) {
			return true;
		}
		return false;
	}

	@Override
	public String getStyledProblemDescription() {
		/*
		 * This method provides Information which is displayed in the
		 * ProblemDetailsView (Codan), further step would be to present a new
		 * view or a new approach how to visualize Ultimate-Results.
		 */
		final StringBuffer sb = new StringBuffer();
		sb.append("<a>SHORT DESCRIPTION:</a>");
		sb.append(System.getProperty("line.separator"));
		sb.append(getProblemArgument(0));
		sb.append(System.getProperty("line.separator"));
		sb.append("<a>LONG DESCRITPTION:</a>");
		sb.append(System.getProperty("line.separator"));
		sb.append("No Long Description anymore because of the"); 
		sb.append("Problem Details View cannot handle large strings!");
		sb.append(System.getProperty("line.separator"));
		sb.append("Please use instead the Ultimate Result Details View!");
		return sb.toString();
	}
}
