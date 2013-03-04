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
		StringBuffer sb = new StringBuffer();
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
