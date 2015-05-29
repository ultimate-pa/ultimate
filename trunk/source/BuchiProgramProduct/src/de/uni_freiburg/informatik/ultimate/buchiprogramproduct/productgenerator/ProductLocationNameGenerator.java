package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.productgenerator;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class ProductLocationNameGenerator {

	private static final String HELPER_STATE_PREFIX = "crhelper";
	private int mHelperUnifique;
	private final NestedWordAutomaton<CodeBlock, String> mNWA;
	
	protected ProductLocationNameGenerator(NestedWordAutomaton<CodeBlock, String> nwa) {
		assert nwa != null;
		
		mHelperUnifique = 0;
		mNWA = nwa;
	}
	
	protected String generateStateName(ProgramPoint loc) {
		return generateStateName(loc, null);
	}

	/**
	 * Central method to create the product state's names. 
	 * 
	 * @param rcfgName
	 *            Name of the state in the RCFG
	 * @param nwaName
	 *            Name of the state in the BA / NWA
	 * @return a String representing the name of this location in the product 
	 */
	protected String generateStateName(ProgramPoint loc, String nwaName) {
		return generateStateName(String.valueOf(loc.hashCode()) + "_" + loc.getLocationName(), nwaName);
	}

	private String generateStateName(String rcfgName, String nwaName) {
		assert nwaName == null || !nwaName.isEmpty();
		if (nwaName == null) {
			return "NP" + "__" + rcfgName;
		} else if (rcfgName.equals("ULTIMATE.startENTRY") && mNWA.isInitial(nwaName)) {
			return "ULTIMATE.start";
		} else {
			return rcfgName + "__" + nwaName;
		}
	}

	protected String generateHelperStateName(String location) {
		mHelperUnifique++;
		return HELPER_STATE_PREFIX + Integer.toString(mHelperUnifique) + "__" + location;
	}
	
	protected boolean isHelperState(ProgramPoint loc){
		if(loc == null){
			return false;
		}
		return loc.getLocationName().startsWith(HELPER_STATE_PREFIX);
	}
	
}
