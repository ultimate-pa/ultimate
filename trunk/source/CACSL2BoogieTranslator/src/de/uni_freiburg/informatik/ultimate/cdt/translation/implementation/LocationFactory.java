/**
 * Location in a C+ACSL program.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * @author dietsch@informatik.uni-freiburg.de
 */
public class LocationFactory {

	public static CACSLLocation createCLocation(IASTNode cNode) {
		return new CLocation(cNode, new Check(Check.Spec.UNKNOWN), false);
	}
	
	public static CACSLLocation createIgnoreCLocation(IASTNode cNode) {
		return new CLocation(cNode, new Check(Check.Spec.UNKNOWN), true);
	}

	public static CACSLLocation createACSLLocation(ACSLNode acslNode) {
		return new ACSLLocation(acslNode, new Check(Check.Spec.UNKNOWN), false);
	}

	public static CACSLLocation createACSLLocation(ACSLNode acslNode, Check type) {
		return new ACSLLocation(acslNode, type, false);
	}

	public static CACSLLocation createCLocation(IASTNode cNode, Check type) {
		return new CLocation(cNode, type, false);
	}

	public static CACSLLocation createLocation(CACSLLocation loc) {
		if (loc instanceof ACSLLocation) {
			ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public static CACSLLocation createLocation(CACSLLocation loc, Check type) {
		if (loc instanceof ACSLLocation) {
			ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation());
		} else {
			throw new UnsupportedOperationException();
		}
	}
}