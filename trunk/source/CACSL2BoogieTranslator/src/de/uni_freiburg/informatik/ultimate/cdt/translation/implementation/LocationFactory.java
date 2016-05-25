/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Location in a C+ACSL program.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

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

	public static CACSLLocation createIgnoreCLocation() {
		return new CLocation(null, new Check(Check.Spec.UNKNOWN), true);
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
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), realLoc.getCheck(), realLoc.ignoreDuringBacktranslation());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	public static CACSLLocation createLocation(CACSLLocation loc, Check type) {
		if (loc instanceof ACSLLocation) {
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation());
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), type, realLoc.ignoreDuringBacktranslation());
		} else {
			throw new UnsupportedOperationException();
		}
	}
	
	public static CACSLLocation createIgnoreLocation(ILocation loc) {
		if (loc instanceof ACSLLocation) {
			final ACSLLocation realLoc = (ACSLLocation) loc;
			return new ACSLLocation(realLoc.getNode(), realLoc.getCheck(), true);
		} else if (loc instanceof CLocation) {
			final CLocation realLoc = (CLocation) loc;
			return new CLocation(realLoc.getNode(), realLoc.getCheck(), true);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
