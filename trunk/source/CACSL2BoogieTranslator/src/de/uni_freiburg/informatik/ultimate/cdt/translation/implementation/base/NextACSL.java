/*
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
 * Container for a list of ACSL nodes and one C node.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 */
public class NextACSL {
	/**
	 * a list of ACSL comments to hold.
	 */
	private final List<ACSLNode> mAcsl;
	/**
	 * The successor C node as reference, where the ACSL is contained in the
	 * translation unit.
	 */
	private final IASTNode mSuccessorCNode;

	/**
	 * Constructor.
	 * 
	 * @param acsl
	 *            a list of ACSL comments to hold.
	 * @param successorCNode
	 *            the successor C node as reference, where the ACSL is contained
	 *            in the translation unit.
	 */
	public NextACSL(final List<ACSLNode> acsl, final IASTNode successorCNode) {
		assert acsl != null;
		mAcsl = acsl;
		mSuccessorCNode = successorCNode;
	}

	public List<ACSLNode> getAcsl() {
		return mAcsl;
	}

	public IASTNode getSuccessorCNode() {
		return mSuccessorCNode;
	}
}
