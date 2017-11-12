/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTParser plug-in.
 *
 * The ULTIMATE CDTParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

/**
 * @author Yannick Bühler
 * @date 12.11.2017
 */
public class DecoratedUnit {
	/**
	 * The root node of this unit
	 */
	private final DecoratorNode mRootNode;
	/**
	 * The {@link IASTTranslationUnit} that was the source of the CDT AST of this unit
	 */
	private final IASTTranslationUnit mSourceTU;
	
	public DecoratedUnit(final DecoratorNode rootNode, final IASTTranslationUnit sourceTU) {
		mRootNode = rootNode;
		mSourceTU = sourceTU;
	}
	
	/**
	 * Getter for the root node
	 * 
	 * @return the root node
	 */
	public DecoratorNode getRootNode() {
		return mRootNode;
	}
	
	/**
	 * Getter for the source translation unit
	 * 
	 * @return the translation unit that was the source of the CDT AST
	 */
	public IASTTranslationUnit getSourceTranslationUnit() {
		return mSourceTU;
	}
}
