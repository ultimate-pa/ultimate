/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
 * Parser example extended with a CDT-AST decorator to support ACSL-ASTs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.decorator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 04.01.2012
 */
public class ASTDecorator {
	/**
	 * All ACSL ASTs in the file, specified with there root node.
	 */
	private List<ACSLNode> mAcslASTs;
	/**
	 * The root node of the decorator.
	 */
	private DecoratorNode mRootNode;
	/**
	 * Helper variable, required for mapASTs().
	 */
	private int mCurrentStartLineNr;

	/**
	 * Entry point to recursive method to generate the mapping between CDT AST
	 * and ACSL ASTs. A translation unit without any C code will return null!
	 * Pure ACSL code is skipped therefore!
	 * 
	 * @param node
	 *            the start node
	 */
	public void mapASTs(IASTNode node) {
		if(!(node instanceof IASTTranslationUnit)) {
			throw new IllegalArgumentException("First node of C-AST must be TU!");
		}
		mCurrentStartLineNr = 1;
		final DecoratorNode result = mapASTs(node, null).get(0);
		assert mAcslASTs.isEmpty();
		setRootNode(result);
	}

	/**
	 * Recursive method to generate the mapping between CDT AST and ACSL ASTs.
	 * 
	 * @param node
	 *            the current node
	 * @param parent
	 *            the current parent (null for root node)
	 * @return the children list or null
	 */
	private List<DecoratorNode> mapASTs(IASTNode node, DecoratorNode parent) {
		if (node.getFileLocation() == null) {
			return null;
		}

		// there is acsl between the previous node and this one.
		final List<DecoratorNode> list = new ArrayList<DecoratorNode>();
		if (parent != null && containsAcsl(mCurrentStartLineNr, node.getFileLocation()
				.getStartingLineNumber())) {
			list.addAll(getAllTheAcsl(parent, mCurrentStartLineNr, node
					.getFileLocation().getStartingLineNumber()));
		}

		if (!containsAcsl(node)) {
			mCurrentStartLineNr = node.getFileLocation().getEndingLineNumber() + 1;
			list.add(new DecoratorNode(parent, node));
			return list;
		}
		// there is ACSL ... take care for all the children
		final DecoratorNode result = new DecoratorNode(parent, node);
		list.add(result);
		for (int i = 0; i < node.getChildren().length; i++) {
			if (i == 0) {
				mCurrentStartLineNr = node.getFileLocation()
						.getStartingLineNumber();
			}
			final List<DecoratorNode> newChildren = mapASTs(node.getChildren()[i],
					result);
			for (int j = 0; j < newChildren.size(); j++) {
				if (newChildren.get(j) != null) {
					result.addChildren(newChildren.get(j));
				}
			}
		}
		if (containsAcsl(mCurrentStartLineNr, node.getFileLocation()
				.getEndingLineNumber() + 1)) {
			// there is acsl between last children and node end ...
			result.addAllChildren(getAllTheAcsl(result, mCurrentStartLineNr,
					node.getFileLocation().getEndingLineNumber()));
		}
		mCurrentStartLineNr = node.getFileLocation().getEndingLineNumber();
		return list;
	}

	/**
	 * This method returns all ACSL comments between start and end.
	 * 
	 * @param parent
	 *            the parent decorator node
	 * @param start
	 *            the start line number (inclusive)
	 * @param end
	 *            the end line number (inclusive)
	 * @return the acsl ast node
	 */
	private List<DecoratorNode> getAllTheAcsl(DecoratorNode parent, int start,
			int end) {
		final List<DecoratorNode> list = new ArrayList<DecoratorNode>();
		for (int i = 0; i < mAcslASTs.size(); i++) {
			if (mAcslASTs.get(i).getEndingLineNumber() <= end
					&& mAcslASTs.get(i).getStartingLineNumber() >= start) {
				list.add(new DecoratorNode(parent, mAcslASTs.remove(i--)));
			}
		}
		return list;
	}

	/**
	 * Determines whether the given node contains ACSL statements or not.
	 * 
	 * @param node
	 *            the node to check
	 * @return true iff the given node contains ACSL statements.
	 */
	private boolean containsAcsl(IASTNode node) {
		if (node.getFileLocation() == null) {
			return false;
		}
		final int start = node.getFileLocation().getStartingLineNumber();
		final int end = node.getFileLocation().getEndingLineNumber();
		return containsAcsl(start, end);
	}

	/**
	 * Determines whether the given line numbers contain ACSL statements.
	 * 
	 * @param start
	 *            the start of the block (incl)
	 * @param end
	 *            the end of the block (incl)
	 * @return true iff the given line numbers contain ACSL statements.
	 */
	private boolean containsAcsl(int start, int end) {
		for (final ACSLNode acsl : mAcslASTs) {
			if (start <= acsl.getStartingLineNumber()
					&& end >= acsl.getEndingLineNumber()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Getter for root node.
	 * 
	 * @return the rootNode
	 */
	public DecoratorNode getRootNode() {
		return mRootNode;
	}

	/**
	 * Setter for root node.
	 * 
	 * @param node
	 *            the root node
	 */
	private void setRootNode(DecoratorNode node) {
		mRootNode = node;
	}

	/**
	 * Setter for the ACSL AST list.
	 * 
	 * @param acslASTs
	 *            the acslASTs to set
	 */
	public void setAcslASTs(List<ACSLNode> acslASTs) {
		mAcslASTs = acslASTs;
	}
}
