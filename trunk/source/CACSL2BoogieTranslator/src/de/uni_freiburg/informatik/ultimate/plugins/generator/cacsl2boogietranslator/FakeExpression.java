/*
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import org.eclipse.cdt.core.dom.ast.ASTNodeProperty;
import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.ExpansionOverlapsBoundaryException;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNodeLocation;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.parser.IToken;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

/**
 * This evil class allows us to create identifier or value expressions for the purpose of backtranslation without having
 * to rebuild a complete CDT AST from scratch.
 *
 * It is more or less an evil hack into the structures of CDT, but there is no other, easy solution. In particular,
 * there is no shared superclass of {@link IASTExpression} and
 * {@link de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression}
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class FakeExpression implements IASTExpression {

	private final String mName;
	private final CType mCType;
	private final IASTNode mBackingNode;

	public FakeExpression(final String name) {
		mName = name;
		mBackingNode = null;
		mCType = null;
	}

	public FakeExpression(final IASTNode actualNode, final String name, final CType cType) {
		mBackingNode = actualNode;
		mName = name;
		mCType = cType;
	}

	@Override
	public IASTTranslationUnit getTranslationUnit() {
		if (mBackingNode != null) {
			return mBackingNode.getTranslationUnit();
		}
		return null;
	}

	@Override
	public IASTNodeLocation[] getNodeLocations() {
		if (mBackingNode != null) {
			return mBackingNode.getNodeLocations();
		}
		return null;
	}

	@Override
	public IASTFileLocation getFileLocation() {
		if (mBackingNode != null) {
			return mBackingNode.getFileLocation();
		}
		return null;
	}

	@Override
	public String getContainingFilename() {
		if (mBackingNode != null) {
			return mBackingNode.getContainingFilename();
		}
		return null;
	}

	@Override
	public boolean isPartOfTranslationUnitFile() {
		if (mBackingNode != null) {
			return mBackingNode.isPartOfTranslationUnitFile();
		}
		return false;
	}

	@Override
	public IASTNode getParent() {
		if (mBackingNode != null) {
			return mBackingNode.getParent();
		}
		return null;
	}

	@Override
	public IASTNode[] getChildren() {
		if (mBackingNode != null) {
			return mBackingNode.getChildren();
		}
		return null;
	}

	@Override
	public void setParent(final IASTNode node) {
		if (mBackingNode != null) {
			mBackingNode.setParent(node);
		}
	}

	@Override
	public ASTNodeProperty getPropertyInParent() {
		if (mBackingNode != null) {
			return mBackingNode.getPropertyInParent();
		}
		return null;
	}

	@Override
	public void setPropertyInParent(final ASTNodeProperty property) {
		if (mBackingNode != null) {
			mBackingNode.setPropertyInParent(property);
		}
	}

	@Override
	public boolean accept(final ASTVisitor visitor) {
		if (mBackingNode != null) {
			return mBackingNode.accept(visitor);
		}
		return false;
	}

	@Override
	public String getRawSignature() {
		return mName;
	}

	@Override
	public boolean contains(final IASTNode node) {
		if (mBackingNode != null) {
			return mBackingNode.contains(node);
		}
		return false;
	}

	@Override
	public IToken getLeadingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		if (mBackingNode != null) {
			return mBackingNode.getLeadingSyntax();
		}
		return null;
	}

	@Override
	public IToken getTrailingSyntax() throws ExpansionOverlapsBoundaryException, UnsupportedOperationException {
		if (mBackingNode != null) {
			return mBackingNode.getTrailingSyntax();
		}
		return null;
	}

	@Override
	public IToken getSyntax() throws ExpansionOverlapsBoundaryException {
		if (mBackingNode != null) {
			return mBackingNode.getSyntax();
		}
		return null;
	}

	@Override
	public boolean isFrozen() {
		if (mBackingNode != null) {
			return mBackingNode.isFrozen();
		}
		return true;
	}

	@Override
	public boolean isActive() {
		if (mBackingNode != null) {
			return mBackingNode.isActive();
		}
		return false;
	}

	@Override
	public IASTNode getOriginalNode() {
		if (mBackingNode != null) {
			return mBackingNode.getOriginalNode();
		}
		return null;
	}

	@Override
	public IType getExpressionType() {
		return null;
	}

	@Override
	public boolean isLValue() {
		return false;
	}

	@Override
	public ValueCategory getValueCategory() {
		return null;
	}

	@Override
	public IASTExpression copy() {
		return null;
	}

	@Override
	public IASTExpression copy(final CopyStyle style) {
		return null;
	}

	@Override
	public String toString() {
		return mName;
	}

	public CType getCType() {
		return mCType;
	}
}
